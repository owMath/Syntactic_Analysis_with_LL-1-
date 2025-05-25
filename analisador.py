"""
Phase 3 Project - Group 04
Lexical and Syntactic Analysis with LL(1) Parser and AST

Students: 
- Gabriel Martins Vicente
- Javier Agustin Aranibar González  
- Matheus Paul Lopuch
- Rafael Bonfim Zacco

Group 04

LL(1) Grammar Documentation:

GRAMMAR (RPN - Reverse Polish Notation):
S -> EXPR
EXPR -> ( OPERAND OPERAND OPERATOR )
     | ( if EXPR then EXPR else EXPR )
     | ( for INT EXPR )
     | ( INT RES )
     | ( NUM MEM )
     | ( MEM )
     | NUM

OPERAND -> EXPR | NUM | MEM
OPERATOR -> + | - | * | / | % | ^ | | | < | > | == | != | <= | >=
NUM -> INT | REAL

FIRST Sets:
FIRST(S) = { (, INT, REAL }
FIRST(EXPR) = { (, INT, REAL }
FIRST(OPERAND) = { (, INT, REAL, MEM }
FIRST(OPERATOR) = { +, -, *, /, %, ^, |, <, >, ==, !=, <=, >= }
FIRST(NUM) = { INT, REAL }

FOLLOW Sets:
FOLLOW(S) = { $ }
FOLLOW(EXPR) = { ), then, else, $ }
FOLLOW(OPERAND) = { (, INT, REAL, MEM, +, -, *, /, %, ^, |, <, >, ==, !=, <=, >= }
FOLLOW(OPERATOR) = { ) }
FOLLOW(NUM) = { ), MEM, RES, +, -, *, /, %, ^, |, <, >, ==, !=, <=, >= }

Parse Table LL(1):
M[S, (] = EXPR
M[S, INT] = EXPR
M[S, REAL] = EXPR
M[EXPR, (] = ( PARSE_PAREN_EXPR
M[EXPR, INT] = NUM
M[EXPR, REAL] = NUM
M[PARSE_PAREN_EXPR, if] = if EXPR then EXPR else EXPR )
M[PARSE_PAREN_EXPR, for] = for INT EXPR )
M[PARSE_PAREN_EXPR, INT] = CHECK_SECOND
M[PARSE_PAREN_EXPR, REAL] = CHECK_SECOND
M[PARSE_PAREN_EXPR, MEM] = CHECK_TYPE
M[PARSE_PAREN_EXPR, (] = OPERAND OPERAND OPERATOR )
M[CHECK_SECOND, RES] = INT RES )
M[CHECK_SECOND, MEM] = NUM MEM )
M[CHECK_SECOND, default] = OPERAND OPERAND OPERATOR )
M[CHECK_TYPE, )] = MEM )
M[CHECK_TYPE, default] = OPERAND OPERAND OPERATOR )
M[OPERAND, (] = EXPR
M[OPERAND, INT] = NUM
M[OPERAND, REAL] = NUM
M[OPERAND, MEM] = MEM
M[NUM, INT] = INT
M[NUM, REAL] = REAL
"""

import sys
import numpy as np
from collections import namedtuple, deque
import json
import platform
import struct

# Try importing Graphviz for AST visualization
try:
    from graphviz import Digraph
    import subprocess
    # Check if Graphviz is accessible
    try:
        subprocess.run(['dot', '-V'], capture_output=True, check=True)
        GRAPHVIZ_AVAILABLE = True
    except (subprocess.CalledProcessError, FileNotFoundError):
        GRAPHVIZ_AVAILABLE = False
except ImportError:
    GRAPHVIZ_AVAILABLE = False
    print("❌ Python's graphviz module not installed. Execute: pip install graphviz")

# Determine appropriate float precision based on architecture
def get_float_type():
    """Determine float precision based on processor architecture"""
    bits = struct.calcsize("P") * 8  # Pointer size in bits
    
    # For our purposes, we'll use standard numpy types
    # Note: numpy doesn't have float128 on all platforms
    if bits <= 16:
        return np.float16
    elif bits <= 32:
        return np.float32
    elif bits <= 64:
        return np.float64
    else:
        # Use longdouble for 128-bit when available
        return np.longdouble

FLOAT_TYPE = get_float_type()

# Token structure
Token = namedtuple('Token', ['value', 'type', 'line', 'col'])

# Global variables
OPERATORS = {'+', '-', '*', '/', '%', '^', '|', '<', '>', '==', '!=', '<=', '>='}
KEYWORDS = {'RES', 'MEM', 'if', 'then', 'else', 'for', 'V'}

history = []
memory = FLOAT_TYPE(0.0)

# Abstract Syntax Tree Node
class ASTNode:
    def __init__(self, node_type, value=None, children=None):
        self.type = node_type
        self.value = value
        self.children = children or []
        self.id = id(self)  # Unique ID for visualization
        
    def __repr__(self):
        return f"ASTNode({self.type}, {self.value})"
    
    def to_dict(self):
        """Convert AST to dictionary for JSON serialization"""
        return {
            'type': self.type,
            'value': self.value,
            'children': [child.to_dict() for child in self.children]
        }

    def get_type(self):
        """Retorna o tipo da expressão representada por este nó"""
        if self.type == 'INT':
            return 'INT'
        elif self.type == 'REAL':
            return 'REAL'
        elif self.type == 'MEM':
            return 'REAL'  # MEM sempre armazena REAL
        elif self.type == 'MEM_ASSIGN':
            return self.children[0].get_type()
        elif self.type == 'RES':
            return 'REAL'  # Histórico pode ser INT ou REAL, mas por simplicidade retornamos REAL
        elif self.type == 'IF':
            # Verifica se a condição é booleana ou numérica
            cond_type = self.children[0].get_type()
            if cond_type not in ['INT', 'REAL', 'BOOL']:
                raise TypeError(f"Condição do IF deve ser numérica ou booleana, recebeu {cond_type}")
            
            # Verifica se os branches têm o mesmo tipo
            then_type = self.children[1].get_type()
            else_type = self.children[2].get_type()
            if then_type != else_type:
                raise TypeError(f"Branches do IF devem ter o mesmo tipo. Recebeu {then_type} e {else_type}")
            return then_type
        elif self.type == 'FOR':
            # Verifica se o contador é inteiro
            count_type = self.children[0].get_type()
            if count_type != 'INT':
                raise TypeError(f"Contador do FOR deve ser INT, recebeu {count_type}")
            return self.children[1].get_type()
        elif self.type == 'BINARY_OP':
            left_type = self.children[0].get_type()
            right_type = self.children[1].get_type()
            op = self.value

            # Operações aritméticas
            if op in {'+', '-', '*', '^'}:
                if left_type == 'REAL' or right_type == 'REAL':
                    return 'REAL'
                elif left_type == 'INT' and right_type == 'INT':
                    return 'INT'
                else:
                    raise TypeError(f"Operação {op} não suportada entre {left_type} e {right_type}")
            
            # Operações de divisão
            elif op in {'/', '|', '%'}:
                if left_type not in ['INT', 'REAL'] or right_type not in ['INT', 'REAL']:
                    raise TypeError(f"Operação {op} requer operandos numéricos")
                return 'REAL'
            
            # Operações de comparação
            elif op in {'<', '>', '==', '!=', '<=', '>='}:
                if left_type not in ['INT', 'REAL'] or right_type not in ['INT', 'REAL']:
                    raise TypeError(f"Operação {op} requer operandos numéricos")
                return 'BOOL'
            
            else:
                raise TypeError(f"Operador desconhecido: {op}")
        else:
            raise TypeError(f"Tipo desconhecido: {self.type}")

class LL1Parser:
    """LL(1) Parser for the RPN language"""
    
    def __init__(self, tokens):
        self.tokens = deque(tokens)
        self.current_token = None
        self.advance()
        
    def advance(self):
        """Consume next token"""
        if self.tokens:
            self.current_token = self.tokens.popleft()
        else:
            self.current_token = Token('$', 'EOF', -1, -1)
    
    def peek(self):
        """Look at next token without consuming"""
        if self.tokens:
            return self.tokens[0]
        return Token('$', 'EOF', -1, -1)
    
    def peek_at(self, index):
        """Look at specific token ahead without consuming"""
        if index < len(self.tokens):
            return self.tokens[index]
        return Token('$', 'EOF', -1, -1)
    
    def parse(self):
        """Start parsing - S -> EXPR"""
        return self.parse_s()
    
    def parse_s(self):
        """S -> EXPR"""
        return self.parse_expr()
    
    def is_operator(self, token):
        """Check if token is an operator"""
        return token.type == 'OPERATOR' or token.value in OPERATORS
    
    def parse_expr(self):
        """Parse expression according to RPN grammar"""
        if self.current_token.value == '(':
            self.advance()  # consume '('
            return self.parse_paren_expr()
        elif self.current_token.type in ['INT', 'REAL']:
            return self.parse_number()
        elif self.current_token.value == 'if':
            return self.parse_if()
        else:
            raise SyntaxError(f"Token inesperado {self.current_token}. Lembre-se que a sintaxe deve estar em RPN (Reverse Polish Notation).\nExemplo: if ( 5 10 < ) then ( 20 15 + ) else ( 50 15 - )")
    
    def parse_paren_expr(self):
        """Parse expression inside parentheses"""
        # Look at first token to determine expression type
        first_token = self.current_token
        
        # Special constructs
        if first_token.value == 'if':
            return self.parse_if()
        elif first_token.value == 'for':
            return self.parse_for()
        elif first_token.value == 'MEM' and self.peek().value == ')':
            # (MEM)
            self.advance()  # consume 'MEM'
            if self.current_token.value != ')':
                raise SyntaxError(f"Expected ')', got {self.current_token}")
            self.advance()  # consume ')'
            return ASTNode('MEM')
        
        # Check for (INT RES) or (NUM MEM)
        if first_token.type in ['INT', 'REAL']:
            second_token = self.peek()
            if second_token.value == 'RES' and first_token.type == 'INT':
                # (INT RES)
                index = int(first_token.value)
                self.advance()  # consume INT
                self.advance()  # consume 'RES'
                if self.current_token.value != ')':
                    raise SyntaxError(f"Expected ')', got {self.current_token}")
                self.advance()  # consume ')'
                return ASTNode('RES', children=[ASTNode('INT', value=index)])
            elif second_token.value == 'MEM':
                # (NUM MEM)
                value = self.parse_number()
                self.advance()  # consume 'MEM'
                if self.current_token.value != ')':
                    raise SyntaxError(f"Expected ')', got {self.current_token}")
                self.advance()  # consume ')'
                return ASTNode('MEM_ASSIGN', children=[value])
        
        # Parse RPN expression: (operand1 operand2 operator)
        operand1 = self.parse_operand()
        operand2 = self.parse_operand()
        
        if not self.is_operator(self.current_token):
            raise SyntaxError(f"Expected operator, got {self.current_token}")
        
        operator = self.current_token.value
        self.advance()  # consume operator
        
        if self.current_token.value != ')':
            raise SyntaxError(f"Expected ')', got {self.current_token}")
        self.advance()  # consume ')'
        
        return ASTNode('BINARY_OP', value=operator, children=[operand1, operand2])
    
    def parse_operand(self):
        """Parse operand: EXPR | NUM | MEM"""
        if self.current_token.value == '(':
            return self.parse_expr()
        elif self.current_token.type in ['INT', 'REAL']:
            return self.parse_number()
        elif self.current_token.value == 'MEM':
            self.advance()
            return ASTNode('MEM')
        else:
            raise SyntaxError(f"Expected operand, got {self.current_token}")
    
    def parse_if(self):
        """Parse if-then-else expression"""
        self.advance()  # consume 'if'
        
        if self.current_token.value != '(': 
            raise SyntaxError(f"Esperado '(' após 'if', recebeu {self.current_token}")
        self.advance()  # consume '('
        # Parse condition in RPN format
        cond_operand1 = self.parse_operand()
        cond_operand2 = self.parse_operand()
        if not self.is_operator(self.current_token):
            raise SyntaxError(f"Esperado operador, recebeu {self.current_token}")
        cond_operator = self.current_token.value
        self.advance()  # consume operator
        if self.current_token.value != ')':
            raise SyntaxError(f"Esperado ')', recebeu {self.current_token}")
        self.advance()  # consume ')'
        condition = ASTNode('BINARY_OP', value=cond_operator, children=[cond_operand1, cond_operand2])
        
        if self.current_token.value != 'then':
            raise SyntaxError(f"Esperado 'then', recebeu {self.current_token}")
        self.advance()  # consume 'then'
        if self.current_token.value != '(': 
            raise SyntaxError(f"Esperado '(' após 'then', recebeu {self.current_token}")
        self.advance()  # consume '('
        # Parse then branch in RPN format
        then_operand1 = self.parse_operand()
        then_operand2 = self.parse_operand()
        if not self.is_operator(self.current_token):
            raise SyntaxError(f"Esperado operador, recebeu {self.current_token}")
        then_operator = self.current_token.value
        self.advance()  # consume operator
        if self.current_token.value != ')':
            raise SyntaxError(f"Esperado ')', recebeu {self.current_token}")
        self.advance()  # consume ')'
        then_branch = ASTNode('BINARY_OP', value=then_operator, children=[then_operand1, then_operand2])
        
        if self.current_token.value != 'else':
            raise SyntaxError(f"Esperado 'else', recebeu {self.current_token}")
        self.advance()  # consume 'else'
        if self.current_token.value != '(': 
            raise SyntaxError(f"Esperado '(' após 'else', recebeu {self.current_token}")
        self.advance()  # consume '('
        # Parse else branch in RPN format
        else_operand1 = self.parse_operand()
        else_operand2 = self.parse_operand()
        if not self.is_operator(self.current_token):
            raise SyntaxError(f"Esperado operador, recebeu {self.current_token}")
        else_operator = self.current_token.value
        self.advance()  # consume operator
        if self.current_token.value != ')':
            raise SyntaxError(f"Esperado ')', recebeu {self.current_token}")
        self.advance()  # consume ')'
        else_branch = ASTNode('BINARY_OP', value=else_operator, children=[else_operand1, else_operand2])
        
        return ASTNode('IF', children=[condition, then_branch, else_branch])
    
    def parse_for(self):
        """Parse for loop expression"""
        self.advance()  # consume 'for'
        
        if self.current_token.type != 'INT':
            raise SyntaxError(f"Expected INT, got {self.current_token}")
        count = ASTNode('INT', value=int(self.current_token.value))
        self.advance()
        
        body = self.parse_expr()
        
        if self.current_token.value != ')':
            raise SyntaxError(f"Expected ')', got {self.current_token}")
        self.advance()
        
        return ASTNode('FOR', children=[count, body])
    
    def parse_number(self):
        """Parse numeric literal"""
        if self.current_token.type == 'INT':
            node = ASTNode('INT', value=int(self.current_token.value))
            self.advance()
            return node
        elif self.current_token.type == 'REAL':
            node = ASTNode('REAL', value=float(self.current_token.value))
            self.advance()
            return node
        else:
            raise SyntaxError(f"Expected number, got {self.current_token}")

def dfa_lexer(line, line_num):
    """Lexical analyzer using DFA approach"""
    # Skip comment lines
    if line.strip().startswith('#'):
        return []
    
    tokens = []
    i = 0
    while i < len(line):
        ch = line[i]
        if ch.isspace():
            i += 1
            continue
        elif ch == '(':
            tokens.append(Token('(', 'LPAREN', line_num, i))
            i += 1
        elif ch == ')':
            tokens.append(Token(')', 'RPAREN', line_num, i))
            i += 1
        elif ch in ['<', '>', '!', '=']:
            # Handle multi-character operators
            start = i
            i += 1
            if i < len(line) and line[i] == '=':
                i += 1
            op = line[start:i]
            if op in OPERATORS:
                tokens.append(Token(op, 'OPERATOR', line_num, start))
            else:
                raise SyntaxError(f"Unrecognized operator '{op}' at line {line_num}, col {start}")
        elif ch in OPERATORS:
            tokens.append(Token(ch, 'OPERATOR', line_num, i))
            i += 1
        elif ch.isdigit() or ch == '.':
            # Parse numbers including scientific notation
            start = i
            has_dot = False
            has_exp = False
            
            # Parse the main part of the number
            while i < len(line) and (line[i].isdigit() or line[i] == '.'):
                if line[i] == '.':
                    if has_dot:
                        break  # Second dot is not allowed
                    has_dot = True
                i += 1
            
            # Check for scientific notation
            if i < len(line) and line[i] in ['e', 'E']:
                has_exp = True
                i += 1
                # Optional sign after exponent
                if i < len(line) and line[i] in ['+', '-']:
                    i += 1
                # Exponent digits
                if i < len(line) and line[i].isdigit():
                    while i < len(line) and line[i].isdigit():
                        i += 1
                else:
                    # Invalid scientific notation
                    raise SyntaxError(f"Malformed number '{line[start:i]}' at line {line_num}")
            
            num = line[start:i]
            try:
                float(num)  # Test validity
                if has_dot or has_exp:
                    tokens.append(Token(num, 'REAL', line_num, start))
                else:
                    tokens.append(Token(num, 'INT', line_num, start))
            except:
                raise SyntaxError(f"Malformed number '{num}' at line {line_num}")
        elif ch.isalpha():
            # Parse identifiers and keywords
            start = i
            while i < len(line) and line[i].isalnum():
                i += 1
            word = line[start:i]
            if word in KEYWORDS:
                tokens.append(Token(word, 'KEYWORD', line_num, start))
            else:
                tokens.append(Token(word, 'IDENTIFIER', line_num, start))
        else:
            raise SyntaxError(f"Unrecognized character '{ch}' at line {line_num}, col {i}")
    return tokens

def evaluate_ast(node):
    """Evaluate AST and return result"""
    global memory
    
    if node is None:
        raise ValueError("Null node in AST evaluation")
    
    # Primeiro verifica o tipo da expressão
    try:
        node_type = node.get_type()
    except TypeError as e:
        raise TypeError(f"Erro de tipo: {str(e)}")
    
    if node.type == 'INT':
        return int(node.value)
    elif node.type == 'REAL':
        return FLOAT_TYPE(node.value)
    elif node.type == 'MEM':
        return memory
    elif node.type == 'MEM_ASSIGN':
        val = evaluate_ast(node.children[0])
        memory = FLOAT_TYPE(val)
        return val
    elif node.type == 'RES':
        index = evaluate_ast(node.children[0])
        # Ensure index is valid
        if index > 0 and index <= len(history):
            return history[-index]
        else:
            return 0  # Default value if index is out of bounds
    elif node.type == 'IF':
        cond = evaluate_ast(node.children[0])
        # Trata condição booleana ou numérica
        if isinstance(cond, (int, float)):
            cond = bool(cond)
        if cond:
            return evaluate_ast(node.children[1])
        else:
            return evaluate_ast(node.children[2])
    elif node.type == 'FOR':
        count = evaluate_ast(node.children[0])
        result = 0
        for _ in range(count):
            result = evaluate_ast(node.children[1])
        return result
    elif node.type == 'BINARY_OP':
        left = evaluate_ast(node.children[0])
        right = evaluate_ast(node.children[1])
        op = node.value
        
        # Verifica o tipo da operação
        if node_type == 'BOOL':
            # Operações de comparação
            if op == '<': 
                return 1 if left < right else 0
            elif op == '>': 
                return 1 if left > right else 0
            elif op == '==': 
                return 1 if left == right else 0
            elif op == '!=': 
                return 1 if left != right else 0
            elif op == '<=': 
                return 1 if left <= right else 0
            elif op == '>=': 
                return 1 if left >= right else 0
        elif node_type == 'REAL':
            # Operações que sempre retornam REAL
            if op == '+': 
                return FLOAT_TYPE(left + right)
            elif op == '-': 
                return FLOAT_TYPE(left - right)
            elif op == '*': 
                return FLOAT_TYPE(left * right)
            elif op == '/':  # Divisão real
                if right == 0:
                    raise ZeroDivisionError("Divisão por zero")
                return FLOAT_TYPE(left / right)
            elif op == '%':  # Modulo
                if right == 0:
                    raise ZeroDivisionError("Modulo por zero")
                return FLOAT_TYPE(left % right)
            elif op == '^':  # Power
                return FLOAT_TYPE(left ** right)
            elif op == '|':  # Divisão real
                if right == 0:
                    raise ZeroDivisionError("Divisão por zero")
                return FLOAT_TYPE(left / right)
        elif node_type == 'INT':
            # Operações que retornam INT
            if op == '+': 
                return int(left + right)
            elif op == '-': 
                return int(left - right)
            elif op == '*': 
                return int(left * right)
            elif op == '/':  # Divisão inteira
                if right == 0:
                    raise ZeroDivisionError("Divisão por zero")
                return int(left) // int(right)
            elif op == '%':  # Modulo
                if right == 0:
                    raise ZeroDivisionError("Modulo por zero")
                return int(left) % int(right)
            elif op == '^':  # Power com expoente inteiro
                return int(left ** int(right))
    else:
        raise ValueError(f"Unknown node type: {node.type}")

def visualize_ast(node, filename="ast"):
    """Visualize AST as PDF and text"""
    if GRAPHVIZ_AVAILABLE:
        dot = Digraph(comment='Abstract Syntax Tree')
        dot.attr(rankdir='TB', size='8,10')
        
        def add_nodes(node, parent_id=None):
            node_id = str(node.id)
            label = f"{node.type}"
            if node.value is not None:
                label += f"\n{node.value}"
            
            dot.node(node_id, label)
            
            if parent_id:
                dot.edge(parent_id, node_id)
            
            for child in node.children:
                add_nodes(child, node_id)
        
        add_nodes(node)
        # Generate PDF only
        dot.render(filename, format='pdf', cleanup=True)
        print(f"📊 Tree saved as: {filename}.pdf")
    else:
        print("⚠️  Graphviz not installed - saving text format only")
    
    # Always save as text too
    with open(f"{filename}.txt", 'w') as f:
        f.write(str(node.to_dict()))

def print_ast_text(node, indent=0):
    """Print AST in text format on terminal"""
    prefix = "  " * indent
    tipo = ""
    try:
        tipo = f" [{node.get_type()}]"
    except TypeError as e:
        tipo = f" [ERRO: {str(e)}]"
    print(f"{prefix}{node.type}{tipo}", end="")
    if node.value is not None:
        print(f": {node.value}")
    else:
        print()
    
    for child in node.children:
        print_ast_text(child, indent + 1)

def main():
    """Main execution function"""
    if len(sys.argv) != 2:
        print("Usage: python analisador.py input.txt")
        sys.exit(1)

    filename = sys.argv[1]
    
    # Print system information
    print(f"System architecture: {platform.machine()}")
    print(f"Using float type: {FLOAT_TYPE}")
    print()
    
    with open(filename, 'r') as f:
        lines = f.readlines()

    for idx, line in enumerate(lines):
        # Skip empty lines
        if not line.strip():
            continue
            
        print(f"\n{'='*50}")
        print(f"Line {idx+1}: {line.strip()}")
        print(f"{'='*50}")
        
        try:
            # Lexical Analysis
            tokens = dfa_lexer(line.strip(), idx+1)
            
            # Skip comment lines
            if not tokens:
                print("💬 Comment line ignored")
                continue
                
            print("\n--- TOKENS ---")
            for i, t in enumerate(tokens):
                print(f"  Token[{i}] => value: '{t.value}', class: {t.type}, position: ({t.line}, {t.col})")
            
            # Syntactic Analysis
            parser = LL1Parser(tokens)
            ast = parser.parse()
            
            print("\n--- ABSTRACT SYNTAX TREE ---")
            print_ast_text(ast)
            
            # Evaluation
            result = evaluate_ast(ast)
            history.append(result)
            
            print(f"\n--- RESULT ---")
            print(f"✅ Value: {result}")
            
            # AST Visualization
            visualize_ast(ast, f"ast_line_{idx+1}")
            
        except ZeroDivisionError as e:
            print(f"\n❌ ARITHMETIC ERROR: {str(e)}")
        except SyntaxError as e:
            print(f"\n❌ SYNTAX ERROR: {str(e)}")
        except Exception as e:
            print(f"\n❌ ERROR: {str(e)}")

if __name__ == '__main__':
    main()