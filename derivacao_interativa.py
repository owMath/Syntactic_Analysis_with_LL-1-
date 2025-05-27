import sys
from tabulate import tabulate
import os
try:
    from colorama import init, Fore, Back, Style
    init(autoreset=True)
except ImportError:
    # fallback para não colorir se não tiver colorama
    class Dummy:
        def __getattr__(self, name):
            return ''
    Fore = Back = Style = Dummy()

# Definições da gramática e tabela LL(1) simplificadas para o exemplo ( 2 3 + )
OPERATORS = {'+', '-', '*', '/', '%', '^', '|', '<', '>', '==', '!=', '<=', '>='}

tokens = ['(', 'INT', 'INT', '+', ')', '$']

# Tabela LL(1) simplificada
ll1_table = {
    'S': {'(': 'EXPR', 'INT': 'EXPR', 'REAL': 'EXPR'},
    'EXPR': {'(': '( PARSE_PAREN_EXPR', 'INT': 'NUM', 'REAL': 'NUM'},
    'PARSE_PAREN_EXPR': {'(': 'OPERAND OPERAND OPERATOR )', 'INT': 'CHECK_SECOND', 'REAL': 'CHECK_SECOND', 'MEM': 'CHECK_TYPE'},
    'CHECK_SECOND': {'(': 'OPERAND OPERAND OPERATOR )', 'INT': 'OPERAND OPERAND OPERATOR )', 'REAL': 'OPERAND OPERAND OPERATOR )', 'MEM': 'OPERAND OPERAND OPERATOR )'},
    'OPERAND': {'(': 'EXPR', 'INT': 'NUM', 'REAL': 'NUM', 'MEM': 'MEM'},
    'NUM': {'INT': 'INT', 'REAL': 'REAL'},
    'OPERATOR': {'+': '+', '-': '-', '*': '*', '/': '/', '%': '%', '^': '^', '|': '|', '<': '<', '>': '>', '==': '==', '!=': '!=', '<=': '<=', '>=': '>='}
}

def get_production(non_terminal, terminal):
    if terminal.isdigit():
        terminal = 'INT'
    elif '.' in terminal:
        terminal = 'REAL'
    return ll1_table.get(non_terminal, {}).get(terminal)

def print_ll1_table_highlight(nt, current_token):
    """Mostra a tabela LL(1) inteira, destacando a célula da produção aplicada"""
    terminals = set()
    for rules in ll1_table.values():
        terminals.update(rules.keys())
    terminals = sorted(terminals)
    table = []
    for ntt in ll1_table:
        row = []
        for t in terminals:
            prod = ll1_table[ntt].get(t, '—')
            if ntt == nt and t == current_token:
                prod = Back.YELLOW + Fore.BLACK + str(prod) + Style.RESET_ALL
            row.append(prod)
        table.append([ntt] + row)
    headers = ["NT"] + terminals
    print("\nTabela LL(1) (célula amarela = produção aplicada no passo):")
    print(tabulate(table, headers=headers, tablefmt="fancy_grid", stralign="center", numalign="center"))
    print()

def clear_screen():
    os.system('cls' if os.name == 'nt' else 'clear')

def main():
    print("Expressão: ( 2 3 + )\n")
    print("Legenda: célula amarela = produção aplicada no passo atual\n")
    stack = ['S']
    input_tokens = tokens.copy()
    current_input = 0
    step = 1
    while stack:
        clear_screen()
        print("Expressão: ( 2 3 + )\n")
        print("Legenda: célula amarela = produção aplicada no passo atual\n")
        top = stack[-1]
        current_token = input_tokens[current_input]
        print(f"Passo {step}:")
        print(f"  Pilha: {' '.join(stack)}")
        print(f"  Entrada: {' '.join(input_tokens[current_input:])}")
        print_ll1_table_highlight(top, current_token)
        if top not in ll1_table:
            if top in OPERATORS and current_token in OPERATORS:
                print(f"  ✓ Consumindo operador: {top}")
                stack.pop()
                current_input += 1
            elif top == current_token:
                print(f"  ✓ Consumindo terminal: {top}")
                stack.pop()
                current_input += 1
            else:
                print(f"  ❌ Erro: Terminal esperado '{top}', encontrado '{current_token}'")
                break
        else:
            production = get_production(top, current_token)
            if production:
                print(f"  → Aplicando regra: {top} -> {production}")
                stack.pop()
                symbols = production.split()
                for symbol in reversed(symbols):
                    if symbol != 'ε':
                        stack.append(symbol)
            else:
                print(f"  ❌ Erro: Não há regra para {top} com entrada '{current_token}'")
                break
        input("Pressione ENTER para o próximo passo...")
        step += 1
    if not stack and current_input == len(input_tokens) - 1:
        print("✅ Derivação concluída com sucesso!")
    else:
        print("❌ Derivação falhou!")

if __name__ == '__main__':
    main() 