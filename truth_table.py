#!/usr/bin/python

###
### Generates a truth table for a boolean algebra expression.
###
### E.G.
### 
### $ python truth_table.py
###   > A . (B + !C)
###         A . (B + !C) = OUT
###  ------------------------------- 
### |   A   |   B   |   C   |  OUT  |
### |-------------------------------|
### |   0   |   0   |   0   |   0   |
### |   0   |   0   |   1   |   0   |
### |   0   |   1   |   0   |   0   |
### |   0   |   1   |   1   |   0   |
### |   1   |   0   |   0   |   1   |
### |   1   |   0   |   1   |   0   |
### |   1   |   1   |   0   |   1   |
### |   1   |   1   |   1   |   1   |
###  ------------------------------- 
###
### 
### The program works by converting the initial expression to reverse-polish
### notation. The program then evaluates every value the identifiers can have
### and prints a table of the results.

### Constants
OP_OR = '+'             # Character for the boolean OR operator.
OP_AND = '.'            # Boolean AND operator.
OP_NOT = '\''            # Boolean negation.
OP_XOR = '^'

T_LBRACKET = '('        # Left bracket token
T_RBRACKET = ')'        # Right bracket token
T_IDENTIFIER = 256      # Identifier token
T_OPERATOR = 257        # Operator token
T_CONSTANT = 260        # Constant token
ASSOC_LEFT = 259        # Left association
ASSOC_RIGHT = 260       # Right association

# Characters denoting identifiers.
IDENTIFIERS = ('A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z')
OPERATORS = (OP_OR, OP_XOR, OP_AND, OP_NOT)

PRECEDENCE = dict(zip(OPERATORS, range(len(OPERATORS))))
ASSOCIATION = {OP_NOT: ASSOC_LEFT, OP_OR: ASSOC_LEFT, OP_XOR: ASSOC_LEFT,
                OP_AND: ASSOC_LEFT}

class MismatchedBracketError(Exception):
    def __init__(self, message='No matching bracket found.'):
        Exception.__init__(self, message)

class ExpressionSyntaxError(Exception):
    def __init__(self, message='Invalid Boolean Algebra expression syntax'):
        Exception.__init__(self, message)

def tokenize(source):
    ''' Given the string source expression, generate a list of tokens. '''
    tokens = []
    for char in source:
        if char in IDENTIFIERS:
            tokens.append((T_IDENTIFIER, char))
        elif char in OPERATORS:
            tokens.append((T_OPERATOR, char))
        elif char == T_LBRACKET:
            tokens.append(T_LBRACKET)
        elif char == T_RBRACKET:
            tokens.append(T_RBRACKET)
        elif char in '10':
            # Convert from using 1 and 0 to denote True and False to bools.
            tokens.append((T_CONSTANT, char == '1'))
        # Ignore all other inputs.
    return tokens

def to_rpn(tokens):
    ''' Implements Dijkstra's Shunting-yard algorithm to create a list of tokens
    in reverse-polish notation from the original infix notation.'''
    output = []
    stack = []
    for token in tokens:
        if token[0] == T_CONSTANT or token[0] == T_IDENTIFIER:
            # Just append constant bools (T/F) and identifiers to the output stack.
            output.append(token)
        if token[0] == T_OPERATOR:
            # If the token is an operator and the top of the stack is an 
            # operator and either the token is left associative and the
            # token's precedence is less than or equal to the precedence of
            # the operator on the stack, or the token's precedence is less than
            # the precedence of the operator on the stack, pop values off the 
            # stack onto the output queue.
            while stack and stack[-1][0] == T_OPERATOR and \
              ((ASSOCIATION[token[1]] == ASSOC_LEFT and PRECEDENCE[token[1]] <= PRECEDENCE[stack[-1][1]]) \
              or PRECEDENCE[token[1]] < PRECEDENCE[stack[-1][1]]):
                output.append(stack.pop())
            stack.append(token)
        if token[0] == T_LBRACKET:
            # Append left brackets to the stack.
            stack.append(token)
        if token[0] == T_RBRACKET:
            # Pop values off the stack on to the output stack until the right
            # bracket's matching bracket is at the top of the stack, then pop
            # off the matching bracket and discard it.
            # In the event a matching left bracket is not found, raise a
            # MismatchedBracketError.
            try:
                while stack[-1][0] != T_LBRACKET:
                    output.append(stack.pop())
                stack.pop()
            except IndexError:
                raise MismatchedBracketError
    # Pop all remaining values on the stack on to the output stack, raising an
    # exception if any unmatched brackets are found.
    while stack:
        if stack[-1][0] == T_LBRACKET or stack[-1][0] == T_RBRACKET:
            raise MismatchedBracketError
        output.append(stack.pop())
    return output


def evaluate(stack, op):
    ''' Evaluate the stack according to rules defined for the operator
    and push the result on to the stack.'''
    if op == OP_OR:
        b = stack.pop()
        a = stack.pop()
        stack.append(a or b)
    elif op == OP_AND:
        b = stack.pop()
        a = stack.pop()
        stack.append(a and b)
    elif op == OP_XOR:
        b = stack.pop()
        a = stack.pop()
        stack.append((a and (not b)) or ((not a) and b))
    elif op == OP_NOT:
        stack.append(not stack.pop())

def gen_truth_table(rpn):
    ''' Calculates the truth table for the expression presented in reverse-
    polish notation.
    Returns a list of dictionaries of the identifier's values and the output'''

    # Create a dictionary mapping identifiers to booleans, starting with all false.
    mappings = dict.fromkeys([name for t_type, name in rpn if t_type == T_IDENTIFIER], False)
    # Get an alphabetical list of distinct identifiers in the expression.
    identifiers = sorted(mappings.keys()) # By using the keys of the mapping dict, ensures no dupes.
    table = []
    for i in xrange(2**len(identifiers)):
        # Calculate the result of the expression. As the expression is now in
        # postfix-notation, the final result is simply the only value on the    
        # stack after the expression has been evaluated.
        stack = []
        for token in rpn:
            if token[0] == T_IDENTIFIER:
                stack.append(mappings[token[1]])
            if token[0] == T_CONSTANT:
                stack.append(token[1])
            if token[0] == T_OPERATOR:
                try:
                    evaluate(stack, token[1])
                except IndexError:
                    # Occurs when nothing to pop off the stack due to a syntax
                    # error in the expression
                    raise ExpressionSyntaxError
        # Add the identifier values and the result as a dictionary to the table
        table.append({'OUT' : stack[0]})
        table[-1].update(mappings)
        # Change the identifier values. Effectively binary increment of one.
        for key in identifiers[::-1]: 
            mappings[key] = not mappings[key]
            if mappings[key]: break
    return table

def format_truth_table(table):
    mappings = {True:'1'.center(7), False:'0'.center(7)}
    
    headings = table[0].keys()
    headings.sort() # Sorts the headings alphabetically.
    headings.sort(key=len) # Sorts 'OUT' to the end of the list.
                           # Stable sort leaves the order of identifiers 
    s = ' ' + '-' * (8 * len(headings) - 1) + ' \n'
    s += '|' + '|'.join([heading.center(7) for heading in headings])
    # Dividing line break. 
    s += '|\n|' + '-' * (8 * len(headings) - 1) + '|'
    for row in table:
        # Rows of values of identifiers ending with the output, delimited with pipes.
        s += '\n|' + '|'.join([mappings[row[heading]] for heading in headings]) + '|'
    # Another dividing line break.
    s += '\n ' + '-' * (8 * len(headings)-1)
    return s

def parse(expression):
    '''Returns the truth table of an expression as a string'''
    table = gen_truth_table(to_rpn(tokenize(expression)))
    s = (expression + ' = OUT').center(len(table[0])*8+2) + '\n'
    return s + format_truth_table(table)
    
if __name__ == '__main__':
    print parse(raw_input())

