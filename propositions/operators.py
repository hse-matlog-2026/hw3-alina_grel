# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5

    if is_constant(formula.root):
        if formula.root == 'T':
            p = Formula('p')
            return Formula('|', p, Formula('~', p))
        else:  
            p = Formula('p')
            return Formula('&', p, Formula('~', p))
    
    if is_variable(formula.root):
        return Formula(formula.root)
    
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))

    if is_binary(formula.root):
        first = to_not_and_or(formula.first)
        second = to_not_and_or(formula.second)
        
        if formula.root == '&' or formula.root == '|':
            return Formula(formula.root, first, second)
        elif formula.root == '->':
            return Formula('|', Formula('~', first), second)
        elif formula.root == '-|':
            return Formula('~', Formula('|', first, second))
        elif formula.root == '-&':
            return Formula('~', Formula('&', first, second))
        elif formula.root == '+':
            return Formula('&',Formula('|', first, second) , Formula('~', Formula('&', first, second)))
        elif formula.root == '<->':
            return Formula('&', Formula('|', Formula('~', first), second), Formula('|', Formula('~', second), first))

    return formula

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    nao= to_not_and_or(formula)

    if is_constant(nao.root):
        if nao.root == 'T':
            p = Formula('p')
            return Formula('|', p, Formula('~', p))
        else: 
            p = Formula('p')
            return Formula('&', p, Formula('~', p))

    if is_variable(nao.root):
        return Formula(nao.root)
    
    if is_unary(nao.root):
        return Formula('~', to_not_and(nao.first))
    
    if is_binary(nao.root):
        first = to_not_and(nao.first)
        second = to_not_and(nao.second)
        
        if nao.root == '&':
            return Formula('&', first, second)
        elif nao.root == '|':
            return Formula('~', Formula('&', Formula('~', first), Formula('~', second)))
    
    return formula_not_and_or

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    nao= to_not_and_or(formula)

    if is_constant(nao.root):
        if nao.root == 'T':
            p = Formula('p')
            return Formula('-&', p, Formula('-&', p, p))
        else:  
            p = Formula('p')
            x = Formula('-&', p, Formula('-&', p, p))
            return Formula('-&', x, x)
    
    if is_variable(nao.root):
        return Formula(nao.root)
    
    if is_unary(nao.root):
        return Formula('-&', to_nand(nao.first), to_nand(nao.first))
    
    if is_binary(nao.root):
        first = to_nand(nao.first)
        second = to_nand(nao.second)
        
        if nao.root == '&':
            return Formula('-&', Formula('-&', first, second), Formula('-&', first, second))
        elif nao.root == '|':
            return Formula('-&', Formula('-&', first, first), Formula('-&', second, second))
    
    return formula_not_and_or

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    nao= to_not_and_or(formula)

    if is_constant(nao.root):
        if nao.root == 'T':
            p = Formula('p')
            return Formula('->', p, p)
        else: 
            p = Formula('p')
            return Formula('~', Formula('->', p, p))

    if is_variable(nao.root):
        return Formula(nao.root)
    
    if is_unary(nao.root):
        return Formula('~', to_implies_not(nao.first))
    
    if is_binary(nao.root):
        first = to_implies_not(nao.first)
        second = to_implies_not(nao.second)
        
        if nao.root == '&':
            return Formula('~', Formula('->', first, Formula('~', second)))
        elif nao.root == '|':
            return Formula('->',Formula('~', first), second)
        elif nao.root == '->':
            return Formula('->', first, second)
    
    return formula_not_and_or

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    fin = to_implies_not(formula)
    
    if is_constant(fin.root):
        if fin.root == 'T':
            return Formula('->', Formula('F'), Formula('F'))
        else:
            return Formula('F')
    
    if is_variable(fin.root):
        return Formula(fin.root)
    
    if is_unary(fin.root):
        return Formula('->', to_implies_false(fin.first), Formula('F'))
    
    if is_binary(fin.root):
        if fin.root == '->':
            return Formula('->', to_implies_false(fin.first), to_implies_false(fin.second))
    
    return fin
