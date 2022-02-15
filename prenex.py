# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    if is_quantifier(formula.root):
        return False
    elif is_variable(formula.root) or is_constant(formula.root) or \
            is_relation(formula.root) or is_equality(formula.root):
        return True
    elif is_unary(formula.root):
        return is_quantifier_free(formula.first)
    return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)
    return is_quantifier_free(formula)


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def _uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.5
    prover, equivalence, line = _prove_equiv(formula)
    new_formula = equivalence.first.second
    return new_formula, prover.qed()


def _prove_equiv(formula: Formula) -> \
        Tuple[Prover, Formula, int]:
    """
    Args:
        formula:
            The formula to process
    Returns:
        A tuple contatining a prover that proved that formula is equivalent
        to an instantiation of itself with unique variables, the
        equivalence formula and the line number of the equivalence
    """
    if is_quantifier_free(formula):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        new_formula = Formula('&', Formula('->', formula, formula),
                              Formula('->', formula, formula))
        taut = prover.add_tautology(new_formula)
        return prover, new_formula, taut
    elif is_unary(formula.root):
        prover, equivalence, line = _prove_equiv(formula.first)
        equiv = equivalence.first.second
        new_first = Formula('->', formula, Formula('~', equiv))
        new_second = Formula('->', Formula('~', equiv), formula)
        new_equivalence = Formula('&', new_first, new_second)
        taut = prover.add_tautology(Formula('->', equivalence, new_equivalence))
        mp = prover.add_mp(new_equivalence, line, taut)
        return prover, new_equivalence, mp
    elif is_binary(formula.root):
        prover1, equivalence1, line1 = _prove_equiv(formula.first)
        prover2, equivalence2, line2 = _prove_equiv(formula.second)
        proof2 = prover2.qed()
        line2 = prover1.add_proof(equivalence2, proof2)
        equiv1 = equivalence1.first.second
        equiv2 = equivalence2.first.second
        op1 = Formula(formula.root, formula.first, formula.second)
        op2 = Formula(formula.root, equiv1, equiv2)
        new_first = Formula('->', op1, op2)
        new_second = Formula('->', op2, op1)
        new_equivalence = Formula('&', new_first, new_second)
        taut = prover1.add_tautology(Formula(
            '->', equivalence1, Formula('->', equivalence2, new_equivalence)))
        mp1 = prover1.add_mp(Formula('->', equivalence2, new_equivalence),
                             line1, taut)
        mp2 = prover1.add_mp(new_equivalence, line2, mp1)
        return prover1, new_equivalence, mp2
    new_var = next(fresh_variable_name_generator)
    prover, equivalence, line = _prove_equiv(formula.predicate)
    equiv = equivalence.first.second.substitute({formula.variable: Term(new_var)})
    new_first = Formula('->', formula, Formula(formula.root, new_var, equiv))
    new_second = Formula('->', Formula(formula.root, new_var, equiv), formula)
    new_equivalence = Formula('&', new_first, new_second)
    if formula.root == 'A':
        imp = prover.add_instantiated_assumption(
            Formula('->', equivalence, new_equivalence),
            Schema(Formula.parse(
                '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
                   {'x', 'y', 'R', 'Q'}), {'R': formula.predicate.substitute(
                {formula.variable: Term('_')}),
                'Q': equiv.substitute({new_var: Term('_')}),
                'x': formula.variable, 'y': new_var})
    else:
        imp = prover.add_instantiated_assumption(
            Formula('->', equivalence, new_equivalence),
            Schema(Formula.parse(
                '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
                   {'x', 'y', 'R', 'Q'}), {'R': formula.predicate.substitute(
                {formula.variable: Term('_')}),
                'Q': equiv.substitute({new_var: Term('_')}),
                'x': formula.variable, 'y': new_var})
    mp = prover.add_mp(new_equivalence, line, imp)
    return prover, new_equivalence, mp


def _pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    if not is_quantifier(formula.first.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        new_formula = Formula('&', Formula('->', formula, formula),
                              Formula('->', formula, formula))
        prover.add_tautology(new_formula)
        return formula, prover.qed()
    else:
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        var = formula.first.variable
        op_quan = _opposite_quantifier(formula.first.root)
        pulled_formula = Formula(op_quan, var,
                                 Formula('~', formula.first.predicate))
        sub_form = Formula('~', formula.first.predicate)
        new_first = Formula('->', formula, pulled_formula)
        new_second = Formula('->', pulled_formula, formula)
        new_equivalence = Formula('&', new_first, new_second)
        if formula.first.root == 'A':
            equiv_line = prover.add_instantiated_assumption(
                new_equivalence, Schema(Formula.parse(
                    '((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
                    {'x', 'R'}),
                {'x': var,
                 'R': formula.first.predicate.substitute(
                     {var: Term('_')})})
        else:
            equiv_line = prover.add_instantiated_assumption(
                new_equivalence, Schema(Formula.parse(
                    '((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
                    {'x', 'R'}),
                {'x': var,
                 'R': formula.first.predicate.substitute(
                     {var: Term('_')})})
        equiv_formula, sub_proof = \
            _pull_out_quantifications_across_negation(sub_form)
        sub_equiv = equivalence_of(sub_form, equiv_formula)
        sub_equiv_line = prover.add_proof(sub_equiv, sub_proof)
        side1 = Formula(op_quan, var, sub_form)
        side2 = Formula(op_quan, var, equiv_formula)
        equivalence2 = equivalence_of(side1, side2)
        if formula.first.root == 'A':
            cond = prover.add_instantiated_assumption(Formula(
                '->', sub_equiv, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': sub_form.substitute({var: Term('_')}),
                 'Q': equiv_formula.substitute({var: Term('_')})})
        else:
            cond = prover.add_instantiated_assumption(Formula(
                '->', sub_equiv, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': sub_form.substitute({var: Term('_')}),
                 'Q': equiv_formula.substitute({var: Term('_')})})
        mp = prover.add_mp(equivalence2, sub_equiv_line, cond)
        equivalence3 = equivalence_of(formula, side2)
        taut_formula = Formula('->', new_equivalence, Formula('->', equivalence2,
                                                      equivalence3))
        taut = prover.add_tautology(taut_formula)
        mp1 = prover.add_mp(Formula('->', equivalence2, equivalence3),
                            equiv_line, taut)
        prover.add_mp(equivalence3, mp, mp1)
        return side2, prover.qed()


def _opposite_quantifier(quantifier):
    """Returns the opposite quantifier of the one given"""
    if quantifier == 'A':
        return 'E'
    return 'A'


def _pull_out_quantifications_from_left_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    if not is_quantifier(formula.first.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        new_formula = Formula('&', Formula('->', formula, formula),
                              Formula('->', formula, formula))
        prover.add_tautology(new_formula)
        return formula, prover.qed()
    else:
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        var = formula.first.variable
        if formula.root == '&' or formula.root == '|':
            op_quan = formula.first.root
        else:
            op_quan = _opposite_quantifier(formula.first.root)
        pulled_formula = Formula(op_quan, var,
                                 Formula(formula.root, formula.first.predicate,
                                         formula.second))
        sub_form = Formula(formula.root, formula.first.predicate, formula.second)
        new_first = Formula('->', formula, pulled_formula)
        new_second = Formula('->', pulled_formula, formula)
        new_equivalence = Formula('&', new_first, new_second)
        if formula.first.root == 'A':
            if formula.root == '&':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.first.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.second})
                sec_quan = 'A'
            elif formula.root == '|':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.first.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.second})
                sec_quan = 'A'
            else:
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.first.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.second})
                sec_quan = 'E'
        else:
            if formula.root == '&':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.first.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.second})
                sec_quan = 'E'
            elif formula.root == '|':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.first.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.second})
                sec_quan = 'E'
            else:
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.first.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.second})
                sec_quan = 'A'
        equiv_formula, sub_proof = \
            _pull_out_quantifications_from_left_across_binary_operator(sub_form)
        sub_equiv = equivalence_of(sub_form, equiv_formula)
        sub_equiv_line = prover.add_proof(sub_equiv, sub_proof)
        side1 = Formula(sec_quan, var, sub_form)
        side2 = Formula(sec_quan, var, equiv_formula)
        equivalence2 = equivalence_of(side1, side2)
        if sec_quan == 'E':
            cond = prover.add_instantiated_assumption(Formula(
                '->', sub_equiv, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': sub_form.substitute({var: Term('_')}),
                 'Q': equiv_formula.substitute({var: Term('_')})})
        else:
            cond = prover.add_instantiated_assumption(Formula(
                '->', sub_equiv, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': sub_form.substitute({var: Term('_')}),
                 'Q': equiv_formula.substitute({var: Term('_')})})
        mp = prover.add_mp(equivalence2, sub_equiv_line, cond)
        equivalence3 = equivalence_of(formula, side2)
        taut_formula = Formula('->', new_equivalence, Formula('->', equivalence2,
                                                      equivalence3))
        taut = prover.add_tautology(taut_formula)
        mp1 = prover.add_mp(Formula('->', equivalence2, equivalence3),
                            equiv_line, taut)
        prover.add_mp(equivalence3, mp, mp1)
        return side2, prover.qed()


"""
Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'})
"""
def _pull_out_quantifications_from_right_across_binary_operator(formula:
                                                                Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    if not is_quantifier(formula.second.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        new_formula = Formula('&', Formula('->', formula, formula),
                              Formula('->', formula, formula))
        prover.add_tautology(new_formula)
        return formula, prover.qed()
    else:
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        var = formula.second.variable
        op_quan = formula.second.root
        pulled_formula = Formula(op_quan, var,
                                 Formula(formula.root, formula.first,
                                         formula.second.predicate))
        sub_form = Formula(formula.root, formula.first, formula.second.predicate)
        new_first = Formula('->', formula, pulled_formula)
        new_second = Formula('->', pulled_formula, formula)
        new_equivalence = Formula('&', new_first, new_second)
        if formula.second.root == 'A':
            if formula.root == '&':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.second.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.first})
                sec_quan = 'A'
            elif formula.root == '|':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.second.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.first})
                sec_quan = 'A'
            else:
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.second.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.first})
                sec_quan = 'A'
        else:
            if formula.root == '&':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.second.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.first})
                sec_quan = 'E'
            elif formula.root == '|':
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'),
                        {'x', 'R', 'Q'}),
                    {'x': var,
                     'R': formula.second.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.first})
                sec_quan = 'E'
            else:
                equiv_line = prover.add_instantiated_assumption(
                    new_equivalence, Schema(Formula.parse(
                        '(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'),
                        {'x','R','Q'}),
                    {'x': var,
                     'R': formula.second.predicate.substitute(
                         {var: Term('_')}), 'Q': formula.first})
                sec_quan = 'E'
        equiv_formula, sub_proof = \
            _pull_out_quantifications_from_right_across_binary_operator(sub_form)
        sub_equiv = equivalence_of(sub_form, equiv_formula)
        sub_equiv_line = prover.add_proof(sub_equiv, sub_proof)
        side1 = Formula(sec_quan, var, sub_form)
        side2 = Formula(sec_quan, var, equiv_formula)
        equivalence2 = equivalence_of(side1, side2)
        if sec_quan == 'E':
            cond = prover.add_instantiated_assumption(Formula(
                '->', sub_equiv, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': sub_form.substitute({var: Term('_')}),
                 'Q': equiv_formula.substitute({var: Term('_')})})
        else:
            cond = prover.add_instantiated_assumption(Formula(
                '->', sub_equiv, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': sub_form.substitute({var: Term('_')}),
                 'Q': equiv_formula.substitute({var: Term('_')})})
        mp = prover.add_mp(equivalence2, sub_equiv_line, cond)
        equivalence3 = equivalence_of(formula, side2)
        taut_formula = Formula('->', new_equivalence, Formula('->', equivalence2,
                                                      equivalence3))
        taut = prover.add_tautology(taut_formula)
        mp1 = prover.add_mp(Formula('->', equivalence2, equivalence3),
                            equiv_line, taut)
        prover.add_mp(equivalence3, mp, mp1)
        return side2, prover.qed()


def _pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    second = formula.second
    cur_form = formula.first
    left_quantifiers = []
    while is_quantifier(cur_form.root):
        if formula.root == '->':
            left_quantifiers.append((_opposite_quantifier(cur_form.root),
                                     cur_form.variable))
        else:
            left_quantifiers.append((cur_form.root, cur_form.variable))
        cur_form = cur_form.predicate
    inner1 = cur_form
    left_quantifiers = left_quantifiers[::-1]
    equiv1, proof1 = _pull_out_quantifications_from_left_across_binary_operator(formula)
    equivalence1 = equivalence_of(formula, equiv1)
    equivalence1_line = prover.add_proof(equivalence1, proof1)
    new_inner = Formula(formula.root, inner1, formula.second)
    equiv2, proof2 = _pull_out_quantifications_from_right_across_binary_operator(
        new_inner)
    equivalence2 = equivalence_of(new_inner, equiv2)
    equivalence2_line = prover.add_proof(equivalence2, proof2)
    for quan, var in left_quantifiers:
        if quan == 'A':
            prev_inner = new_inner
            prev_equiv2 = equiv2
            prev_equivalence2 = equivalence2
            new_inner = Formula(quan, var, new_inner)
            equiv2 = Formula(quan, var, equiv2)
            equivalence2 = equivalence_of(new_inner, equiv2)
            prev_equivalence2_line = equivalence2_line
            assump_line = prover.add_instantiated_assumption(
                Formula('->', prev_equivalence2, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': prev_inner.substitute({var: Term('_')}),
                 'Q': prev_equiv2.substitute({var: Term('_')})})
            equivalence2_line = prover.add_mp(
                equivalence2, prev_equivalence2_line, assump_line)
        else:
            prev_inner = new_inner
            prev_equiv2 = equiv2
            prev_equivalence2 = equivalence2
            new_inner = Formula(quan, var, new_inner)
            equiv2 = Formula(quan, var, equiv2)
            equivalence2 = equivalence_of(new_inner, equiv2)
            prev_equivalence2_line = equivalence2_line
            assump_line = prover.add_instantiated_assumption(
                Formula('->', prev_equivalence2, equivalence2),
                Schema(Formula.parse(
                    '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
                    {'x', 'y', 'R', 'Q'}),
                {'x': var, 'y': var,
                 'R': prev_inner.substitute({var: Term('_')}),
                 'Q': prev_equiv2.substitute({var: Term('_')})})
            equivalence2_line = prover.add_mp(
                equivalence2, prev_equivalence2_line, assump_line)
    equivalence3 = equivalence_of(formula, equiv2)
    taut = prover.add_tautology(Formula('->', equivalence1, Formula(
        '->', equivalence2, equivalence3)))
    mp1 = prover.add_mp(Formula('->', equivalence2, equivalence3),
                        equivalence1_line, taut)
    prover.add_mp(equivalence3, equivalence2_line, mp1)
    return equiv2, prover.qed()


def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    if is_variable(formula.root) or is_constant(formula.root) or \
            is_relation(formula.root) or is_equality(formula.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        new_formula = Formula('&', Formula('->', formula, formula),
                              Formula('->', formula, formula))
        prover.add_tautology(new_formula)
        return formula, prover.qed()
    elif is_unary(formula.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prenex_inner, inner_proof = \
            _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        equivalence1 = equivalence_of(formula.first, prenex_inner)
        equiv1_line = prover.add_proof(equivalence1, inner_proof)
        neg_prenex_inner = Formula('~', prenex_inner)
        equivalence2 = equivalence_of(formula, neg_prenex_inner)
        taut = prover.add_tautology(Formula('->', equivalence1, equivalence2))
        equiv2_line = prover.add_mp(equivalence2, equiv1_line, taut)
        prenex_formula, prenex_proof = \
            _pull_out_quantifications_across_negation(neg_prenex_inner)
        equivalence3 = equivalence_of(neg_prenex_inner, prenex_formula)
        equiv3_line = prover.add_proof(equivalence3, prenex_proof)
        equivalence4 = equivalence_of(formula, prenex_formula)
        new_taut = prover.add_tautology(Formula('->', equivalence2,
                                                Formula('->', equivalence3,
                                                        equivalence4)))
        mp1 = prover.add_mp(Formula('->', equivalence3, equivalence4),
                            equiv2_line, new_taut)
        prover.add_mp(equivalence4, equiv3_line, mp1)
        return prenex_formula, prover.qed()
    elif is_binary(formula.root):
        prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
        prenex_left, left_proof = \
            _to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        prenex_right, right_proof = \
            _to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        equivalence_left = equivalence_of(formula.first, prenex_left)
        equivalence_right = equivalence_of(formula.second, prenex_right)
        equiv_left = prover.add_proof(equivalence_left, left_proof)
        equiv_right = prover.add_proof(equivalence_right, right_proof)
        op_prenex = Formula(formula.root, prenex_left, prenex_right)
        equivalence1 = equivalence_of(formula, op_prenex)
        taut = prover.add_tautology(Formula(
            '->', equivalence_left, Formula('->', equivalence_right,
                                            equivalence1)))
        mp = prover.add_mp(Formula('->', equivalence_right, equivalence1),
                           equiv_left, taut)
        equiv1_line = prover.add_mp(equivalence1, equiv_right, mp)
        prenex_formula, prenex_proof = \
            _pull_out_quantifications_across_binary_operator(op_prenex)
        equivalence2 = equivalence_of(op_prenex, prenex_formula)
        equiv2_line = prover.add_proof(equivalence2, prenex_proof)
        equivalence3 = equivalence_of(formula, prenex_formula)
        new_taut = prover.add_tautology(Formula('->', equivalence1,
                                                Formula('->', equivalence2,
                                                        equivalence3)))
        mp1 = prover.add_mp(Formula('->', equivalence2, equivalence3),
                            equiv1_line, new_taut)
        prover.add_mp(equivalence3, equiv2_line, mp1)
        return prenex_formula, prover.qed()
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    var = formula.variable
    prenex_pred, pred_proof = \
        _to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
    equivalence_pred = equivalence_of(formula.predicate, prenex_pred)
    equiv_pred = prover.add_proof(equivalence_pred, pred_proof)
    prenex_formula = Formula(formula.root, formula.variable, prenex_pred)
    equivalence = equivalence_of(formula, prenex_formula)
    if formula.root == 'A':
        imp = prover.add_instantiated_assumption(Formula(
            '->', equivalence_pred, equivalence),
            Schema(Formula.parse(
                '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
            {'x': var, 'y': var,
             'R': formula.predicate.substitute({var: Term('_')}),
             'Q': prenex_pred.substitute({var: Term('_')})})
    else:
        imp = prover.add_instantiated_assumption(Formula(
            '->', equivalence_pred, equivalence),
            Schema(Formula.parse(
                '(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
            {'x': var, 'y': var,
             'R': formula.predicate.substitute({var: Term('_')}),
             'Q': prenex_pred.substitute({var: Term('_')})})
    prover.add_mp(equivalence, equiv_pred, imp)
    return prenex_formula, prover.qed()


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.10
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    unique_formula, unique_proof = _uniquely_rename_quantified_variables(formula)
    unique_equivalence = equivalence_of(formula, unique_formula)
    unique_line = prover.add_proof(unique_equivalence, unique_proof)
    prenex_unique, prenex_proof = \
        _to_prenex_normal_form_from_uniquely_named_variables(unique_formula)
    prenex_equivalence = equivalence_of(unique_formula, prenex_unique)
    prenex_equiv_line = prover.add_proof(prenex_equivalence, prenex_proof)
    equivalence = equivalence_of(formula, prenex_unique)
    taut = prover.add_tautology(Formula('->', unique_equivalence,
                                        Formula('->', prenex_equivalence,
                                                equivalence)))
    mp1 = prover.add_mp(Formula('->', prenex_equivalence, equivalence),
                        unique_line, taut)
    prover.add_mp(equivalence, prenex_equiv_line, mp1)
    return prenex_unique, prover.qed()
