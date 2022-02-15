# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen, \
                        memoized_parameterless_method

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """
    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((string[0] >= '0' and string[0] <= '9') or \
              (string[0] >= 'a' and string[0] <= 'd')) and \
             string.isalnum()) or string == '_'

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'u' and string[0] <= 'z' and string.isalnum()

@lru_cache(maxsize=100) # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= 'f' and string[0] <= 't' and string.isalnum()

@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        else:
            ret_str = self.root + '('
            length = len(self.arguments)
            for idx, arg in enumerate(self.arguments):
                ret_str += str(arg)
                if idx != length - 1:
                    ret_str += ','
            ret_str += ')'
            return ret_str

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1
        if is_variable(string[0]) or is_constant(string[0]):
            if string[0] == '_':
                return Term('_'), string[1:]
            new_root = string[0]
            for idx, char in enumerate(string[1:]):
                if char.isalnum():
                    new_root += char
                else:
                    return Term(new_root), string[idx + 1:]
            return Term(string), ""
        if is_function(string[0]):
            new_root = string[0]
            for idx, char in enumerate(string[1:]):
                if char.isalnum():
                    new_root += char
                else:
                    break
            args = []
            cur_idx = len(new_root) + 1
            cur_term, cur_suffix = Term._parse_prefix(string[cur_idx:])
            args.append(cur_term)
            while cur_suffix[0] != ')':
                cur_term, cur_suffix = Term._parse_prefix(cur_suffix[1:])
                args.append(cur_term)
            return Term(new_root, args), cur_suffix[1:]

    @staticmethod
    def parse_prefix_public(string):
        """
        A public version of _parse_prefix
        """
        return Term._parse_prefix(string)

    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2
        ret_term, suffix = Term._parse_prefix(string)
        return ret_term

    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5.1
        term_constants = set()
        if is_variable(self.root):
            return term_constants
        if is_constant(self.root):
            term_constants.add(self.root)
            return term_constants
        for arg in self.arguments:
            term_constants = term_constants.union(arg.constants())
        return term_constants


    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5.2
        term_variables = set()
        if is_variable(self.root):
            term_variables.add(self.root)
            return term_variables
        if is_constant(self.root):
            return term_variables
        for arg in self.arguments:
            term_variables = term_variables.union(arg.variables())
        return term_variables

    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5.3
        term_functions = set()
        if is_constant(self.root) or is_variable(self.root):
            return term_functions
        term_functions.add((self.root, len(self.arguments)))
        for arg in self.arguments:
            term_functions = term_functions.union(arg.functions())
        return term_functions

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1
        if is_constant(self.root) or is_variable(self.root):
            if self.root in substitution_map:
                for var in substitution_map[self.root].variables():
                    if var in forbidden_variables:
                        raise ForbiddenVariableError(var)
                return substitution_map[self.root]
            return self
        args = []
        for arg in self.arguments:
            args.append(arg.substitute(substitution_map, forbidden_variables))
        return Term(self.root, args)


@lru_cache(maxsize=100) # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == '='

@lru_cache(maxsize=100) # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= 'F' and string[0] <= 'T' and string.isalnum()

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == '&' or string == '|' or string == '->'

@lru_cache(maxsize=100) # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == 'A' or string == 'E'

@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the root, if the
                root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate           
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        if is_equality(self.root):
            return str(self.arguments[0]) + '=' + str(self.arguments[1])
        if is_relation(self.root):
            ret_str = self.root + '('
            length = len(self.arguments)
            for idx, arg in enumerate(self.arguments):
                ret_str += str(arg)
                if idx != length - 1:
                    ret_str += ','
            ret_str += ')'
            return ret_str
        if is_unary(self.root):
            return self.root + str(self.first)
        if is_binary(self.root):
            return '(' + str(self.first) + self.root + str(self.second) + ')'
        return self.root + str(self.variable) + '[' + str(self.predicate) + ']'

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1
        if is_unary(string[0]):
            new_formula, suffix = Formula._parse_prefix(string[1:])
            return Formula('~', new_formula), suffix
        if string[0] == '(':
            new_formula1, suffix1 = Formula._parse_prefix(string[1:])
            operator = suffix1[0]
            if suffix1[0] == '-':
                operator += suffix1[1]
                suffix1 = suffix1[2:]
            else:
                suffix1 = suffix1[1:]
            new_formula2, suffix2 = Formula._parse_prefix(suffix1)
            return Formula(operator, new_formula1, new_formula2), suffix2[1:]
        if is_relation(string[0]):
            new_root = string[0]
            for idx, char in enumerate(string[1:]):
                if char.isalnum():
                    new_root += char
                else:
                    break
            args = []
            cur_idx = len(new_root) + 1
            cur_suffix = string[cur_idx:]
            while cur_suffix[0] != ')':
                idx = 0
                if cur_suffix[0] == ',':
                    idx = 1
                cur_term, cur_suffix = Term.parse_prefix_public(cur_suffix[idx:])
                args.append(cur_term)
            return Formula(new_root, args), cur_suffix[1:]
        if is_quantifier(string[0]):
            new_quantifier = string[0]
            new_variable = string[1]
            new_idx = 2
            while string[new_idx] != '[':
                new_variable += string[new_idx]
                new_idx += 1
            new_idx += 1
            new_predicate, suffix = Formula._parse_prefix(string[new_idx:])
            return Formula(new_quantifier, new_variable, new_predicate), suffix[1:]
        term1, suffix1 = Term.parse_prefix_public(string)
        op = suffix1[0]
        term2, suffix2 = Term.parse_prefix_public(suffix1[1:])
        return Formula(op, [term1, term2]), suffix2

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        new_formula, suffix = Formula._parse_prefix(string)
        return new_formula

    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6.1
        formula_constants = set()
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                formula_constants = formula_constants.union(arg.constants())
            return formula_constants
        if is_unary(self.root):
            return self.first.constants()
        if is_binary(self.root):
            return self.first.constants().union(self.second.constants())
        return self.predicate.constants()

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6.2
        formula_variables = set()
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                formula_variables = formula_variables.union(arg.variables())
            return formula_variables
        if is_unary(self.root):
            return self.first.variables()
        if is_binary(self.root):
            return self.first.variables().union(self.second.variables())
        return self.predicate.variables().union({self.variable})


    @memoized_parameterless_method
    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6.3
        formula_free_variables = set()
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                formula_free_variables = formula_free_variables.union(arg.variables())
            return formula_free_variables
        if is_unary(self.root):
            return self.first.free_variables()
        if is_binary(self.root):
            return self.first.free_variables().union(self.second.free_variables())
        return self.predicate.free_variables().difference({self.variable})

    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6.4
        formula_functions = set()
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                formula_functions = formula_functions.union(arg.functions())
            return formula_functions
        if is_unary(self.root):
            return self.first.functions()
        if is_binary(self.root):
            return self.first.functions().union(self.second.functions())
        return self.predicate.functions()

    @memoized_parameterless_method
    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        formula_relations = set()
        if is_equality(self.root):
            return formula_relations
        if is_relation(self.root):
            return {(self.root, len(self.arguments))}
        if is_unary(self.root):
            return self.first.relations()
        if is_binary(self.root):
            return self.first.relations().union(self.second.relations())
        return self.predicate.relations()

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2
        if is_unary(self.root):
            return Formula(self.root,
                           self.first.substitute(substitution_map,
                                                 forbidden_variables))
        if is_binary(self.root):
            return Formula(self.root,
                           self.first.substitute(substitution_map,
                                                 forbidden_variables),
                           self.second.substitute(substitution_map,
                                                  forbidden_variables))
        if is_equality(self.root) or is_relation(self.root):
            args = []
            for arg in self.arguments:
                args.append(arg.substitute(substitution_map,
                                           forbidden_variables))
            return Formula(self.root, args)
        forbidden_variables = set(forbidden_variables).union({self.variable})
        if self.variable in substitution_map:
            substitution_map = dict(substitution_map)
            del substitution_map[self.variable]
        return Formula(self.root, self.variable,
                       self.predicate.substitute(substitution_map,
                                                 forbidden_variables))

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each atomic
            propositional formula to the subformula for which it was
            substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(x=7->~Q(y)))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(z2->~z3)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(z5->~z6)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8
        return self._propositional_skeleton_helper({})

    def _propositional_skeleton_helper(self, prop_to_pred):
        """
        A helper for propositional_skeleton
        Args:
            prop_to_pred: maps the propositional variables to the
            predicate sub formulas

        Returns:
            Same as propositional_skeleton
        """
        if is_unary(self.root):
            first_tuple = self.first._propositional_skeleton_helper(prop_to_pred)
            return PropositionalFormula(self.root, first_tuple[0]), first_tuple[1]
        if is_binary(self.root):
            first_tuple = self.first._propositional_skeleton_helper(prop_to_pred)
            second_tuple = self.second._propositional_skeleton_helper(first_tuple[1])
            return PropositionalFormula(self.root, first_tuple[0], second_tuple[0]), second_tuple[1]
        for prop, pred in prop_to_pred.items():
            if self == pred:
                return PropositionalFormula(prop), prop_to_pred
        new_pred = next(fresh_variable_name_generator)
        prop_to_pred[new_pred] = self
        return PropositionalFormula(new_pred), prop_to_pred


    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each atomic propositional subformula
                of the given skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each atomic propositional subformula with
            the formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(z2->~z3))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(x=7->~Q(y)))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
        if is_propositional_variable(skeleton.root):
            return substitution_map[skeleton.root]
        if is_unary(skeleton.root):
            return Formula(skeleton.root, Formula.from_propositional_skeleton(
                skeleton.first, substitution_map))
        return Formula(skeleton.root, Formula.from_propositional_skeleton(
            skeleton.first, substitution_map),
                       Formula.from_propositional_skeleton(
                           skeleton.second, substitution_map))
