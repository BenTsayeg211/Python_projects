import sys
import os

IN_SUFFIX = ".jack"
OUT_SUFFIX = ".vm"

KEYWORDS = {'class', 'constructor', 'function', 'method', 'field', 'static',
            'var', 'int', 'char', 'boolean', 'void', 'true', 'false', 'null',
            'this', 'let', 'do', 'if', 'else', 'while', 'return'}
SYMBOLS = {'{', '}', '[', ']', '(', ')', '.', ',', ';', '+', '-', '*', '/', '&'
           , '|', '<', '>', '=', '~'}
SEPARATORS = {' ', '\n', '\t', '\r'}
OP = {'+', '-', '*', '/', '&', '|', '<', '>', '='}
UNARY_OP = {'-', '~'}
KW_CONST = {'true', 'false', 'null', 'this'}


class JackTokenizer:
    """
    This class represents a Jack tokenizer that separates a file's tokens
    """
    def __init__(self, file):
        """
        Creates a new tokenizer for the given input file
        :param file: The given input file
        """
        self.__file = file
        self.__pos = 0
        self.__cur_token = ""
        self.__type = ""

    def has_more_tokens(self):
        """
        Checks if there are more tokens in the file
        :return: True if there are more tokens, False otherwise
        """
        cur_char = self.__file.read(1)
        while cur_char in SEPARATORS or cur_char == '/':
            if cur_char == '/':
                next_char = self.__file.read(1)
                if next_char == '/':
                    while cur_char != "\n":
                        cur_char = self.__file.read(1)
                elif next_char == '*':
                    cur_char = self.__file.read(1)
                    prev_char = ""
                    while not (prev_char == "*" and cur_char == "/"):
                        prev_char = cur_char
                        cur_char = self.__file.read(1)
                else:
                    self.__file.seek(self.__pos)
                    return True
            cur_char = self.__file.read(1)
        self.__file.seek(self.__pos)
        if cur_char:
            return True
        return False

    def __handle_comment(self):
        """
        Handles a comment in the input file
        :return: None
        """
        cur_char = self.__file.read(1)
        self.__pos += 1
        if cur_char == "/":  # line comment
            while cur_char != "\n":
                cur_char = self.__file.read(1)
                self.__pos += 1
            self.__file.seek(self.__pos)
            next_char = self.__file.read()
            if next_char == "\n":
                self.__pos += 1
            else:
                self.__file.seek(self.__pos)
        else:  # API or block comment
            cur_char = self.__file.read(1)
            self.__pos += 1
            prev_char = ""
            while not(prev_char == "*" and cur_char == "/"):
                if cur_char == "\n":
                    self.__pos += 1
                    next_char = self.__file.read(1)
                    if next_char == "\n":
                        self.__pos += 1
                    else:
                        self.__file.seek(self.__pos)
                else:
                    self.__pos += 1
                prev_char = cur_char
                cur_char = self.__file.read(1)

    def advance(self):
        """
        Advances to the next token
        :return: None
        """
        token = ""
        cur_char = " "
        while cur_char in SEPARATORS:  # removing all separators
            cur_char = self.__file.read(1)
            if cur_char == "\n":
                self.__pos += 1
                self.__file.seek(self.__pos)
                next_char = self.__file.read()
                if next_char == "\n":
                    self.__pos += 1
                else:
                    self.__file.seek(self.__pos)
            elif cur_char == '/':
                self.__pos += 1
                next_char = self.__file.read(1)
                self.__file.seek(self.__pos)
                if next_char == "/" or next_char == "*":
                    self.__handle_comment()
                    cur_char = " "
            else:
                self.__pos += 1

        if cur_char in SYMBOLS:  # token is a symbol
            self.__cur_token = cur_char
            return

        if ord(cur_char) == 34:  # token is a string constant
            token += cur_char
            cur_char = self.__file.read(1)
            self.__pos += 1
            while ord(cur_char) != 34:
                token += cur_char
                cur_char = self.__file.read(1)
                self.__pos += 1
            token += cur_char
            self.__cur_token = token
            return

        while (cur_char not in SYMBOLS) and (cur_char not in SEPARATORS):  # otherwise
            token += cur_char
            cur_char = self.__file.read(1)
            self.__pos += 1

        self.__pos -= 1
        self.__file.seek(self.__pos)
        self.__cur_token = token

    def keyword(self):
        """
        Returns the current keyword token
        :return: The current keyword token
        """
        return self.__cur_token

    def symbol(self):
        """
        Returns the current symbol token
        :return: The current symbol token
        """
        return self.__cur_token

    def identifier(self):
        """
        Returns the current identifier token
        :return: The current identifier token
        """
        return self.__cur_token

    def string_val(self):
        """
        Returns the current stringConstant token
        :return: The current stringConstant token
        """
        return self.__cur_token[1:-1]

    def int_val(self):
        """
        Returns the current integerConstant token
        :return: The current integerConstant token
        """
        return int(self.__cur_token)

    def token_type(self):
        """
        Returns the current token type
        :return: The current token type
        """
        if self.__cur_token in KEYWORDS:
            return "keyword"
        if self.__cur_token in SYMBOLS:
            return "symbol"
        if self.__cur_token.isdigit():
            return "integerConstant"
        if ord(self.__cur_token[0]) == 34:
            return "stringConstant"
        return "identifier"


class SymbolTable:
    """
    This class represents a symbol table for a Jack class or subroutine
    """
    def __init__(self):
        """
        Creates a new empty symbol table
        """
        self.__table = {}
        self.__statics = 0
        self.__fields = 0
        self.__args = 0
        self.__variables = 0

    def start_subroutine(self):
        """
        Starts a new subroutine scope which resets the table
        :return: None
        """
        self.__table.clear()
        self.__args = 0
        self.__variables = 0

    def define(self, name, kind, sym_type):
        """
        Adds a new identifier to the table and assigns it a running index
        :param name: The identifier's name
        :param kind: The identifier's kind
        :param sym_type: The identifier's type
        :return: None
        """
        cur_index = ""
        if kind == "field":
            cur_index = self.__fields
            self.__fields += 1
        elif kind == "static":
            cur_index = self.__statics
            self.__statics += 1
        elif kind == "argument":
            cur_index = self.__args
            self.__args += 1
        else:
            cur_index = self.__variables
            self.__variables += 1
        self.__table[name] = [kind, sym_type, cur_index]

    def var_count(self, kind):
        """
        Returns the number of variables of the given kind defined in the table
        :param kind: The kind of the variable
        :return: The number of this kind of variables defined in the table
        """
        if kind == "field":
            return self.__fields
        elif kind == "static":
            return self.__statics
        elif kind == "argument":
            return self.__args
        return self.__variables

    def kind_of(self, name):
        """
        :param name: The name of an identifier
        :return: The kind of the named identifier. None if not defined in scope
        """
        if name in self.__table:
            return self.__table[name][0]
        return None

    def type_of(self, name):
        """
        :param name: The name of an identifier
        :return: The type of the named identifier. None if not defined in scope
        """
        if name in self.__table:
            return self.__table[name][1]
        return None

    def index_of(self, name):
        """
        :param name: The name of an identifier
        :return: The index of the named identifier. None if not defined in scope
        """
        if name in self.__table:
            return self.__table[name][2]
        return None


class VMWriter:
    """
    This class represents a VM code writer
    """
    def __init__(self, output_file):
        """
        Creates a new output .vm file and prepares it for writing
        """
        self.__out_file = output_file

    def write_push(self, segment, index):
        """
        Writes a VM push command
        :param segment: The segments to push from
        :param index: The index in the segment
        :return: None
        """
        self.__out_file.write("push " + segment + " " + str(index) + "\n")

    def write_pop(self, segment, index):
        """
        Writes a VM pop command
        :param segment: The segments to pop to
        :param index: The index in the segment
        :return: None
        """
        self.__out_file.write("pop " + segment + " " + str(index) + "\n")

    def write_arithmetic(self, command):
        """
        Writes a VM arithmetic-logical command
        :param command: The command to write
        :return: None
        """
        self.__out_file.write(command + "\n")

    def write_label(self, label):
        """
        Write a VM label command
        :param label: The label to write
        :return: None
        """
        self.__out_file.write("label " + label + "\n")

    def write_goto(self, label):
        """
        Writes a VM goto command
        :param label: The label to go to
        :return: None
        """
        self.__out_file.write("goto " + label + "\n")

    def write_if(self, label):
        """
        Writes a VM if-goto command
        :param label: The label to go to
        :return: None
        """
        self.__out_file.write("if-goto " + label + "\n")

    def write_call(self, name, args_num):
        """
        Writes a VM call command
        :param name: The name of the function to call to
        :param args_num: The number of the function's arguments
        :return: None
        """
        self.__out_file.write("call " + name + " " + str(args_num) + "\n")

    def write_function(self, name, locals_num):
        """
        Writes a VM function command
        :param name: The name of the function
        :param locals_num: The number of the function's local variables
        :return: None
        """
        self.__out_file.write("function " + name + " " + str(locals_num) + "\n")

    def write_return(self):
        """
        Writes a VM return command
        :return: None
        """
        self.__out_file.write("return\n")

    def close(self):
        """
        Closes the output file
        :return: None
        """
        self.__out_file.close()


class CompilationEngine:
    """
    Represents a compilation engine for a given tokenizer and VM writer file
    """
    def __init__(self, tokenizer, vm_writer):
        """
        Creates a new compilation engine
        :param tokenizer: The given tokenizer
        :param vm_writer: The given VM writer
        """
        self.__tokenizer = tokenizer
        self.__vm_writer = vm_writer
        self.__class_table = SymbolTable()
        self.__subroutine_table = SymbolTable()
        self.__class_name = ""
        self.__cur_subroutine = ""
        self.__if_label = 0
        self.__while_label = 0

    def compile_class(self):
        """
        Compiles a class
        :return: None
        """
        # class className {
        self.__tokenizer.advance()
        self.__class_name = self.__tokenizer.identifier()
        self.__tokenizer.advance()

        # class var decs
        self.__tokenizer.advance()
        cur_token = self.__tokenizer.keyword()
        while cur_token == "static" or cur_token == "field":
            self.compile_class_var_dec()
            cur_token = self.__tokenizer.keyword()

        # subroutine decs }
        cur_token = self.__tokenizer.keyword()
        while cur_token == "function" or cur_token == "method" or cur_token == "constructor":
            self.compile_subroutine_dec()
            cur_token = self.__tokenizer.keyword()

        self.__vm_writer.close()

    def compile_class_var_dec(self):
        """
        Compiles a class variable declaration
        :return: None
        """
        # ('static' | 'field') type varName
        cur_kind = self.__tokenizer.keyword()
        self.__tokenizer.advance()
        cur_type = ""
        if self.__tokenizer.token_type() == "identifier":
            cur_type = self.__tokenizer.identifier()
        else:
            cur_type = self.__tokenizer.keyword()
        self.__tokenizer.advance()
        cur_iden = self.__tokenizer.identifier()
        self.__class_table.define(cur_iden, cur_kind, cur_type)

        # (',' varName)* ';'
        self.__tokenizer.advance()
        cur_token = self.__tokenizer.symbol()
        while cur_token == ",":
            self.__tokenizer.advance()
            cur_iden = self.__tokenizer.identifier()
            self.__class_table.define(cur_iden, cur_kind, cur_type)
            self.__tokenizer.advance()
            cur_token = self.__tokenizer.symbol()
        self.__tokenizer.advance()

    def compile_subroutine_dec(self):
        """
        Compiles a subroutine declaration
        :return: None
        """
        self.__subroutine_table.start_subroutine()

        subroutine_type = self.__tokenizer.identifier()

        # ('constructor'|'method'|'function') ('void' | type) subroutineName'('
        if self.__tokenizer.identifier() == "method":
            self.__subroutine_table.define("this", "argument", self.__class_name)
        self.__tokenizer.advance()
        self.__tokenizer.advance()
        self.__cur_subroutine = self.__tokenizer.identifier()
        self.__tokenizer.advance()

        # parameterList
        self.__tokenizer.advance()
        self.compile_parameter_list()

        # ')' subroutineBody
        self.__tokenizer.advance()
        self.compile_subroutine_body(subroutine_type)

    def compile_parameter_list(self):
        """
        Compiles a parameter list
        :return: None
        """
        if self.__tokenizer.token_type() != "symbol":
            # (type varName)
            cur_type = ""
            if self.__tokenizer.token_type() == "identifier":
                cur_type = self.__tokenizer.identifier()
            else:
                cur_type = self.__tokenizer.keyword()
            self.__tokenizer.advance()
            cur_iden = self.__tokenizer.identifier()
            self.__subroutine_table.define(cur_iden, "argument", cur_type)
            self.__tokenizer.advance()

            # (',' type varName)*
            cur_token = self.__tokenizer.symbol()
            while cur_token != ")":
                self.__tokenizer.advance()
                if self.__tokenizer.token_type() == "identifier":
                    cur_type = self.__tokenizer.identifier()
                else:
                    cur_type = self.__tokenizer.keyword()
                self.__tokenizer.advance()
                cur_iden = self.__tokenizer.identifier()
                self.__subroutine_table.define(cur_iden, "argument", cur_type)
                self.__tokenizer.advance()
                cur_token = self.__tokenizer.symbol()

    def compile_subroutine_body(self, sub_type):
        """
        Compiles a subroutine body
        :param sub_type: The type of the subroutine
        :return: None
        """
        # '{'
        self.__tokenizer.advance()

        # varDec*
        if self.__tokenizer.token_type() == "keyword":
            while self.__tokenizer.keyword() == "var":
                self.compile_var_dec()

        self.__vm_writer.write_function(
            self.__class_name + "." + self.__cur_subroutine,
            self.__subroutine_table.var_count("variable"))

        if sub_type == "method":
            self.__vm_writer.write_push("argument", 0)
            self.__vm_writer.write_pop("pointer", 0)

        elif sub_type == "constructor":
            self.__vm_writer.write_push("constant", self.__class_table.var_count("field"))
            self.__vm_writer.write_call("Memory.alloc", 1)
            self.__vm_writer.write_pop("pointer", 0)

        # statements '}'
        self.compile_statements()

        self.__tokenizer.advance()

    def compile_var_dec(self):
        """
        Compiles a variable declaration
        :return: None
        """
        # 'var' type varName
        self.__tokenizer.advance()
        cur_type = ""
        if self.__tokenizer.token_type() == "identifier":
            cur_type = self.__tokenizer.identifier()
        else:
            cur_type = self.__tokenizer.keyword()
        self.__tokenizer.advance()
        cur_iden = self.__tokenizer.identifier()
        self.__subroutine_table.define(cur_iden, "variable", cur_type)
        self.__tokenizer.advance()

        # (',' varName)*
        while self.__tokenizer.symbol() == ",":
            self.__tokenizer.advance()
            cur_iden = self.__tokenizer.identifier()
            self.__subroutine_table.define(cur_iden, "variable", cur_type)
            self.__tokenizer.advance()

        # ';'
        self.__tokenizer.advance()

    def compile_statements(self):
        """
        Compiles statements
        :return: None
        """
        # statement*
        while self.__tokenizer.token_type() == "keyword":
            cur_token = self.__tokenizer.keyword()
            if cur_token == "let":
                self.compile_let()
            elif cur_token == "if":
                self.compile_if()
            elif cur_token == "while":
                self.compile_while()
            elif cur_token == "do":
                self.compile_do()
            else:
                self.compile_return()

    def compile_let(self):
        """
        Compiles a let statement
        :return: None
        """
        # 'let' varName
        self.__tokenizer.advance()
        var_name = self.__tokenizer.identifier()
        self.__tokenizer.advance()

        in_arr = False

        # ('[' expression ']')?
        if self.__tokenizer.symbol() == "[":
            in_arr = True
            self.__push_identifier(var_name)
            self.__tokenizer.advance()
            self.compile_expression()
            self.__vm_writer.write_arithmetic("add")
            self.__tokenizer.advance()

        # '=' expression ';'
        self.__tokenizer.advance()
        self.compile_expression()
        self.__tokenizer.advance()

        if in_arr:
            self.__vm_writer.write_pop("temp", 0)
            self.__vm_writer.write_pop("pointer", 1)
            self.__vm_writer.write_push("temp", 0)
            self.__vm_writer.write_pop("that", 0)

        else:
            self.__pop_identifier(var_name)

    def compile_if(self):
        """
        Compiles an if statement
        :return: None
        """
        l1 = "IF_END&" + str(self.__if_label)
        l2 = "ELSE_START&" + str(self.__if_label)
        self.__if_label += 1

        # 'if' '(' expression ')' '{' statements '}'
        self.__tokenizer.advance()
        self.__tokenizer.advance()
        self.compile_expression()
        self.__tokenizer.advance()
        self.__tokenizer.advance()
        self.__vm_writer.write_arithmetic("not")
        self.__vm_writer.write_if(l1)
        self.compile_statements()
        self.__tokenizer.advance()

        is_else = False

        # ('else' '{' statements '}')?
        if self.__tokenizer.token_type() == "keyword":
            if self.__tokenizer.keyword() == "else":
                is_else = True
                self.__tokenizer.advance()
                self.__tokenizer.advance()

        if is_else:
            self.__vm_writer.write_goto(l2)
            self.__vm_writer.write_label(l1)
            self.compile_statements()
            self.__tokenizer.advance()
            self.__vm_writer.write_label(l2)
        else:
            self.__vm_writer.write_label(l1)

    def compile_while(self):
        """
        Compiles a while statement
        :return: None
        """
        l1 = "WHILE_START&" + str(self.__while_label)
        l2 = "WHILE_END&" + str(self.__while_label)
        self.__while_label += 1

        # 'while' '(' expression ')' '{' statements '}'
        self.__tokenizer.advance()
        self.__tokenizer.advance()
        self.__vm_writer.write_label(l1)
        self.compile_expression()
        self.__vm_writer.write_arithmetic("not")
        self.__vm_writer.write_if(l2)
        self.__tokenizer.advance()
        self.__tokenizer.advance()
        self.compile_statements()
        self.__vm_writer.write_goto(l1)
        self.__vm_writer.write_label(l2)
        self.__tokenizer.advance()

    def compile_do(self):
        """
        Compiles a do statement
        :return: None
        """
        # 'do' subroutineCall ';'
        self.__tokenizer.advance()
        self.compile_term()
        self.__tokenizer.advance()
        self.__vm_writer.write_pop("temp", 0)

    def compile_return(self):
        """
        Compiles a return statement
        :return: None
        """
        is_void = True

        # 'return' expression? ';'
        self.__tokenizer.advance()
        if self.__tokenizer.token_type() != "symbol" or self.__tokenizer.symbol() != ';':
            self.compile_expression()
            is_void = False
        if is_void:
            self.__vm_writer.write_push("constant", 0)
        self.__vm_writer.write_return()
        self.__tokenizer.advance()

    def compile_expression(self):
        """
        Compiles an expression
        :return: None
        """
        # term
        self.compile_term()

        # (op term)*
        while self.__tokenizer.token_type() == "symbol" and self.__tokenizer.symbol() in OP:
            op = self.__tokenizer.symbol()
            self.__tokenizer.advance()
            self.compile_term()
            self.__write_operator(op)

    def compile_term(self):
        """
        Compiles a term
        :return: None
        """
        token_type = self.__tokenizer.token_type()
        if token_type == "integerConstant":  # integerConstant
            self.__vm_writer.write_push("constant", self.__tokenizer.int_val())
            self.__tokenizer.advance()
        elif token_type == "stringConstant":  # stringConstant
            self.__vm_writer.write_push("constant", len(self.__tokenizer.string_val()))
            self.__vm_writer.write_call("String.new", 1)
            for char in self.__tokenizer.string_val():
                self.__vm_writer.write_push("constant", ord(char))
                self.__vm_writer.write_call("String.appendChar", 2)
            self.__tokenizer.advance()
        elif (token_type == "keyword") and (self.__tokenizer.keyword() in KW_CONST):  # keywordConstant
            kw = self.__tokenizer.keyword()
            if kw == "true":
                self.__vm_writer.write_push("constant", 1)
                self.__vm_writer.write_arithmetic("neg")
            elif kw == "false" or kw == "null":
                self.__vm_writer.write_push("constant", 0)
            elif kw == "this":
                self.__vm_writer.write_push("pointer", 0)
            self.__tokenizer.advance()
        elif token_type == "symbol":
            if self.__tokenizer.symbol() in UNARY_OP:  # unaryOp term
                un_op = self.__tokenizer.symbol()
                self.__tokenizer.advance()
                self.compile_term()
                self.__write_unary_operator(un_op)
            elif self.__tokenizer.symbol() == '(':  # '(' expression ')'
                self.__tokenizer.advance()
                self.compile_expression()
                self.__tokenizer.advance()
        else:  # varName / subroutineName / className
            first_iden = self.__tokenizer.identifier()
            self.__tokenizer.advance()
            if self.__tokenizer.symbol() == '[':  # '['expression']'
                self.__tokenizer.advance()
                self.__push_identifier(first_iden)
                self.compile_expression()
                self.__vm_writer.write_arithmetic("add")
                self.__vm_writer.write_pop("pointer", 1)
                self.__vm_writer.write_push("that", 0)
                self.__tokenizer.advance()
            elif self.__tokenizer.symbol() == '(':  # '(' expressionList ')'
                self.__tokenizer.advance()
                self.__vm_writer.write_push("pointer", 0)
                args_num = self.compile_expression_list()
                self.__vm_writer.write_call(self.__class_name + "." + first_iden, args_num + 1)
                self.__tokenizer.advance()
            elif self.__tokenizer.symbol() == '.':  # '.' subroutineName '(' expressionList ')'
                self.__tokenizer.advance()
                second_iden = self.__tokenizer.identifier()
                self.__tokenizer.advance()
                self.__tokenizer.advance()
                if self.__push_identifier(first_iden):  # varName
                    args_num = self.compile_expression_list()
                    if self.__subroutine_table.kind_of(first_iden) is not None:
                        self.__vm_writer.write_call(
                            self.__subroutine_table.type_of(
                                first_iden) + "." + second_iden, args_num + 1)
                    else:
                        self.__vm_writer.write_call(
                            self.__class_table.type_of(
                                first_iden) + "." + second_iden, args_num + 1)
                else:  # className
                    args_num = self.compile_expression_list()
                    self.__vm_writer.write_call(first_iden + "." + second_iden, args_num)
                self.__tokenizer.advance()
            else:  # varName
                self.__push_identifier(first_iden)

    def compile_expression_list(self):
        """
        Compiles an expression list
        :return: The number of expressions compiled
        """
        expressions_num = 0

        # (expression (',' expression)* )?
        if not(self.__tokenizer.token_type() == "symbol" and self.__tokenizer.symbol() == ')'):
            self.compile_expression()
            expressions_num += 1
        while self.__tokenizer.symbol() != ')':
            self.__tokenizer.advance()
            self.compile_expression()
            expressions_num += 1
        return expressions_num

    def __push_identifier(self, var_name):
        """
        Writes a VM push command for the given identifier name
        :param var_name: The identifier name
        :return: True if its a subroutine or class variable. Else otherwise
        """
        if self.__subroutine_table.kind_of(var_name) is not None:
            if self.__subroutine_table.kind_of(var_name) == "argument":
                self.__vm_writer.write_push("argument", self.__subroutine_table.index_of(var_name))
            else:
                self.__vm_writer.write_push("local", self.__subroutine_table.index_of(var_name))
            return True
        elif self.__class_table.kind_of(var_name) is not None:
            if self.__class_table.kind_of(var_name) == "field":
                self.__vm_writer.write_push("this", self.__class_table.index_of(var_name))
            else:
                self.__vm_writer.write_push("static", self.__class_table.index_of(var_name))
            return True
        else:
            return False

    def __pop_identifier(self, var_name):
        """
        Writes a VM pop command for the given identifier name
        :param var_name: The given identifier name
        :return: True if its a subroutine or class variable. Else otherwise
        """
        if self.__subroutine_table.kind_of(var_name) is not None:
            if self.__subroutine_table.kind_of(var_name) == "argument":
                self.__vm_writer.write_pop("argument", self.__subroutine_table.index_of(var_name))
            else:
                self.__vm_writer.write_pop("local", self.__subroutine_table.index_of(var_name))
        elif self.__class_table.kind_of(var_name) is not None:
            if self.__class_table.kind_of(var_name) == "field":
                self.__vm_writer.write_pop("this", self.__class_table.index_of(var_name))
            else:
                self.__vm_writer.write_pop("static", self.__class_table.index_of(var_name))
        else:
            return False

    def __write_operator(self, op):
        """
        Writes a given operator in VM code
        :param op: The given operator
        :return: None
        """
        if op == "+":
            self.__vm_writer.write_arithmetic("add")
        elif op == "-":
            self.__vm_writer.write_arithmetic("sub")
        elif op == "*":
            self.__vm_writer.write_call("Math.multiply", 2)
        elif op == "/":
            self.__vm_writer.write_call("Math.divide", 2)
        elif op == "&":
            self.__vm_writer.write_arithmetic("and")
        elif op == "|":
            self.__vm_writer.write_arithmetic("or")
        elif op == "<":
            self.__vm_writer.write_arithmetic("lt")
        elif op == ">":
            self.__vm_writer.write_arithmetic("gt")
        else:
            self.__vm_writer.write_arithmetic("eq")

    def __write_unary_operator(self, un_op):
        """
        Writes a given unary operator in VM code
        :param un_op: The given unary operator
        :return: None
        """
        if un_op == "-":
            self.__vm_writer.write_arithmetic("neg")
        else:
            self.__vm_writer.write_arithmetic("not")


class JackCompiler:
    """
    Represents a Jack compiler
    """
    def __init__(self):
        """
        Creates a new Jack compiler for the given program input
        """
        self.__input_progs_list = []
        self.__out_progs_list = []
        self.__create_progs_lists()

        for idx, in_prog in enumerate(self.__input_progs_list):
            cur_tokenizer = JackTokenizer(in_prog)
            cur_vm_writer = VMWriter(self.__out_progs_list[idx])
            cur_engine = CompilationEngine(cur_tokenizer, cur_vm_writer)
            if cur_tokenizer.has_more_tokens():
                cur_tokenizer.advance()
                cur_engine.compile_class()

        for idx in range(len(self.__input_progs_list)):
            self.__input_progs_list[idx].close()

    def __create_progs_lists(self):
        """
        Creates a list of the input and output programs for the analyzer
        :return: None
        """
        if os.path.isdir(sys.argv[1]):
            for file in os.listdir(sys.argv[1]):
                if file.endswith(IN_SUFFIX):
                    self.__input_progs_list.append(open(sys.argv[1] + '/' + file, 'r'))
                    self.__out_progs_list.append(open(sys.argv[1] + '/' + file[:-5] + OUT_SUFFIX, 'w'))
        else:
            self.__input_progs_list.append(open(sys.argv[1], 'r'))
            self.__out_progs_list.append(open(sys.argv[1][:-5] + OUT_SUFFIX, 'w'))


if __name__ == '__main__':
    JackCompiler()
