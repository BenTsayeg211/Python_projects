import sys
import os

IN_SUFFIX = ".vm"
OUT_SUFFIX = ".asm"
SEGMENTS = {"local": "LCL", "argument": "ARG", "this": "THIS", "that": "THAT",
            "temp": "5"}
POINTERS = {"0": "THIS", "1": "THAT"}
PUSH_END = "@SP\nA=M\nM=D\n@SP\nM=M+1"
POP_START = "@SP\nM=M-1\n"
ARITH_START = "@SP\nAM=M-1\n"
ARITH_END = "@SP\nM=M+1"


class Counter:
    """
    An object that holds all the counters needed for the labels created
    by eq, gt and lt
    """
    def __init__(self):
        self.eqCounter = 0
        self.aGTEGT = 0
        self.calcGT = 0
        self.gt = 0
        self.endGT = 0
        self.aGTELT = 0
        self.calcLT = 0
        self.lt = 0
        self.endLT = 0


def create_prog_list(progs_list):
    """
    Creates a list of programs to translate based on the given program input
    :param progs_list: The list to fill with the programs
    :return: The list of programs to translate
    """
    if os.path.isdir(sys.argv[1]):
        for file in os.listdir(sys.argv[1]):
            if file.endswith(IN_SUFFIX):
                cur_file = open(sys.argv[1] + '/' + file, 'r')
                progs_list.append(cur_file)
    else:
        cur_file = open(sys.argv[1])
        progs_list.append(cur_file)


def parse_line(cur_line):
    """
    Removes tabs, comments and spaces from the given line and splits it
    :param cur_line: The current line to parse
    :return: A list with the different parts of the line
    """
    if "\n" in cur_line:
        cur_line = cur_line[:cur_line.find("\n")]
    if "//" in cur_line:
        cur_line = cur_line[:cur_line.find("//")]
    for x in range(cur_line.count("\t")):
        cur_line = cur_line.replace("\t", "")
    cur_line = cur_line.split(" ")
    for x in range(cur_line.count('')):
        cur_line.remove('')
    return cur_line


def get_name(file_name):
    """
    Gets the name of the file without the path (needed for static names)
    :param file_name: The file name (with path if given)
    :return: only the file name
    """
    if "/" in file_name:
        file_name = file_name[file_name.rindex("/") + 1: -3]
    return file_name


def translate_to_assembly(command, cur_name, count):
    """
    Translates the given vm language command to hack assembly
    :param command: The given vm command
    :param cur_name: The current file name
    :param count: The counter object
    :return: The translation of the command to hack assembly
    """
    if len(command) == 0:
        return ""
    if command[0] == "push":
        comment = " // " + command[0] + " " + command[1] + " " + command[2]
        if (command[1] == "local" or command[1] == "argument" or
                command[1] == "this" or command[1] == "that"):
            commands = "@" + command[2] + "\nD=A\n@" + SEGMENTS[command[1]] + \
                       "\nA=D+M\nD=M\n"
        elif command[1] == "constant":
            commands = "@" + command[2] + "\nD=A\n"
        elif command[1] == "static":
            commands = "@" + cur_name + "." + command[2] + "\nD=M\n"
        elif command[1] == "temp":
            commands = "@" + command[2] + "\nD=A\n@" + SEGMENTS[command[1]] + \
                       "\nA=D+A\nD=M\n"
        else:
            commands = "@" + POINTERS[command[2]] + "\nD=M\n"
        return commands + PUSH_END + comment + "\n"

    elif command[0] == "pop":
        comment = " // " + command[0] + " " + command[1] + " " + command[2]
        if (command[1] == "local" or command[1] == "argument" or
                command[1] == "this" or command[1] == "that"):
            commands = "@" + command[2] + "\nD=A\n@" + SEGMENTS[command[1]] + \
                       "\nD=D+M\n@R13\nM=D\n@SP\nA=M\nD=M\n@R13\nA=M\nM=D" + \
                       comment + "\n"
        elif command[1] == "static":
            commands = "A=M\nD=M\n@" + cur_name + "." + command[2] + "\nM=D" +\
                       comment + "\n"
        elif command[1] == "temp":
            commands = "@" + command[2] + "\nD=A\n@" + SEGMENTS[command[1]] + \
                       "\nD=D+A\n@R13\nM=D\n@SP\nA=M\nD=M\n@R13\nA=M\nM=D" + \
                       comment + "\n"
        else:
            commands = "A=M\nD=M\n@" + POINTERS[command[2]] + "\nM=D" + \
                       comment + "\n"
        return POP_START + commands

    elif command[0] == "add":
        comment = " // " + command[0]
        commands = ARITH_START + "D=M\n@SP\nAM=M-1\nM=D+M\n" + \
                                 ARITH_END + comment + "\n"
        return commands
    elif command[0] == "sub":
        comment = " // " + command[0]
        commands = ARITH_START + "D=M\n@SP\nAM=M-1\nM=M-D\n" + \
                                 ARITH_END + comment + "\n"
        return commands
    elif command[0] == "neg":
        comment = " // " + command[0]
        commands = ARITH_START + "M=-M\n" + ARITH_END + comment + "\n"
        return commands

    elif command[0] == "and":
        comment = " // " + command[0]
        commands = ARITH_START + "D=M\n@SP\nAM=M-1\nM=D&M\n" + \
                                 ARITH_END + comment + "\n"
        return commands
    elif command[0] == "or":
        comment = " // " + command[0]
        commands = ARITH_START + "D=M\n@SP\nAM=M-1\nM=D|M\n" + \
                                 ARITH_END + comment + "\n"
        return commands
    elif command[0] == "not":
        comment = " // " + command[0]
        commands = ARITH_START + "M=!M\n" + ARITH_END + comment + "\n"
        return commands

    elif command[0] == "eq":
        comment = " // " + command[0]
        commands = ARITH_START + "D=M\n@SP\nAM=M-1\nD=M-D\nM=-1\n@eq" + \
                                 str(count.eqCounter) + \
                                 "\nD;JEQ\n@SP\nA=M\nM=0\n(eq" + \
                                 str(count.eqCounter) + ")\n" + \
                                 ARITH_END + comment + "\n"
        count.eqCounter += 1
        return commands
    elif command[0] == "gt":
        comment = " // " + command[0]
        commands = ARITH_START + \
                   "D=M\n@R13\nM=D\n@SP\nAM=M-1\nD=M\n@aGTEGT" + \
                   str(count.aGTEGT) + "\nD;JGE\n@R13\nD=M\n@CALCGT" + \
                   str(count.calcGT) + "\nD;JLT\n@SP\nA=M\nM=0\n@ENDGT" + \
                   str(count.endGT) + "\n0;JMP\n(aGTEGT" + str(count.aGTEGT) +\
                   ")\n@R13\nD=M\n@CALCGT" + str(count.calcGT) + \
                   "\nD;JGE\n@SP\nA=M\nM=-1\n@ENDGT" + str(count.endGT) + \
                   "\n0;JMP\n(CALCGT" + str(count.calcGT) + \
                   ")\n@SP\nA=M\nD=M-D\n@GT" + str(count.gt) + \
                   "\nD;JGT\n@SP\nA=M\nM=0\n@ENDGT" + str(count.endGT) + \
                   "\n0;JMP\n(GT" + str(count.gt) + ")\n@SP\nA=M\nM=-1\n(ENDGT" + \
                   str(count.endGT) + ")\n" + ARITH_END + comment + "\n"
        count.aGTEGT += 1
        count.calcGT += 1
        count.gt += 1
        count.endGT += 1
        return commands
    elif command[0] == "lt":
        comment = " // " + command[0]
        commands = ARITH_START + \
                   "D=M\n@R13\nM=D\n@SP\nAM=M-1\nD=M\n@aGTELT" + \
                   str(count.aGTELT) + "\nD;JGE\n@R13\nD=M\n@CALCLT" + \
                   str(count.calcLT) + "\nD;JLT\n@SP\nA=M\nM=-1\n@ENDLT" + \
                   str(count.endLT) + "\n0;JMP\n(aGTELT" + str(count.aGTELT) +\
                   ")\n@R13\nD=M\n@CALCLT" + str(count.calcLT) + \
                   "\nD;JGE\n@SP\nA=M\nM=0\n@ENDLT" + str(count.endLT) + \
                   "\n0;JMP\n(CALCLT" + str(count.calcLT) + \
                   ")\n@SP\nA=M\nD=M-D\n@LT" + str(count.lt) + \
                   "\nD;JLT\n@SP\nA=M\nM=0\n@ENDLT" + str(count.endLT) + \
                   "\n0;JMP\n(LT" + str(count.lt) + ")\n@SP\nA=M\nM=-1\n(ENDLT" + \
                   str(count.endLT) + ")\n" + ARITH_END + comment + "\n"
        count.aGTELT += 1
        count.calcLT += 1
        count.lt += 1
        count.endLT += 1
        return commands


if __name__ == '__main__':
    progs = []
    create_prog_list(progs)
    if os.path.isdir(sys.argv[1]):
        out_name = sys.argv[1]
    else:
        out_name = sys.argv[1][:-3]
    out_file = open(out_name + OUT_SUFFIX, 'w')
    counter = Counter()
    for prog in progs:
        out_file.write("// " + prog.name[:-3] + OUT_SUFFIX + "\n")
        for line in prog:
            line = parse_line(line)
            line = translate_to_assembly(line, get_name(prog.name), counter)
            out_file.write(line)
        out_file.write("\n")
        prog.close()

    out_file.close()
