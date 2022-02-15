from board import Board
from search import SearchProblem, astar
import util
from itertools import combinations
from functools import reduce
import numpy as np
from search import StateNode, get_moves_list


class BlokusFillProblem(SearchProblem):
    """
    A one-player Blokus game as a search problem.
    This problem is implemented for you. You should NOT change it!
    """

    def __init__(self, board_w, board_h, piece_list, starting_point=(0, 0)):
        self.board = Board(board_w, board_h, 1, piece_list, starting_point)
        self.expanded = 0

    def get_start_state(self):
        """
        Returns the start state for the search problem
        """
        return self.board

    def is_goal_state(self, state):
        """
        state: Search state
        Returns True if and only if the state is a valid goal state
        """
        return not any(state.pieces[0])

    def get_successors(self, state):
        """
        state: Search state

        For a given state, this should return a list of triples,
        (successor, action, stepCost), where 'successor' is a
        successor to the current state, 'action' is the action
        required to get there, and 'stepCost' is the incremental
        cost of expanding to that successor
        """
        # Note that for the search problem, there is only one player - #0
        self.expanded = self.expanded + 1
        return [(state.do_move(0, move), move, 1) for move in
                state.get_legal_moves(0)]

    def get_cost_of_actions(self, actions):
        """
        actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.  The sequence must
        be composed of legal moves
        """
        return len(actions)


#####################################################
# This portion is incomplete.  Time to write code!  #
#####################################################
class BlokusCornersProblem(SearchProblem):
    def __init__(self, board_w, board_h, piece_list, starting_point=(0, 0)):
        self.board = Board(board_w, board_h, 1, piece_list, starting_point)
        self.expanded = 0

    def get_start_state(self):
        """
        Returns the start state for the search problem
        """
        return self.board

    def is_goal_state(self, state):
        return not (state.get_position(self.board.board_w - 1, 0) == -1
                    or state.get_position(0, self.board.board_h - 1) == -1
                    or state.get_position(self.board.board_w - 1,
                                          self.board.board_h - 1) == -1)

    def get_successors(self, state):
        """
        state: Search state

        For a given state, this should return a list of triples,
        (successor, action, stepCost), where 'successor' is a
        successor to the current state, 'action' is the action
        required to get there, and 'stepCost' is the incremental
        cost of expanding to that successor
        """
        # Note that for the search problem, there is only one player - #0
        self.expanded = self.expanded + 1
        return [(state.do_move(0, move), move, move.piece.get_num_tiles()) for
                move in state.get_legal_moves(0)]

    def get_cost_of_actions(self, actions):
        """
        actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.  The sequence must
        be composed of legal moves
        """
        total_cost = 0
        for action in actions:
            total_cost += action.piece.get_num_tiles()
        return total_cost


def blokus_corners_heuristic(state, problem):
    """
    Your heuristic for the BlokusCornersProblem goes here.

    This heuristic must be consistent to ensure correctness.  First, try to come up
    with an admissible heuristic; almost all admissible heuristics will be consistent
    as well.

    If using A* ever finds a solution that is worse uniform cost search finds,
    your heuristic is *not* consistent, and probably not admissible!  On the other hand,
    inadmissible or inconsistent heuristics may find optimal solutions, so be careful.
    """
    "*** YOUR CODE HERE ***"
    max_area = problem.board.board_w * problem.board.board_h
    no_1 = True
    for piece in problem.ones:
        if state.pieces[0, state.piece_list.pieces.index(piece)]:
            no_1 = False
            break
    if (state.get_position(problem.board.board_w - 1, 0) == -1 and
            (state.get_position(problem.board.board_w - 1, 1) != -1 or
             state.get_position(problem.board.board_w - 2, 0) != -1 or
             (state.get_position(problem.board.board_w - 2, 1) != -1 and
              no_1))):
        return max_area
    if (state.get_position(problem.board.board_w - 1,
                           problem.board.board_h - 1) == -1
            and (state.get_position(problem.board.board_w - 2,
                                    problem.board.board_h - 1) != -1 or
                 state.get_position(problem.board.board_w - 1,
                                    problem.board.board_h - 2) != -1 or
                 (state.get_position(problem.board.board_w - 2,
                                     problem.board.board_h - 2) != -1 and
                  no_1))):
        return max_area
    if (state.get_position(0, problem.board.board_h - 1) == -1
            and (state.get_position(0, problem.board.board_h - 2) != -1
                 or state.get_position(1, problem.board.board_h - 1) != -1
                 or (state.get_position(1, problem.board.board_h - 2) != -1 and
                     no_1))):
        return max_area
    unreached_corners = []
    if state.get_position(problem.board.board_w - 1, 0) == -1:
        unreached_corners.append((problem.board.board_w - 1, 0))
    if state.get_position(0, problem.board.board_h - 1) == -1:
        unreached_corners.append((0, problem.board.board_h - 1))
    if (state.get_position(problem.board.board_w - 1,
                           problem.board.board_h - 1) == -1):
        unreached_corners.append((problem.board.board_w - 1,
                                  problem.board.board_h - 1))
    if len(unreached_corners) == 0:
        return 0
    min_dists = []
    for corner in unreached_corners:
        min_dists.append(float("inf"))
    row_num = len(state.state)
    col_num = len(state.state[0])
    for row in range(row_num):
        for col in range(col_num):
            if state.connected[0][row][col] and \
                    state.get_position(col, row) == -1:
                for idx in range(len(unreached_corners)):
                    dist = max(abs(col - unreached_corners[idx][0]),
                               abs(row - unreached_corners[idx][1])) + 1
                    if dist < min_dists[idx]:
                        min_dists[idx] = dist
    max_min_dist = max(min_dists) + len(unreached_corners) - 1
    remaining_pieces = []
    for piece in state.piece_list:
        if state.pieces[0, state.piece_list.pieces.index(piece)]:
            remaining_pieces.append(piece)
    min_pos_val = max_area
    for length in range(len(remaining_pieces) + 1):
        for comb in combinations(remaining_pieces, length):
            cur_val = reduce(lambda a, b: a + b.get_num_tiles(), comb, 0)
            if max_min_dist <= cur_val < min_pos_val:
                min_pos_val = cur_val
    return min_pos_val


class BlokusCoverProblem(SearchProblem):
    def __init__(self, board_w, board_h, piece_list, starting_point=(0, 0),
                 targets=[(0, 0)]):
        self.targets = targets.copy()
        self.expanded = 0
        "*** YOUR CODE HERE ***"
        self.board = Board(board_w, board_h, 1, piece_list, starting_point)

    def get_start_state(self):
        """
        Returns the start state for the search problem
        """
        return self.board

    def is_goal_state(self, state):
        "*** YOUR CODE HERE ***"
        for target in self.targets:
            if state.get_position(target[1], target[0]) == -1:
                return False
        return True

    def get_successors(self, state):
        """
        state: Search state

        For a given state, this should return a list of triples,
        (successor, action, stepCost), where 'successor' is a
        successor to the current state, 'action' is the action
        required to get there, and 'stepCost' is the incremental
        cost of expanding to that successor
        """
        # Note that for the search problem, there is only one player - #0
        self.expanded = self.expanded + 1
        return [(state.do_move(0, move), move, move.piece.get_num_tiles()) for
                move in state.get_legal_moves(0)]

    def get_cost_of_actions(self, actions):
        """
        actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.  The sequence must
        be composed of legal moves
        """
        "*** YOUR CODE HERE ***"
        total_cost = 0
        for action in actions:
            total_cost += action.piece.get_num_tiles()
        return total_cost


def blokus_cover_heuristic(state, problem):
    "*** YOUR CODE HERE ***"
    max_area = problem.board.board_w * problem.board.board_h
    unreached_targets = []
    for target in problem.targets:
        if state.get_position(target[1], target[0]) == -1:
            unreached_targets.append((target[1], target[0]))
            if 0 <= target[0] - 1 and state.get_position(target[1],
                                                         target[0] - 1) != -1:
                return max_area
            if target[0] + 1 <= problem.board.board_h - 1 and \
                    state.get_position(target[1], target[0] + 1) != -1:
                return max_area
            if 0 <= target[1] - 1 and state.get_position(target[1] - 1,
                                                         target[0]) != -1:
                return max_area
            if target[1] + 1 <= problem.board.board_w - 1 and \
                    state.get_position(target[1] + 1, target[0]) != -1:
                return max_area
    if len(unreached_targets) == 0:
        return 0
    min_dists = []
    for target in unreached_targets:
        min_dists.append(float("inf"))
    row_num = len(state.state)
    col_num = len(state.state[0])
    for row in range(row_num):
        for col in range(col_num):
            if state.connected[0][row][col] and \
                    state.get_position(col, row) == -1:
                for idx in range(len(unreached_targets)):
                    dist = max(abs(col - unreached_targets[idx][0]),
                               abs(row - unreached_targets[idx][1])) + 1
                    if dist < min_dists[idx]:
                        min_dists[idx] = dist
    return max(min_dists)


class ClosestLocationSearch:
    """
    In this problem you have to cover all given positions on the board,
    but the objective is speed, not optimality.
    """

    def __init__(self, board_w, board_h, piece_list, starting_point=(0, 0),
                 targets=(0, 0)):
        self.expanded = 0
        self.targets = targets.copy()
        "*** YOUR CODE HERE ***"
        self.board = Board(board_w, board_h, 1, piece_list, starting_point)

    def get_start_state(self):
        """
        Returns the start state for the search problem
        """
        return self.board

    def solve(self):
        """
        This method should return a sequence of actions that covers all target locations on the board.
        This time we trade optimality for speed.
        Therefore, your agent should try and cover one target location at a time. Each time, aiming for the closest uncovered location.
        You may define helpful functions as you wish.

        Probably a good way to start, would be something like this --

        current_state = self.board.__copy__()
        backtrace = []

        while ....

            actions = set of actions that covers the closets uncovered target location
            add actions to backtrace

        return backtrace
        """
        "*** YOUR CODE HERE ***"
        cur_state = self.board.__copy__()
        remaining_targets = self.targets.copy()
        backtrace = []
        while remaining_targets:
            closest_idx = find_closest_uncovered(cur_state, remaining_targets)
            closest_target = remaining_targets.pop(closest_idx)
            new_moves, cur_state, new_expansions = ucs_closest(
                cur_state, closest_target)
            backtrace.extend(new_moves)
            self.expanded += new_expansions
        return backtrace


def find_closest_uncovered(cur_state, remaining_targets):
    min_dists = []
    for target in remaining_targets:
        min_dists.append(float("inf"))
    row_num = len(cur_state.state)
    col_num = len(cur_state.state[0])
    for row in range(row_num):
        for col in range(col_num):
            if cur_state.connected[0][row][col] and \
                    cur_state.check_tile_legal(0, col, row):
                for idx in range(len(remaining_targets)):
                    dist = max(abs(col - remaining_targets[idx][0]),
                               abs(row - remaining_targets[idx][1])) + 1
                    if dist < min_dists[idx]:
                        min_dists[idx] = dist
    return np.argmin(min_dists)


def ucs_closest(cur_state, cur_target):
    expanded = 0
    pr_queue = util.PriorityQueue()
    pr_queue.push(StateNode(cur_state, None, None, 0), 0)
    opened_states = set()
    while not pr_queue.isEmpty():
        cur_state_node = pr_queue.pop()
        if cur_state_node.state in opened_states:
            continue
        if cur_state_node.state.get_position(cur_target[1], cur_target[0]) \
                != -1:
            return get_moves_list(cur_state_node), cur_state_node.state, \
                   expanded
        opened_states.add(cur_state_node.state)
        cur_successors = [(cur_state_node.state.do_move(0, move), move,
                           move.piece.get_num_tiles()) for move in
                          cur_state_node.state.get_legal_moves(0)]
        expanded += 1
        for suc in cur_successors:
            new_cost = cur_state_node.cost + suc[2]
            pr_queue.push(
                StateNode(suc[0], cur_state_node, suc[1], new_cost),
                new_cost)


class MiniContestSearch:
    """
    Implement your contest entry here
    """

    def __init__(self, board_w, board_h, piece_list, starting_point=(0, 0),
                 targets=(0, 0)):
        self.targets = targets.copy()
        "*** YOUR CODE HERE ***"
        self.board = Board(board_w, board_h, 1, piece_list, starting_point)
        self.cover_problem = BlokusCoverProblem(board_w, board_h, piece_list,
                                                starting_point, self.targets)
        self.expanded = 0

    def get_start_state(self):
        """
        Returns the start state for the search problem
        """
        return self.board

    def solve(self):
        "*** YOUR CODE HERE ***"
        moves = astar(self.cover_problem, blokus_cover_heuristic)
        self.expanded = self.cover_problem.expanded
        return moves


def blokus_cover_heuristic_not_admis(state, problem):
    max_area = problem.board.board_w * problem.board.board_h
    unreached_targets = []
    for target in problem.targets:
        if state.get_position(target[1], target[0]) == -1:
            unreached_targets.append((target[1], target[0]))
            if 0 <= target[0] - 1 and state.get_position(target[1],
                                                         target[0] - 1) != -1:
                return max_area
            if target[0] + 1 <= problem.board.board_h - 1 and \
                    state.get_position(target[1], target[0] + 1) != -1:
                return max_area
            if 0 <= target[1] - 1 and state.get_position(target[1] - 1,
                                                         target[0]) != -1:
                return max_area
            if target[1] + 1 <= problem.board.board_w - 1 and \
                    state.get_position(target[1] + 1, target[0]) != -1:
                return max_area
    if len(unreached_targets) == 0:
        return 0
    min_dists = []
    for target in unreached_targets:
        min_dists.append(float("inf"))
    row_num = len(state.state)
    col_num = len(state.state[0])
    for row in range(row_num):
        for col in range(col_num):
            if state.connected[0][row][col] and \
                    state.get_position(col, row) == -1:
                for idx in range(len(unreached_targets)):
                    dist = max(abs(col - unreached_targets[idx][0]),
                               abs(row - unreached_targets[idx][1])) + 1
                    if dist < min_dists[idx]:
                        min_dists[idx] = dist
    return sum(min_dists)
