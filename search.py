"""
In search.py, you will implement generic search algorithms
"""

import util


class StateNode:

    def __init__(self, state, father, move, cost):
        self.state = state
        self.father = father
        self.move = move
        self.cost = cost


class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def get_start_state(self):
        """
        Returns the start state for the search problem
        """
        util.raiseNotDefined()

    def is_goal_state(self, state):
        """
        state: Search state

        Returns True if and only if the state is a valid goal state
        """
        util.raiseNotDefined()

    def get_successors(self, state):
        """
        state: Search state

        For a given state, this should return a list of triples,
        (successor, action, stepCost), where 'successor' is a
        successor to the current state, 'action' is the action
        required to get there, and 'stepCost' is the incremental
        cost of expanding to that successor
        """
        util.raiseNotDefined()

    def get_cost_of_actions(self, actions):
        """
        actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.  The sequence must
        be composed of legal moves
        """
        util.raiseNotDefined()


def depth_first_search(problem):
    """
    Search the deepest nodes in the search tree first.

    Your search algorithm needs to return a list of actions that reaches
    the goal. Make sure to implement a graph search algorithm.

    To get started, you might want to try some of these simple commands to
    understand the search problem that is being passed in:

	print("Start:", problem.get_start_state().state)
    print("Is the start a goal?", problem.is_goal_state(problem.get_start_state()))
    print("Start's successors:", problem.get_successors(problem.get_start_state()))
    """
    "*** YOUR CODE HERE ***"
    stack = util.Stack()
    stack.push((problem.get_start_state(), []))
    opened_states = set()
    while not stack.isEmpty():
        cur_state = stack.pop()
        if problem.is_goal_state(cur_state[0]):
            return cur_state[1]
        if cur_state[0] in opened_states:
            continue
        opened_states.add(cur_state[0])
        cur_actions = cur_state[1]
        cur_successors = problem.get_successors(cur_state[0])
        for suc in cur_successors:
            new_actions = [*cur_actions, suc[1]]
            stack.push((suc[0], new_actions))


def breadth_first_search(problem):
    """
    Search the shallowest nodes in the search tree first.
    """
    if problem.is_goal_state(problem.get_start_state()):
        return []
    queue = util.Queue()
    queue.push((problem.get_start_state(), []))
    opened_states = set()
    while not queue.isEmpty():
        cur_state = queue.pop()
        if cur_state[0] in opened_states:
            continue
        opened_states.add(cur_state[0])
        cur_actions = cur_state[1]
        cur_successors = problem.get_successors(cur_state[0])
        for suc in cur_successors[::-1]:
            new_actions = [*cur_actions, suc[1]]
            if problem.is_goal_state(suc[0]):
                return new_actions
            queue.push((suc[0], new_actions))


def uniform_cost_search(problem):
    """
    Search the node of least total cost first.
    """
    pr_queue = util.PriorityQueue()
    pr_queue.push(StateNode(problem.get_start_state(), None, None, 0), 0)
    opened_states = set()
    while not pr_queue.isEmpty():
        cur_state_node = pr_queue.pop()
        if cur_state_node.state in opened_states:
            continue
        if problem.is_goal_state(cur_state_node.state):
            return get_moves_list(cur_state_node)
        opened_states.add(cur_state_node.state)
        cur_successors = problem.get_successors(cur_state_node.state)
        for suc in cur_successors:
            new_cost = cur_state_node.cost + suc[2]
            pr_queue.push(StateNode(suc[0], cur_state_node, suc[1], new_cost),
                          new_cost)


def null_heuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0


def a_star_search(problem, heuristic=null_heuristic):
    """
    Search the node that has the lowest combined cost and heuristic first.
    """
    "*** YOUR CODE HERE ***"
    problem.ones = []
    for piece in problem.board.piece_list:
        if piece.get_num_tiles() == 1:
            problem.ones.append(piece)
    pr_queue = util.PriorityQueue()
    pr_queue.push(StateNode(problem.get_start_state(), None, None, 0), 0)
    opened_states = set()
    while not pr_queue.isEmpty():
        cur_state_node = pr_queue.pop()
        if cur_state_node.state in opened_states:
            continue
        if problem.is_goal_state(cur_state_node.state):
            return get_moves_list(cur_state_node)
        opened_states.add(cur_state_node.state)
        cur_successors = problem.get_successors(cur_state_node.state)
        for suc in cur_successors:
            new_cost = cur_state_node.cost + suc[2]
            pr_queue.push(StateNode(suc[0], cur_state_node, suc[1], new_cost),
                          new_cost + heuristic(suc[0], problem))


def get_moves_list(state_node):
    moves_list = []
    while state_node.move:
        moves_list.append(state_node.move)
        state_node = state_node.father
    return moves_list[::-1]


# Abbreviations
bfs = breadth_first_search
dfs = depth_first_search
astar = a_star_search
ucs = uniform_cost_search
