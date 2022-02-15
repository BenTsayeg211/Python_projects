from boggle_board_randomizer import *
from tkinter import *
from Boggle_gui_final import *


def list_of_possible_words(filename):
    """
    This function receives a filename and returns a list of all the lines.
    :param filename: the name of the text file containing the words
    :return: a list of all the words
    """
    with open(filename) as wordsfile:
        return wordsfile.read().splitlines()


class BoggleGame:
    """
    This class initiates a boggle game and contains all the relevant
    functions required for the game.
    """

    def __init__(self, root, font_type, size, bg, font_color, time):
        """
        This is the init function, it initiates an instance of Boggle Game,
        using the BoggleGui class as well.
        :param root: the tkinter root to initiate the game on
        :param font_type:
        :param size:
        :param bg: the background color of the game
        :param font_color: the color of the text in the game
        :param time:
        """
        self.font_color = font_color
        self.font_size = size
        self.font_type = font_type
        self.bg_color = bg
        self.time = time
        self.root = root
        # initiate a countdown and update id for the respective funcs to be
        # used by the time_countdown func when it needs to end the game,
        # this allows after_cancel to be called on the appropriate id.
        self.countdown_id = None
        self.update_id = None
        # initiate the board to be used in the game:
        self.board = randomize_board()
        # initiate the gui part of the game
        self.boggle_gui = BoggleGui(self.root, self.board, self.font_type,
                                    self.font_size, self.bg_color,
                                    self.font_color)
        self.score = 0
        self.current_location = None
        self.used_locations = []
        self.current_word_formation = ''
        self.list_of_words = list_of_possible_words('boggle_dict.txt')
        self.correct_words = []
        self.current_message = None

    def is_move_legal(self, current_location, target_location):
        """
        This function receives 2 locations and checks whether choosing the
        second location is a legal move in respect to the current location.
        :param current_location: the current location on the board (meaning
        the last letter button pressed)
        :param target_location: the requested location (meaning the next
        letter button pressed).
        :return: True if the move is legal, False if the move is illegal
        """
        if abs(target_location[0] - current_location[0]) > 1:
            return False
        if abs(target_location[1] - current_location[1]) > 1:
            return False
        return True

    def user_pressed_confirm(self):
        """
        This function handles what happens when the user presses the
        "confirm" button on the screen (meaning he wishes to finish the word).
        It first checks whether the correct word func returns true (for a
        word that exists in the dictionary) and then if the word is correct
        modifies the score accordingly, resets the current word formation
        and the current location and used locations,
        modifies the correct words list.
        :return: no return, just modifies the game fields
        """

        if self.correct_word(self.current_word_formation):
            # if one of the letters is the special combination Qu, we need
            # to first change the u to uppercase and only then show it on
            # the correct words list.
            if 'u' in self.current_word_formation:
                self.current_word_formation = self.current_word_formation.replace(
                    'u', 'U')
            self.score += (len(self.current_word_formation)) ** 2
            self.correct_words.append(self.current_word_formation)
            # now update the gui screen:
            self.boggle_gui.update_correct_words_list(
                self.current_word_formation)

            self.current_location = None
            # self.boggle_gui.current_location = None
            self.used_locations = []
            self.current_word_formation = ''
        else:
            # if the word is incorrect, reset everything:
            self.current_location = None
            self.used_locations = []
            self.current_word_formation = ''
        for button in self.boggle_gui.button_locations_dict:
            # either way, change the buttons background back to default:
            self.boggle_gui.button_locations_dict[button].configure(
                bg=str(self.boggle_gui.default_button_background))

    def user_pressed_clear(self):
        """
        This function handles what happens when the user presses the clear
        button on the game screen.
        :return: no return, changes the fields of game and gui
        """
        # first, return all the buttons bg to default:
        for button in self.boggle_gui.button_locations_dict:
            self.boggle_gui.button_locations_dict[button].configure(
                bg=str(self.boggle_gui.default_button_background))
        # now, reset the location, word formation and used locations fields:
        self.current_location = None
        self.current_word_formation = ''
        self.used_locations = []

    def correct_word(self, word):
        """
        This simple function receives a word and checks if it is a legal
        word in the dictionary.
        :param word: word to check
        :return: True if the word is legal, False if not
        """
        # first, if there is a lowercase u in the word (in the special
        # instance of Qu), replace it with U so that the word can be found
        # in the dictionary (comprised entirely of uppercase letters):
        if 'u' in word:
            word = word.replace('u', 'U')
        if word in self.list_of_words and word not in self.correct_words:
            return True
        return False

    def manage_user_selected_location(self, location_selected):
        """
        This function is the function that handles what happens when the
        user presses one of the letter buttons, which is the main thing
        happening in the game.
        The function handles all of the possible scenarios, including first
        selection, legal/illegal selection, reselction of last button pressed.
        :param location_selected: a tuple of two numbers, representing the (
        row, column) of the location selected on the board.
        :return: none
        """
        # if its the first choice on a clean board:
        if len(self.used_locations) == 0:
            self.current_location = location_selected
            self.used_locations.append(location_selected)
            self.current_word_formation += self.get_letter_at_location(
                location_selected)
            # update the gui with the button pressed:
            self.boggle_gui.button_locations_dict[location_selected]. \
                configure(bg='spring green')
            return

        # if its an illegal move due to not being neighboring:
        if not self.is_move_legal(self.current_location, location_selected):
            return
        # if user reselected the last location, remove that location from the
        # used locations list and reset current
        # location to the last location in the used list, if one exists:
        if location_selected == self.current_location:
            # reset the button bg to the default background:
            self.boggle_gui.button_locations_dict[location_selected].configure(
                bg=str(self.boggle_gui.default_button_background))
            # remove the location from used locations list:
            self.used_locations.pop()
            if len(self.used_locations) > 0:
                self.current_location = self.used_locations[-1]
                if self.get_letter_at_location(location_selected) == 'Qu':
                    self.current_word_formation = self.current_word_formation[
                                        :len(self.current_word_formation) - 2]
                else:
                    self.current_word_formation = self.current_word_formation[
                                        :len(self.current_word_formation) - 1]
            else:
                self.current_location = None
                if self.get_letter_at_location(location_selected) == 'Qu':
                    self.current_word_formation = self.current_word_formation[
                                        :len(self.current_word_formation) - 2]
                else:
                    self.current_word_formation = self.current_word_formation[
                                        :len(self.current_word_formation) - 1]
            return
        # if location selected is in the used locations list, it is an
        # illegal move, do nothing:
        if location_selected in self.used_locations:
            return
        # if the move is legal and not used already,
        # update the current location and used location lists and button bg:
        self.boggle_gui.button_locations_dict[location_selected].configure(
            bg='spring green')
        self.current_location = location_selected
        self.used_locations.append(location_selected)
        self.current_word_formation += self.get_letter_at_location(
            location_selected)

    def update_gui_with_gameplay_details(self):
        """
        This function updates the game screen with the current state of the
        game details.
        :return: none, updates the gui fields directly
        """
        self.boggle_gui.current_score_label.configure(text=str(self.score))
        self.boggle_gui.word_construct_label.configure(
            text=self.current_word_formation)

    def get_letter_at_location(self, location):
        """
        This simple function receives a location and returns the letter on
        that location in the board.
        :param location: a tuple of (row, column) numbers
        :return: the letter at that spot in the board
        """
        location_row = location[0]
        location_column = location[1]
        return self.board[location_row][location_column]

    def update_game_details(self):
        """
        This function checks whether "flags" have been raised by the gui
        requesting certain actions, calls the appropriate functions,
        and then immediately resets the flag.
        It then calls the update_gui func to make sure the screen is always
        updates, and finally it calls itself using root.after every 2
        milliseconds (while also updating its id in the field initiated in
        the init function, to be used at the end of the game)
        :return: none, updates the fields directly
        """
        if self.boggle_gui.letter_button_current_request:
            location_to_deal_with = self.boggle_gui.current_button_location
            self.manage_user_selected_location(location_to_deal_with)
            self.boggle_gui.letter_button_current_request = False
        if self.boggle_gui.clear_button_request:
            self.user_pressed_clear()
            self.boggle_gui.clear_button_request = False
        if self.boggle_gui.confirm_button_request:
            self.user_pressed_confirm()
            self.boggle_gui.confirm_button_request = False
        self.update_gui_with_gameplay_details()
        self.update_id = self.root.after(2, self.update_game_details)

    def time_countdown(self):
        """
        This function handles the time countdown (3 minutes to play the
        game) and handles what happens when the time runs out
        :return: none, handles all actions directly
        """
        # if there is still time remaining, call recursively using after
        # method until time is up, also updating the id of the after call to
        # be used at the endgame:
        if self.boggle_gui.seconds > 0:
            self.boggle_gui.seconds -= 1
            self.boggle_gui.update_time()
            self.countdown_id = self.root.after(self.time, self.time_countdown)
        else:
            # if the time is up, cancel the after calls pending for update
            # and countdown functions, and then ask the user if they would
            # like to play again:
            self.root.after_cancel(self.countdown_id)
            self.root.after_cancel(self.update_id)
            user_ans = self.boggle_gui.time_is_up_message_box()
            if not user_ans:
                # if the user selected no, destroy and exit:
                self.root.destroy()

            if user_ans:
                # if the user pressed yes, destroy current window and
                # immediately open a new root and new game on it.
                self.root.destroy()
                new_game_root = Tk()
                new_game = BoggleGame(new_game_root, self.font_type,
                                      self.font_size,
                                      self.bg_color, self.font_color,
                                      self.time)
                new_game.time_countdown()
                new_game.update_game_details()


def start_game_standard_mode():
    """
    This function destroys the start screen and starts a game in "standard
    mode", a standard looking game
    of Boggle.
    :return: no return, runs the game
    """
    game = BoggleGame(root1, 'david', 2, 'white', 'black', 10000000)
    game.time_countdown()
    game.update_game_details()
root1 = Tk()
root1.configure(bg='old lace')
start_game_standard_mode()
root1.mainloop()

