from tkinter import *
from tkinter import messagebox


class BoggleGui:
    """
    This class intiates and manages a gui using tkinter to allow the user to
    play the game Boggle.
    """
    def __init__(self, root, board, font_type, size, bg, font_color):
        """
        This is the init fucntion, the constructor for the BoggleGui class
        :param root: the root upon which to work
        :param board: the board to implement the letters on
        :param font_type: what type of font to use in the
        :param size: font size
        :param bg: the background color of the game
        :param font_color: the font color of the game
        """
        self.font_color = font_color
        self.font_size = size
        self.font_type = font_type
        self.bg_color = bg
        self.board = board
        root.configure(background=self.bg_color)
        # give the user 3 minutes to play, the 181 seconds is because the
        # first second is missed due to the delayed call to after in the
        # gameplay time countdown.
        self.seconds = 5
        # initiate flags to be raised when a button is pressed that can be
        # checked by the gameplay:
        self.letter_button_current_request = False
        self.clear_button_request = False
        self.confirm_button_request = False
        # field to be checked by gameplay which button is pressed:
        self.current_button_location = None
        self.initial_score = 0
        # initiate a stringvar to represent the time remaining
        self.time_var = StringVar()
        # ------------------------------left_frame----------------------#
        self.left_frame = Frame(root, bg=self.bg_color)
        self.left_frame.pack(side=LEFT, fill=BOTH, pady=20, padx=20)
        # -----------------------Time------------------------#
        self.time_title_label = LabelFrame(self.left_frame,
                                           text='Time remaining:',
                                           font=(self.font_type,
                                                 25 + self.font_size), padx=5,
                                           pady=5, highlightthickness=4,
                                           highlightbackground='blue',
                                           bg=self.bg_color,
                                           fg=self.font_color)
        self.time_title_label.pack(side=TOP, pady=20)


        self.time_remaining_label = Label(self.time_title_label,
                                          textvariable=self.time_var,
                                          font=(self.font_type,
                                                20 + self.font_size),
                                          bg='white')
        self.time_remaining_label.pack()

        # -----------------------word_list--------------------------------#
        self.word_list_header_frame = Frame(self.left_frame,
                                            bg=self.bg_color)
        self.word_list_header_frame.pack(padx=6, pady=10)

        self.correct_list_header_label = Label(self.word_list_header_frame,
                                               text='Correct words',
                                               font=(self.font_type,
                                                     30 + self.font_size),
                                               padx=1, pady=1,
                                               bg=self.bg_color,
                                               fg=self.font_color)
        self.correct_list_header_label.pack(side=TOP, padx=3, pady=3)

        self.word_list_frame = Frame(self.left_frame, bg=self.bg_color)
        self.word_list_frame.pack(padx=2, pady=2)

        scrollbar = Scrollbar(self.word_list_frame, orient="vertical")

        self.correct_word_list_box = Listbox(self.word_list_frame,
                                             yscroll=scrollbar.set,
                                             font=15, fg=self.font_color,
                                             bg=self.bg_color)
        scrollbar.pack(side=LEFT, fill="y")

        self.correct_word_list_box.pack(padx=2, pady=2)
        scrollbar.config(command=self.correct_word_list_box.yview)

        self.correct_word_list_box.config(yscrollcommand=scrollbar.set)
        self.correct_word_list_box.pack(padx=2, pady=2)
        # ------------------SCORE----------------------------#
        self.score_frame = Frame(root, bg=self.bg_color)
        self.score_frame.pack(side=RIGHT, fill=BOTH, padx=120, pady=44)

        self.score_title = LabelFrame(self.score_frame, text='Score:',
                                      font=(
                                      self.font_type, 25 + self.font_size)
                                      , padx=20,
                                      pady=5, highlightthickness=4,
                                      highlightbackground='light goldenrod',
                                      bg=self.bg_color,
                                      fg=self.font_color)
        self.score_title.pack(side=TOP)

        self.current_score_label = Label(self.score_title,
                                         text=str(self.initial_score),
                                         font=(self.font_type,
                                               25 + self.font_size),
                                         bg=self.bg_color,
                                         fg=self.font_color)
        self.current_score_label.pack()
        # ----------------------Top_frame-------------------#
        self.top_frame = Frame(root, bg=self.bg_color)
        self.top_frame.pack(side=TOP)

        self.boggle_label = Label(self.top_frame, text="Boggle",
                                  bg=self.bg_color,
                                  fg=self.font_color,
                                  font=(self.font_type, 50 + self.font_size))
        self.boggle_label.pack(side=TOP, pady=30)
        # ------------------------Bottom_frame-----------------#
        self.bottom_frame = Frame(root, bg=self.bg_color)
        self.bottom_frame.pack(side=BOTTOM)

        self.word_construct_frame = Frame(self.bottom_frame)
        self.word_construct_frame.pack(side=BOTTOM, pady=18)

        self.word_construct_label = Label(self.word_construct_frame,
                                        text='this is where the word is built',
                                        font=(self.font_type,
                                        25 + self.font_size),
                                        padx=10, pady=5,
                                        bg=self.bg_color,
                                        fg=self.font_color)
        self.word_construct_label.pack(side=BOTTOM, padx=2, pady=2)

        self.confirm_button = Button(self.bottom_frame, bg='green2',
                                     highlightthickness=2, height=1, width=10,
                                     font=(
                                     self.font_type, 20 + self.font_size),
                                     text='Confirm',
                                     command=self.confirm_pressed)
        self.confirm_button.pack(side=LEFT)

        self.clear_button = Button(self.bottom_frame, bg='red2',
                                   highlightthickness=2, height=1,
                                   width=10,
                                   font=(self.font_type,
                                             20 + self.font_size),
                                   text='Clear', command=self.clear)
        self.clear_button.pack(side=RIGHT)
        # --------------------Buttons_frame----------------------#
        self.letter_buttons_frame = Frame(root)
        self.letter_buttons_frame.pack(pady=20)
        # create a dictionary to hold the locations as keys and the button
        # objects as values to be used by gameplay:
        self.button_locations_dict = {}
        i = 0
        for x, row in enumerate(self.board):
            for y, letter in enumerate(row):
                # create a function for each button using the following
                # func, to be explained there:
                button_func = self.get_location_of_button_pressed(x, y)
                self.button_locations_dict[x, y] = \
                    Button(self.letter_buttons_frame, text=letter,
                    font=(self.font_type, 33 + self.font_size), width=3,
                    command=button_func)
                self.button_locations_dict[x, y].grid(row=i // 4, column=i % 4)
                i += 1
        # get the default button background (differs between windows and
        # linux systems, in order to reset the bg of the button in gameplay:
        self.default_button_background =\
            self.button_locations_dict[(0, 0)].cget("background")

    def get_location_of_button_pressed(self, x, y):
        """
        This second order function helps us to create a unique function for
        each button to link its command to, thus allowing us to treat only
        the button that was pressed.
        :param x: the x coordinate of the button (the row num)
        :param y: the y coordinate of the button (the column num)
        :return: the function for each button
        """
        def inner_func():
            # raise a flag letting the game know that a letter button was
            # pressed and change the current button to the appropriate
            # coordinates for gameplay to handle:
            self.letter_button_current_request = True
            self.current_button_location = x, y
        return inner_func

    def time_as_string(self):
        """
        This func simply represents the current time remaining as a str in
        order to show to user.
        :return: the time remaining as a str
        """
        minutes_remaining = str(self.seconds // 60)
        if self.seconds:
            seconds_remaining = str(self.seconds % 60)
            if len(seconds_remaining) < 2:
                seconds_remaining = '0' + seconds_remaining
        else:
            seconds_remaining = '00'

        time_remaining = '0' + minutes_remaining + ':' + seconds_remaining
        return time_remaining

    def update_time(self):
        """
        This simple function just sets the time_var to the return value of
        the time as string func
        :return: none, changes time_var directly
        """
        self.time_var.set(self.time_as_string())

    def update_correct_words_list(self, word):
        """
        This simple function receives a word and adds it to the listbox of
        the correct words, which immediately shows it to the user
        :param word: word to add to correct words
        :return: none, changes the listbox directly
        """
        self.correct_word_list_box.insert(END, word)

    def confirm_pressed(self):
        """
        This function is the function that the confirm button directs to,
        it changes the confirm_button_request flag to True, which is then
        handled by gameplay
        :return: none, changes the flag directly
        """
        self.confirm_button_request = True

    def time_is_up_message_box(self):
        """
        This function is called when the time runs out on the game and
        creates a yes/no message box which asks the user whether they'd
        like to play again.
        :return: True if user pressed yes, False if user pressed no
        """
        user_answer = messagebox.askyesno('Time is up!',
                                          'Your time is up! Your score is ' +
                                          self.current_score_label.cget("text")
                                          + ', Would you like to play again?')
        return user_answer

    def clear(self):
        """
        This function is the function that the clear button directs to,
        it changes the clear_button_request flag to True, which is then
        handled by gameplay.
        :return: none, changes the flag directly.
        """
        self.clear_button_request = True
