"""Implements the operators for bimodal logic in the model checker.

This module provides implementations of various logical operators used in bimodal logic,
which combines temporal and modal reasoning. The operators are organized into several
categories based on their semantic role:

Extensional Operators:
    - NegationOperator (¬): Logical negation
    - AndOperator (∧): Logical conjunction 
    - OrOperator (∨): Logical disjunction
    - ConditionalOperator (→): Material implication (defined)
    - BiconditionalOperator (↔): Material biconditional (defined)

Extremal Operators:
    - BotOperator (⊥): Logical contradiction/falsity
    - TopOperator (⊤): Logical tautology/truth (defined)

Modal Operators:
    - NecessityOperator (□): Truth in all possible worlds
    - DefPossibilityOperator (◇): Truth in at least one possible world (defined)

Temporal Operators:
    - FutureOperator (⏵): Truth at all future times
    - PastOperator (⏴): Truth at all past times
    - NextOperator: Truth at the "next" time in a history 
    - PreviousOperator: Truth at the "previous" time in a history 
    --Until 
    --Since
    --PreProg
    --Pastprog
    - DefFutureOperator: Possibility of future truth (defined)
    - DefPastOperator: Possibility of past truth (defined)

All operators adhere to a fail-fast philosophy, raising explicit errors when
required data is missing or invalid rather than attempting fallbacks.
"""
import z3

from model_checker import syntactic
from model_checker.utils import pretty_set_print
##############################################################################
############################ EXTENSIONAL OPERATORS ###########################
##############################################################################

class NegationOperator(syntactic.Operator):
    """Logical negation operator that inverts the truth value of its argument.
    
    This operator implements classical logical negation (¬). When applied to a formula A,
    it returns true when A is false and false when A is true.
    
    Key Properties:
        - Involutive: ¬¬A ≡ A
        - Preserves excluded middle: A ∨ ¬A is a tautology
        - Preserves non-contradiction: ¬(A ∧ ¬A) is a tautology
        - Truth-functional: Value depends only on truth value of argument
        
    Example:
        If p means "it's raining", then ¬p means "it's not raining"
    """

    name = "\\neg"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is false.
        
        Args:
            argument: The argument to negate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        return self.semantics.false_at(argument, eval_point)

    def false_at(self, argument, eval_point):
        """Returns false if argument is true.
        
        Args:
            argument: The argument to negate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        return self.semantics.true_at(argument, eval_point)

    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for the negation of an argument.
        
        Args:
            argument: The argument to negate
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where the true and false times are swapped from the argument's extension
        """
        new_truth_condition = {}
        for world_id, temporal_profile in argument.proposition.extension.items():
            true_times, false_times = temporal_profile
            new_truth_condition[world_id] = (false_times, true_times)
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class AndOperator(syntactic.Operator):
    """Logical conjunction operator that returns true when both arguments are true.
    
    This operator implements classical logical conjunction (∧). When applied to formulas
    A and B, it returns true when both A and B are true, and false otherwise.
    
    Key Properties:
        - Commutative: A ∧ B ≡ B ∧ A
        - Associative: (A ∧ B) ∧ C ≡ A ∧ (B ∧ C)
        - Identity: A ∧ ⊤ ≡ A
        - Annihilator: A ∧ ⊥ ≡ ⊥
        - Idempotent: A ∧ A ≡ A
        - Truth-functional: Value depends only on truth values of arguments
        
    Example:
        If p means "it's raining" and q means "it's cold", then (p ∧ q) means 
        "it's raining and it's cold"
    """

    name = "\\wedge"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Returns true if both arguments are true.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.And(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if either argument is false.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.Or(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for the conjunction of two arguments.
        
        Args:
            leftarg: The left argument of the conjunction
            rightarg: The right argument of the conjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where true_times are the intersection of both arguments' true times,
                 and false_times are the union of both arguments' false times
        """
        leftarg_truth_condition = leftarg.proposition.extension
        rightarg_truth_condition = rightarg.proposition.extension
        new_truth_condition = {}
        
        for world_id, temporal_profile in leftarg_truth_condition.items():
            left_true_times, left_false_times = temporal_profile
            right_true_times, right_false_times = rightarg_truth_condition[world_id]
            
            # Find intersection while preserving order from left_true_times
            new_true_times = [t for t in left_true_times if t in right_true_times]
            
            # Find union while preserving order and removing duplicates
            new_false_times = sorted(set(left_false_times) | set(right_false_times))
            
            new_truth_condition[world_id] = (new_true_times, new_false_times)
            
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class OrOperator(syntactic.Operator):
    """Logical disjunction operator that returns true when at least one argument is true.
    
    This operator implements classical logical disjunction (∨). When applied to formulas
    A and B, it returns true when either A or B (or both) are true, and false otherwise.
    
    Key Properties:
        - Commutative: A ∨ B ≡ B ∨ A
        - Associative: (A ∨ B) ∨ C ≡ A ∨ (B ∨ C)
        - Identity: A ∨ ⊥ ≡ A
        - Annihilator: A ∨ ⊤ ≡ ⊤
        - Idempotent: A ∨ A ≡ A
        - Truth-functional: Value depends only on truth values of arguments
        
    Example:
        If p means "it's raining" and q means "it's cold", then (p ∨ q) means 
        "it's raining or it's cold (or both)"
    """

    name = "\\vee"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        """Returns true if either argument is true.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.Or(
            semantics.true_at(leftarg, eval_point),
            semantics.true_at(rightarg, eval_point)
        )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if both arguments are false.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        return z3.And(
            semantics.false_at(leftarg, eval_point),
            semantics.false_at(rightarg, eval_point)
        )

    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for the disjunction of two arguments.
        
        Args:
            leftarg: The left argument of the disjunction
            rightarg: The right argument of the disjunction
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where true_times are the union of both arguments' true times,
                 and false_times are the intersection of both arguments' false times
        """
        leftarg_truth_condition = leftarg.proposition.extension
        rightarg_truth_condition = rightarg.proposition.extension
        new_truth_condition = {}
        
        for world_id, temporal_profile in leftarg_truth_condition.items():
            left_true_times, left_false_times = temporal_profile
            right_true_times, right_false_times = rightarg_truth_condition[world_id]
            
            # Find union of true times
            new_true_times = sorted(set(left_true_times) | set(right_true_times))
            
            # Find intersection of false times
            new_false_times = [t for t in left_false_times if t in right_false_times]
            
            new_truth_condition[world_id] = (new_true_times, new_false_times)
            
        return new_truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


##############################################################################
############################## EXTREMAL OPERATORS ############################
##############################################################################

class BotOperator(syntactic.Operator):
    """Bottom element of the space of propositions is false at all worlds and times.
    
    This operator implements logical falsity (⊥). It evaluates to false at every world
    and time point in the model structure.
    
    Key Properties:
        - Always evaluates to false regardless of context
        - Identity element for disjunction: ⊥ ∨ A ≡ A
        - Annihilator for conjunction: ⊥ ∧ A ≡ ⊥
        - Negation gives top: ¬⊥ ≡ ⊤
        
    Example:
        ⊥ represents a logical contradiction like "it's raining and not raining"
    """

    name = "\\bot"
    arity = 0

    def true_at(self, eval_point):
        """Returns true if world state != itself (always false)."""
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state != world_state

    def false_at(self, eval_point):
        """Returns true if world state == itself (always true)."""
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        # Get the world array from the world ID
        world_array = self.semantics.world_function(eval_world)
        world_state = z3.Select(world_array, eval_time)
        return world_state == world_state

    def find_truth_condition(self, eval_point):
        """Returns the extension where all times are false at all worlds.
        
        Args:
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where for each world, no times are true and all times are false
        """
        return self.semantics.all_false

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)



##############################################################################
############################## MODAL OPERATORS ###############################
##############################################################################

class NecessityOperator(syntactic.Operator):
    """Modal operator that evaluates whether a formula holds in all possible worlds.

    This operator implements 'it is necessary that'. It evaluates whether its argument
    holds in all possible worlds at the current time.

    Key Properties:
        - Evaluates truth across all possible worlds at the current time
        - Returns true only if the argument is true in ALL possible worlds
        - Returns false if there exists ANY possible world where the argument is false
        - Dual of possibility: □A ≡ ¬◇¬A
        - Only considers worlds within the valid model structure

    Methods:
        true_at: Returns true if argument holds in all possible worlds
        false_at: Returns true if argument fails in some possible world
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different possible worlds

    Example:
        If p means "it's raining", then □p means "it is necessarily raining"
        (true in all possible worlds at the current time).
    """
    name = "\\Box"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true in all possible worlds at the eval_time."""
        semantics = self.semantics
        
        # Extract time from eval_point
        eval_time = eval_point["time"]
        
        # The argument must be true in all worlds at the eval_time
        other_world = z3.Int('nec_true_world')
        # For any other_world
        return z3.ForAll(
            other_world,
            z3.Implies(
                z3.And(
                    # If other_world is a valid world
                    semantics.is_world(other_world),
                    # And eval_time is in other_world
                    semantics.is_valid_time_for_world(other_world, eval_time),
                ),
                # Then the argument is true in other_world at the eval_time
                semantics.true_at(argument, {"world": other_world, "time": eval_time})
            )
        )

    def false_at(self, argument, eval_point):
        """Returns true if argument is false in any possible worlds at the eval_time."""
        semantics = self.semantics
        
        # Extract time from eval_point
        eval_time = eval_point["time"]
        
        # The argument must be false in some world at the eval_time
        other_world = z3.Int('nec_true_world')
        # There is some other_world
        return z3.Exists(
            other_world,
            z3.And(
                # Where other_world is a valid world
                semantics.is_world(other_world),
                # And eval_time is in other_world
                semantics.is_valid_time_for_world(other_world, eval_time),
                # And the argument is false in other_world at the eval_time
                semantics.false_at(argument, {"world": other_world, "time": eval_time})
            )
        )

    # TODO: should this use eval_point?
    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for: 'It is necessary that: argument'.
        
        Args:
            argument: The argument to apply necessity to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context (not used)
                - "time": The time for evaluation context (not used)
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs.
                 Box A is true at test_time in current_world if:
                 - A is true in any_world in all_worlds at the test_time.
                 And false otherwise.
        """
        semantics = argument.proposition.model_structure.semantics
        all_worlds = argument.proposition.model_structure.world_arrays.keys()
        argument_extension = argument.proposition.extension
        # Initialize result dictionary to eventually return
        new_truth_condition = {}

        # For each world in the model
        for current_world in all_worlds:
            # Get the time interval for this world
            start_time, end_time = semantics.world_time_intervals[current_world]
            # Generate a list of all valid times for this world
            world_time_interval = list(range(start_time, end_time + 1))
            # # Skip worlds that do not include the eval_time
            # if eval_time not in world_time_interval:
            #     continue
            # Initialize lists to store times when necessity is true/false
            true_times, false_times = [], []

            # For each time point in this world's interval
            for test_time in world_time_interval:
                # Check if argument is false at this time in any possible world
                is_false_in_some_world = any(
                    test_time in argument_extension[any_world][1]
                    for any_world in all_worlds
                )
                # If false in any world
                if is_false_in_some_world:
                    # Then the necessity is false at this time
                    false_times.append(test_time)
                else:
                    # Otherwise the necessity is true at this time
                    true_times.append(test_time)

            # Store the temporal profile for this world
            new_truth_condition[current_world] = (true_times, false_times)

        # Return result dictionary
        return new_truth_condition
            
    def print_method(self, argument, eval_point, indent_num, use_colors):
        """Print the modal operator and its argument across all possible worlds.
        """
        # Get the model structure and all world IDs
        model_structure = argument.proposition.model_structure
        
        # Get all worlds (IDs) for evaluation
        all_worlds = list(model_structure.world_arrays.keys())
        
        # Pass the worlds to print_over_worlds
        self.print_over_worlds(argument, eval_point, all_worlds, indent_num, use_colors)
   


##############################################################################
############################## TENSE OPERATORS ###############################
##############################################################################

class FutureOperator(syntactic.Operator):
    """Temporal operator that evaluates whether a formula holds at all future times.

    This operator implements the 'it will always be the case that'. It evaluates
    whether its argument holds at all future times within the eval_world (after the present).

    Key Properties:
        - Evaluates truth across all future times in the current world
        - Returns true only if the argument is true at ALL future times
        - Returns false if there exists ANY future time where the argument is false
        - Vacuously true if there are no future times (e.g., at the end of the timeline)
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds at all future times
        false_at: Returns true if argument fails at some future time
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ⏵p means "it will always be raining"
        (from all times after the preset).
    """
    name = "\\Future"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true at all future times in this world's interval."""
        semantics = self.semantics
        
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        future_time = z3.Int('future_true_time')
        return z3.ForAll(
            future_time,
            z3.Implies(
                z3.And(
                    # Time is within the valid range for this world's interval
                    semantics.is_valid_time_for_world(eval_world, future_time),
                    # Time is in the future of eval_time
                    eval_time < future_time,
                ),
                # Then the argument is true in the eval_world at the future_time
                semantics.true_at(argument, {"world": eval_world, "time": future_time}),
            )
        )
    
    def false_at(self, argument, eval_point):
        """Returns true if argument is false at at least one future time in this world's interval.
        
        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        future_time = z3.Int('future_false_time')
        return z3.Exists(
            future_time,
            z3.And(
                # Time is within the valid range for this world's interval
                semantics.is_valid_time_for_world(eval_world, future_time),
                # Time is in the future of eval_time
                eval_time < future_time,
                # And the argument is true in the eval_world at the future_time
                semantics.false_at(argument, {"world": eval_world, "time": future_time}),
            )
        )
    
    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for 'It will always be the case that: argument'.
        
        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if the argument is true in all
                 future times and the time is in the false_times otherwise
                 
        Raises:
            KeyError: If world_time_intervals information is missing for a required world_id.
                      This follows the fail-fast philosophy to make errors explicit.
        """
        model_structure = argument.proposition.model_structure
        semantics = model_structure.semantics
        argument_extension = argument.proposition.extension
        truth_condition = {}
        
        # For any current_world with a temporal_profile of true and false times
        for current_world, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            
            # Start with empty lists for past/future times
            new_true_times, new_false_times = [], []
            
            # Find the time_interval for the current_world
            start_time, end_time = semantics.world_time_intervals[current_world]
            time_interval = list(range(start_time, end_time + 1))
            
            # Calculate which times the argument always will be true
            for time_point in time_interval:

                # Check if there are any world_times strictly after this time_point
                has_future_times = any(any_time > time_point for any_time in time_interval)
                
                # If there are no future times in this world's interval, the Future operator is vacuously true
                if not has_future_times:
                    new_true_times.append(time_point)
                    continue
                    
                # Find all false times that are after this time point
                future_false_times = [
                    any_time
                    for any_time in false_times
                    if any_time > time_point
                    and any_time in time_interval
                ]
                
                # If there are no false times in the future
                if not future_false_times:
                    # Add time_point to the new_true_times
                    new_true_times.append(time_point)
                else:
                    # Otherwise add time_point to the new_false_times
                    new_false_times.append(time_point)
            
            # Store the results for this world_id
            truth_condition[current_world] = (new_true_times, new_false_times)

        # Return result dictionary
        return truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class PastOperator(syntactic.Operator):
    """Temporal operator that evaluates whether an argument holds at all past times.

    This operator implements the 'it has always been the case that'. It evaluates
    whether its argument is true at all past times within the eval_world (before the present).

    Key Properties:
        - Evaluates truth across all past times in the current world
        - Returns true only if the argument is true at ALL past times
        - Returns false if there exists ANY past time where the argument is false
        - Vacuously true if there are no past times (e.g., at the start of the timeline)
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds at all past times
        false_at: Returns true if argument fails at some past time
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ⏴p means "it has always been raining"
        (from all times before the present).
    """

    name = "\\Past"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true at all past times in this world's interval.
        
        Args:
            argument: The argument to apply the past operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        past_time = z3.Int('past_true_time')
        return z3.ForAll(
            past_time,
            z3.Implies(
                z3.And(
                    # If the past_time is within the eval_world's time interval
                    semantics.is_valid_time_for_world(eval_world, past_time),
                    # And the past_time is before the eval_time
                    past_time < eval_time,
                ),
                # Then the argument is true at the past_time in the eval_world
                semantics.true_at(argument, {"world": eval_world, "time": past_time}),
            )
        )
    
    def false_at(self, argument, eval_point):
        """Returns true if argument is false at at least one past time in this world's interval.
        
        Args:
            argument: The argument to apply the past operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """
        semantics = self.semantics
        
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        past_time = z3.Int('past_false_time')
        return z3.Exists(
            past_time,
            z3.And(
                # The past_time is within the eval_world's time interval
                semantics.is_valid_time_for_world(eval_world, past_time),
                # The past_time is before the eval_time
                past_time < eval_time,
                # And the argument is true at the past_time in the eval_world
                semantics.false_at(argument, {"world": eval_world, "time": past_time}),
            )
        )
    
    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for 'It has always been the case that: argument'.
        
        Args:
            argument: The argument to apply the past operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if the argument is true in all
                 past times and the time is in the false_times otherwise
                 
        Raises:
            KeyError: If world_time_intervals information is missing for a world_id.
                     This follows the fail-fast philosophy to make errors explicit.
        """
        model_structure = argument.proposition.model_structure
        semantics = model_structure.semantics
        argument_extension = argument.proposition.extension
        truth_condition = {}
        
        # For any current_world with a temporal_profile of true and false times
        for current_world, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            
            # Start with empty lists for past/future times
            new_true_times, new_false_times = [], []
            
            # Find the time_interval for the current_world
            start_time, end_time = semantics.world_time_intervals[current_world]
            time_interval = list(range(start_time, end_time + 1))
            
            # Calculate which times the argument always has been true
            for time_point in time_interval:

                # Check if there are any world_times strictly before this time_point
                has_past_times = any(any_time < time_point for any_time in time_interval)
                
                # If there are no past times in this world's interval, the Past operator is vacuously true
                if not has_past_times:
                    new_true_times.append(time_point)
                    continue
                    
                # Find all false times that are before this time point
                past_false_times = [
                    any_time
                    for any_time in false_times
                    if any_time < time_point
                    and any_time in time_interval
                ]
                
                # If there are no false times in the past
                if not past_false_times:
                    # Add time_point to the new_true_times
                    new_true_times.append(time_point)
                else:
                    # Otherwise add time_point to the new_false_times
                    new_false_times.append(time_point)
            
            # Store the results for this world_id
            truth_condition[current_world] = (new_true_times, new_false_times)

        # Return result dictionary
        return truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the sentence over all time points.
        
        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)

class NextOperator(syntactic.Operator):
    """Temporal operator that evaluates whether an argument holds at the "next" time in a history. 

    This operator implements the "Next it will be the case that..." It evaluates
    whether its argument is true at the "next" time in a history. 

    Key Properties:
        - Evaluates the truth value of a formula and the successive time in a history.
        --Returns true if the formula is true at the next time. 
        --Returns false if the formula is false at the next time. 
        - Vacuously true if there is no "next" time. 
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds at the next time
        false_at: Returns true if argument fails at the next time
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ∘p means "it will rain at the next time"
        . More colloquially, it might mean "it will rain tomorrow." 
    """

    name = "\\Next"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true at the time of evaluation plus one. 
        
        Args:
            argument: The argument to apply the next operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        #define "next time" variable
        next_time = eval_time + 1
        next_point = {"world": eval_world, "time": next_time}

        return z3.And(
                
            #Time is within the valid range for this world's interval
            semantics.is_valid_time_for_world(eval_world, next_time),

            #Formula is true at next time in world 
            semantics.true_at(argument, next_point)
            )

    def false_at(self, argument, eval_point):
        """Returns true if argument is false at the "next" time in the world's time interval. 
        
        Args:
            argument: The argument to apply the next operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics

        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        #define "next time" variable
        next_time = eval_time + 1
        next_point = {"world": eval_world, "time": next_time}

        return z3.And(
                # Time is within the valid range for this world's interval
                semantics.is_valid_time_for_world(eval_world, next_time),

                #Formula is false at the next time in world 
                semantics.false_at(argument, next_point),
            )
    
    def find_truth_condition(self, argument, eval_world, eval_time):
        """Gets truth-condition for 'Next it will be the case that'.
        
        Args:
            argument: The argument to apply the next operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if the argument is true in all
                 past times and the time is in the false_times otherwise
                 
        Raises:
            KeyError: If world_time_intervals information is missing for a world_id.
                     This follows the fail-fast philosophy to make errors explicit.
        """
        model_structure = argument.proposition.model_structure
        semantics = model_structure.semantics
        argument_extension = argument.proposition.extension
        truth_condition = {}
        
        # For any current_world with a temporal_profile of true and false times
        for current_world, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            
            # Start with empty lists for past/future times
            new_true_times, new_false_times = [], []
            
            # Find the time_interval for the current_world
            start_time, end_time = semantics.world_time_intervals[current_world]
            time_interval = list(range(start_time, end_time + 1))
            
            # Calculate which times the argument is next true 
            for time_point in time_interval:

                # Check if there are any world_times strictly after this time_point
                has_future_times = any(any_time > time_point for any_time in time_interval)
                
                # If there are no future times in this world's interval, the Next operator is vacuously true
                if not has_future_times:
                    new_true_times.append(time_point)
                    continue
                    
                # Find the next time from each time point 
                next_false_times=[
                    any_time
                    for any_time in false_times 
                    if any_time==(time_point + 1)
                    and any_time in time_interval 
                ]

                # If the argument is not false at the next time, consider it true now 
                if not next_false_times:
                    # Add time_point to the new_true_times
                    new_true_times.append(time_point)
                else:
                    # Otherwise add time_point to the new_false_times
                    new_false_times.append(time_point)
            
            # Store the results for this world_id
            truth_condition[current_world] = (new_true_times, new_false_times)

        # Return result dictionary
        return truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the sentence over all time points.
        
        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
        all_times = sentence_obj.proposition.model_structure.all_times
        self.print_over_times(sentence_obj, eval_point, all_times, indent_num, use_colors)

class PreviousOperator(syntactic.Operator):
    """Temporal operator that evaluates whether an argument holds at the "previous" time in a history. 

    This operator implements the "Previously it was the case that.." It evaluates
    whether its argument is true at the "next" time in a history. 

    Key Properties:
        - Evaluates the truth value of a formula and the previous time in a history.
        --Returns true if the formula is true at the previous time. 
        --Returns false if the formula is false at the previous time. 
        - Vacuously true if there is no "previous" time. 
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds at the previous time
        false_at: Returns true if argument fails at the previous time
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ∘p means "it will rain at the next time"
        . More colloquially, it might mean "it will rain tomorrow." 
    """

    name = "\\Previous"
    arity = 1

    def true_at(self, argument, eval_point):
        """Returns true if argument is true at the time of evaluation plus one. 
        
        Args:
            argument: The argument to apply the next operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics

        #Extract world and time from eval_point
        eval_world=eval_point["world"]
        eval_time=eval_point["time"]

        #Define "previous time" variable
        previous_time = eval_time -1
        previous_point = {"world": eval_world, "time": previous_time}

        return z3.And(
                
            #Time is within the valid range for this world's interval
            semantics.is_valid_time_for_world(eval_world, previous_time),

            #Formula is true at next time in world 
            semantics.true_at(argument, previous_point)
            )


    def false_at(self, argument, eval_point):
        """Returns true if argument is false at the "next" time in the world's time interval. 
        
        Args:
            argument: The argument to apply the next operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics

        #Extract world and time from eval_point
        eval_world=eval_point["world"]
        eval_time=eval_point["time"]

        #Define "previous time" variable
        previous_time = eval_time -1
        previous_point = {"world": eval_world, "time": previous_time}

        return z3.And(
                
            #Time is within the valid range for this world's interval
            semantics.is_valid_time_for_world(eval_world, previous_time),

            #Formula is false at previous time in world 
            semantics.false_at(argument, previous_point)
            )


    
    def find_truth_condition(self, argument, eval_point):
        """Gets truth-condition for 'Previously it was the case that'.
        
        Args:
            argument: The argument to apply the previous operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if the argument is true in all
                 past times and the time is in the false_times otherwise
                 
        Raises:
            KeyError: If world_time_intervals information is missing for a world_id.
                     This follows the fail-fast philosophy to make errors explicit.
        """
        model_structure = argument.proposition.model_structure
        semantics = model_structure.semantics
        argument_extension = argument.proposition.extension
        truth_condition = {}
        
        # For any current_world with a temporal_profile of true and false times
        for current_world, temporal_profile in argument_extension.items():
            true_times, false_times = temporal_profile
            
            # Start with empty lists for past/future times
            new_true_times, new_false_times = [], []
            
            # Find the time_interval for the current_world
            start_time, end_time = semantics.world_time_intervals[current_world]
            time_interval = list(range(start_time, end_time + 1))
            
            # Calculate which times the argument always has been true
            for time_point in time_interval:

                # Check if there are any world_times strictly before this time_point
                has_past_times = any(any_time < time_point for any_time in time_interval)
                
                # If there are no past times in this world's interval, the Previous operator is vacuously true
                if not has_past_times:
                    new_true_times.append(time_point)
                    continue
                    
                # Find the previous time from each time point 
                previous_false_times=[
                    any_time
                    for any_time in false_times 
                    if any_time==(time_point -1)
                    and any_time in time_interval 
                ]

                # If the argument is not false at the previous time, consider it true now 
                if not previous_false_times:
                    # Add time_point to the new_true_times
                    new_true_times.append(time_point)
                else:
                    # Otherwise add time_point to the new_false_times
                    new_false_times.append(time_point)
            
            # Store the results for this world_id
            truth_condition[current_world] = (new_true_times, new_false_times)

        # Return result dictionary
        return truth_condition
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the sentence over all time points.
        
        Args:
            sentence_obj: The sentence to print
            eval_point: The evaluation point (world ID and time)
            indent_num: The indentation level
            use_colors: Whether to use colors in output
        """
        all_times = sentence_obj.proposition.model_structure.all_times
        self.print_over_times(sentence_obj, eval_point, all_times, indent_num, use_colors)

class UntilOperator(syntactic.Operator):
    """Temporal operator that takes two arguments in the same world but which may differ in time. 
    The operator evaluates whether the left operator i). is true and 
    ii). is true at all points in between itself and the time in the right argument. 

    This operator implements the 'x will be the case until y'. It evaluates
    whether its argument holds at all future times within the eval_world (after the present).

    Key Properties:
        - Evaluates truth across at the left argument and at all times between the left and right argument.
        - Returns true only if the left argument is true at ALL times in between the left and right argument. 
        - Returns false if there exists ANY time in between both arguments where p is false. 
        - Vacuously true if the right argument is never true. 
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds i). at the left argument, ii). that the right argument holds at some point in the future, and iii). that the left argument holds at all points between the left and right point. 
        false_at: Returns true if the argument fails to hold at any point in time between the time of the left and the time of the right argument. 
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it rains" and q means "it snows" then p U q means "it rains until it snows" 
    """
    name = "\\Until"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        
        """
        Returns true if the left argument is true at all times from eval_time up to (but not including) the time
        when the right argument becomes true. The right argument must eventually be true.
        """
        semantics = self.semantics
        
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        some_time = z3.Int('some_time')
        t = z3.Int('t')
        
        some_point = {"world": eval_world, "time": some_time}
        mid_point = {"world": eval_world, "time": t}
        
        return z3.Exists(
            some_time,

            z3.And(
                semantics.is_valid_time_for_world(some_time),
                eval_time < some_time,
                semantics.true_at(rightarg, some_point),

            z3.ForAll(
                t,
                z3.Implies(
                    z3.And(
                        semantics.is_valid_time_for_world(t),
                        eval_time <= t,
                        t < some_time
                    ),
                    semantics.true_at(leftarg, mid_point)
                )
            )
        )
    )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if argument is false at at least one future time in this world's interval.
        
        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """

        """Returns true if argument is true at all future times in this world's interval."""
        semantics = self.semantics
        
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        some_time = z3.Int('some_time')
        t = z3.Int('t')
        
        some_point = {"world": eval_world, "time": some_time}
        mid_point = {"world": eval_world, "time": t}
        
        # If there exists a future time where rightarg is true, but some point between now and that time where leftarg is false
        return z3.Exists(
            some_time,
            z3.And(
                semantics.is_valid_time_for_world(some_time),
                eval_time < some_time,
                semantics.true_at(rightarg, some_point),
            z3.Exists(
                t,
                z3.And(
                    semantics.is_valid_time_for_world(t),
                    eval_time <= t,
                    t < some_time,
                    semantics.false_at(leftarg, mid_point)
                )
            )
        )
    )
    
    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for 'leftarg will be the case until rightarg'.
        
        Args:
            leftarg: the event which will hold until right arg 
            rightarg: some future time which orders leftarg, all times between which leftarg will hold. 
            eval_point: Dictionary containing evaluation parameters for leftarg:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if it is true for all times ordered by the  right argument 
                 and the time is in the false_times otherwise
                 
        Raises:
            KeyError: If world_time_intervals information is missing for a required world_id.
                      This follows the fail-fast philosophy to make errors explicit.
        """
        """
        Computes the times in each world where 'leftarg U rightarg' is true or false.
        
        Returns:
        dict: {world_id: (true_times, false_times)}
        """

        """Evaluates the 'p Until q' truth condition over all times in each world."""
        #Get Semantics
        semantics = self.semantics

        #LeftArg and RightArg should have the same model structure
        model_structure = leftarg.proposition.model_structure

        #Define truth conditions for leftarg and rightarg 
        leftarg_truth = leftarg.proposition.extension
        rightarg_truth = rightarg.proposition.extension

        #initialize new truth conditions
        new_truth_condition = {}

        #checks to make sure rightarg and leftarg contianed in the same word 
        for world_id, (left_true_times, left_false_times) in leftarg_truth.items():
            if world_id not in rightarg_truth:
                raise KeyError(f"Missing truth condition for world_id {world_id} in rightarg")

            #checks to see arguments are in the world's times 
            right_true_times, _ = rightarg_truth[world_id]
            if world_id not in semantics.world_time_intervals:
                raise KeyError(f"Missing world_time_intervals for world_id {world_id}")

            #defines start and end variables as world intervals 
            start_time, end_time = semantics.world_time_intervals[world_id]

            #generates list of all times between start and end variables 
            time_interval = list(range(start_time, end_time + 1))

            #initialize true and false times 
            true_times = []
            false_times = []

            #for each time in the time interval 
            for t in time_interval:
                
                #initialize check 
                satisfied = False

                #for each time in between the defined time interval 
                for t_prime in range(t + 1, end_time + 1):

                    #if rightarg is true at that time 
                    if t_prime in right_true_times:

                        #check to see if all points in between that time and the first time are true 
                        if all(t_mid in left_true_times for t_mid in range(t, t_prime)):

                            #if yes, check
                            satisfied = True

                            #break to save space complexity 
                            break
                
                #if a candidate interval was found, add to "true times" of until 
                if satisfied:
                    true_times.append(t)

                #otherwise add to false times 
                else:
                    false_times.append(t)

            #define truth conditions for until 
            new_truth_condition[world_id] = (true_times, false_times)

        #return 
        return new_truth_condition

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
class SinceOperator(syntactic.Operator):
    """Temporal operator that takes two arguments in the same world but which may differ in time. 
    The operator evaluates whether the left operator i). is true and 
    ii). is true at all points in between itself and the time in the right argument, in which that time is in the past . 

    This operator implements the 'x will be the case until y'. It evaluates
    whether its argument holds at all future times within the eval_world (after the present).

    Key Properties:
        - Evaluates truth across at the left argument and at all times between the left and right argument.
        - Returns true only if the left argument is true at ALL times in between the left and right argument. 
        - Returns false if there exists ANY time in between both arguments where p is false. 
        - Vacuously true if the right argument is never true. 
        - Only considers times within the valid interval for the current world

    Methods:
        true_at: Returns true if argument holds i). at the left argument, ii). that the right argument holds at some point in the future, and iii). that the left argument holds at all points between the left and right point. 
        false_at: Returns true if the argument fails to hold at any point in time between the time of the left and the time of the right argument. 
        find_truth_condition: Computes temporal profiles for all worlds
        print_method: Displays evaluation across different time points

    Example:
        If p means "it rains" and q means "it snows" then p U q means "it rains until it snows" 
    """
    name = "\\Since"
    arity = 2

    def true_at(self, leftarg, rightarg, eval_point):
        
        """
        Returns true if the left argument is true at all times from eval_time up to (but not including) the time
        when the right argument becomes true. The right argument must eventually be true.
        """
        semantics = self.semantics
        
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        some_time = z3.Int('some_time')
        t = z3.Int('t')
        
        some_point = {"world": eval_world, "time": some_time}
        mid_point = {"world": eval_world, "time": t}
        
        return z3.Exists(
            some_time,

            z3.And(
                semantics.is_valid_time_for_world(some_time),
                eval_time > some_time,
                semantics.true_at(rightarg, some_point),

            z3.ForAll(
                t,
                z3.Implies(
                    z3.And(
                        semantics.is_valid_time_for_world(t),
                        eval_time >= t,
                        t > some_time
                    ),
                    semantics.true_at(leftarg, mid_point)
                )
            )
        )
    )

    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if argument is false at at least one future time in this world's interval.
        
        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """

        """Returns true if argument is true at all future times in this world's interval."""
        semantics = self.semantics
        
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        some_time = z3.Int('some_time')
        t = z3.Int('t')
        
        some_point = {"world": eval_world, "time": some_time}
        mid_point = {"world": eval_world, "time": t}
        
        # If there exists a future time where rightarg is true,
        # # but some point between now and that time where leftarg is false
        return z3.Exists(
            some_time,
            z3.And(
                semantics.is_valid_time_for_world(some_time),
                eval_time > some_time,
                semantics.true_at(rightarg, some_point),
            z3.Exists(
                t,
                z3.And(
                    semantics.is_valid_time_for_world(t),
                    eval_time >= t,
                    t > some_time,
                    semantics.false_at(leftarg, mid_point)
                )
            )
        )
    )
    
    def find_truth_condition(self, leftarg, rightarg, eval_point):
        """Gets truth-condition for 'leftarg will be the case until rightarg'.
        
        Args:
            leftarg: the event which will hold until right arg 
            rightarg: some future time which orders leftarg, all times between which leftarg will hold. 
            eval_point: Dictionary containing evaluation parameters for leftarg:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
            
        Returns:
            dict: A dictionary mapping world_ids to (true_times, false_times) pairs,
                 where a time is in the true_times if it is true for all times ordered by the  right argument 
                 and the time is in the false_times otherwise
                 
        Raises:
            KeyError: If world_time_intervals information is missing for a required world_id.
                      This follows the fail-fast philosophy to make errors explicit.
        """
        """
        Computes the times in each world where 'leftarg U rightarg' is true or false.
        
        Returns:
        dict: {world_id: (true_times, false_times)}
        """

           #Get Semantics
        semantics = self.semantics

        #LeftArg and RightArg should have the same model structure
        model_structure = leftarg.proposition.model_structure

        #Define truth conditions for leftarg and rightarg 
        leftarg_truth = leftarg.proposition.extension
        rightarg_truth = rightarg.proposition.extension

        #initialize new truth conditions
        new_truth_condition = {}

        #checks to make sure rightarg and leftarg contianed in the same word 
        for world_id, (left_true_times, left_false_times) in leftarg_truth.items():
            if world_id not in rightarg_truth:
                raise KeyError(f"Missing truth condition for world_id {world_id} in rightarg")

            #checks to see arguments are in the world's times 
            right_true_times, _ = rightarg_truth[world_id]
            if world_id not in semantics.world_time_intervals:
                raise KeyError(f"Missing world_time_intervals for world_id {world_id}")

            #defines start and end variables as world intervals 
            start_time, end_time = semantics.world_time_intervals[world_id]

            #generates list of all times between start and end variables 
            time_interval = list(range(start_time, end_time + 1))

            #initialize true and false times 
            true_times = []
            false_times = []

            #for each time in the time interval 
            for t in time_interval:
                
                #initialize check 
                satisfied = False

                #for each time in between the defined time interval 
                for t_prime in range(start_time, t):

                    #if rightarg is true at that time 
                    if t_prime in right_true_times:

                        #check to see if all points in between that time and the first time are true 
                        if all(t_mid in left_true_times for t_mid in range(t_prime + 1, t + 1)):


                            #if yes, check
                            satisfied = True

                            #break to save space complexity 
                            break
                
                #if a candidate interval was found, add to "true times" of until 
                if satisfied:
                    true_times.append(t)

                #otherwise add to false times 
                else:
                    false_times.append(t)

            #define truth conditions for until 
            new_truth_condition[world_id] = (true_times, false_times)

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)







##############################################################################
######################## DEFINED EXTENSIONAL OPERATORS #######################
##############################################################################

class ConditionalOperator(syntactic.DefinedOperator):
    """Material conditional operator that returns true unless the antecedent is true and consequent false.
    
    This operator implements classical material implication (→). When applied to formulas
    A and B, it returns true when either A is false or B is true, and false otherwise.
    
    Key Properties:
        - Defined as: A → B ≡ ¬A ∨ B
        - Vacuously true when antecedent is false
        - Truth-functional: Value depends only on truth values of arguments
        - Not equivalent to natural language "if-then"
        - Supports modus ponens: From A and A → B, infer B
        - Supports modus tollens: From ¬B and A → B, infer ¬A
        
    Example:
        If p means "it's raining" and q means "the ground is wet", then (p → q) means 
        "if it's raining then the ground is wet" (in the material sense)
    """

    name = "\\rightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        return [OrOperator, [NegationOperator, leftarg], rightarg]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)


class BiconditionalOperator(syntactic.DefinedOperator):
    """Material biconditional operator that returns true when both arguments have the same truth value.
    
    This operator implements classical material biconditional (↔). When applied to formulas
    A and B, it returns true when A and B have the same truth value (both true or both false).
    
    Key Properties:
        - Defined as: A ↔ B ≡ (A → B) ∧ (B → A)
        - Commutative: A ↔ B ≡ B ↔ A
        - Reflexive: A ↔ A is a tautology
        - Truth-functional: Value depends only on truth values of arguments
        - Not equivalent to natural language "if and only if"
        - Represents logical equivalence between formulas
        
    Example:
        If p means "it's raining" and q means "there are clouds", then (p ↔ q) means 
        "it's raining if and only if there are clouds" (in the material sense)
    """

    name = "\\leftrightarrow"
    arity = 2

    def derived_definition(self, leftarg, rightarg):  # type: ignore
        right_to_left = [ConditionalOperator, leftarg, rightarg]
        left_to_right = [ConditionalOperator, rightarg, leftarg]
        return [AndOperator, right_to_left, left_to_right]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition for sentence_obj, increases the indentation
        by 1, and prints both of the arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)



##############################################################################
####################### DEFINED EXTREMAL OPERATORS ###########################
##############################################################################

class TopOperator(syntactic.DefinedOperator):
    """Top element of the space of propositions is true at all worlds and times.
    
    This operator implements logical truth (⊤). It evaluates to true at every world
    and time point in the model structure.
    
    Key Properties:
        - Always evaluates to true regardless of context
        - Identity element for conjunction: ⊤ ∧ A ≡ A
        - Annihilator for disjunction: ⊤ ∨ A ≡ ⊤
        - Negation gives bottom: ¬⊤ ≡ ⊥
        
    Example:
        ⊤ represents a logical tautology like "it's raining or not raining"
    """

    name = "\\top"
    arity = 0

    def derived_definition(self):  # type: ignore
        """Define top in terms of negation and bottom."""
        return [NegationOperator, [BotOperator]]

    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Prints the proposition and its arguments."""
        self.general_print(sentence_obj, eval_point, indent_num, use_colors)



##############################################################################
####################### DEFINED INTENSIONAL OPERATORS ########################
##############################################################################

class DefPossibilityOperator(syntactic.DefinedOperator):
    """Modal operator that evaluates whether a formula holds in at least one possible world.

    This operator implements 'it is possible that'. It evaluates whether its argument
    holds in at least one possible world at the current time.

    Key Properties:
        - Evaluates truth across all possible worlds at the current time
        - Returns true if the argument is true in ANY possible world
        - Returns false if the argument is false in ALL possible worlds
        - Defined as the dual of necessity: ◇A ≡ ¬□¬A
        - Only considers worlds within the valid model structure

    Methods:
        derived_definition: Defines possibility in terms of negation and necessity
        print_method: Displays evaluation across different possible worlds

    Example:
        If p means "it's raining", then ◇p means "it is possible that it's raining"
        (true in at least one possible world at the current time).
    """
    name = "\\Diamond"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        """Define possibility in terms of negation and necessity."""
        return [NegationOperator, [NecessityOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print the possibility operator and its argument across all possible worlds.
        """
        # Get the model structure and all world IDs
        model_structure = sentence_obj.proposition.model_structure
        
        # Get all worlds (IDs) for evaluation
        all_worlds = list(model_structure.world_arrays.keys())
        
        # Pass the worlds to print_over_worlds
        self.print_over_worlds(sentence_obj, eval_point, all_worlds, indent_num, use_colors)



##############################################################################
######################### DEFINED TEMPORAL OPERATORS #########################
##############################################################################

class DefFutureOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula holds at some future time.

    This operator implements 'it will at some point be the case that'. It evaluates
    whether its argument is true at at least one future time within the eval_world
    (after the present).

    Key Properties:
        - Evaluates truth across all future times in the current world
        - Returns true if the argument is true at ANY future time
        - Returns false if the argument is false at ALL future times
        - Defined as the dual of future necessity: ⏵A ≡ ¬⏵¬A
        - Only considers times within the valid interval for the current world

    Methods:
        derived_definition: Defines future possibility in terms of negation and future necessity
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then ⏵p means "it will at some point be raining"
        (true at at least one future time).
    """

    name = "\\future"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [FutureOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class DefPastOperator(syntactic.DefinedOperator):

    name = "\\past"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [NegationOperator, [PastOperator, [NegationOperator, argument]]]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)

class PreProgOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula which  holds in the present held over the duration since it was not true. 
    It is meant to capture the intuitive truth conditions for the present progressive, e.g. "He is running for president," "He is learning to play the violin." 

    This operator implements the present progressive as  'it is the case and it is the case since it was not. '. 

    Key Properties:
        - Evaluates truth at present time and at times since it was not the case. 
        - Returns true if the argument is true at the present and at ALL times since it has not been the case
        - Returns false if the argument is false or it has not been false at all times since it has not been the case 
        - Only considers times within the valid interval for the current world

    Methods:
        derived_definition: Defines present progressive in terms of the metric Since Operator and conjunction
        print_method: Displays evaluation across different time points

    Example:
        If p means "it rains (now)" then tau(p) means "it is raining" 
        (true at at least one future time).
    """

    name = "\\PreProg"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
            return [AndOperator,  [UntilOperator, [NegationOperator, argument], argument],  argument, ]
            #change to Polish notation: operator, comma, argument 
          
        
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)


class PastProgOperator(syntactic.DefinedOperator):
    """Temporal operator that evaluates whether a formula held in the past and holds in the present since holding in the past. 
    It is meant to capture the intuitive truth conditions for the past progressive, e.g. "I have lost my wallet," "It has been raining"

    This operator implements the present progressive as  'it was the case and since it was the case, it is the case. '. 

    Key Properties:
        - Evaluates truth at present and past times
        - Returns true if the argument is true at the past (for the present) and that in the present it has been the case "since" it was the case in the past. 
        ------Note: This formalization risks evaluating pathological cases in which there was a gap between two true past times but no gap between the second past time and the present as true. Try to block. 
        - Returns false if the argument is false in the past or it has not been true at all times from the past to the present. 
        - Only considers times within the valid interval for the current world

    Methods:
        derived_definition: Defines past progressive in terms of the metric Since Operator and conjunction
        print_method: Displays evaluation across different time points

    Example:
        If p means "it's raining", then SGIMA(p) means "it has been raining"
        (true at at least one future time).
    """

    name = "\\PastProg"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [AndOperator,  [SinceOperator, [NegationOperator, argument], argument],  argument, ]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)





bimodal_operators = syntactic.OperatorCollection(
    # extensional operators
    NegationOperator,
    AndOperator,
    OrOperator,

    # extremal operators
    TopOperator,

    # modal operators
    NecessityOperator,

    # tense operators
    FutureOperator,
    PastOperator,
    NextOperator, 
    PreviousOperator, 
    UntilOperator, 
    SinceOperator, 

    # defined operators
    ConditionalOperator,
    BiconditionalOperator,
    BotOperator,
    DefPossibilityOperator,
    DefFutureOperator,
    DefPastOperator,
    PreProgOperator, 
    PastProgOperator, 
)

