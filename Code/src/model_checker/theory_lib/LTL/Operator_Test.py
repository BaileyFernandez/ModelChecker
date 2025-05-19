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

    name = "\\Preprog"
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

    name = "\\Pastprog"
    arity = 1

    def derived_definition(self, argument):  # type: ignore
        return [AndOperator,  [SinceOperator, [NegationOperator, argument], argument],  argument, ]
    
    def print_method(self, sentence_obj, eval_point, indent_num, use_colors):
        """Print temporal operator evaluation across different time points."""
        eval_world = eval_point["world"]
        eval_world_history = sentence_obj.proposition.model_structure.get_world_history(eval_world)
        eval_world_times = eval_world_history.keys()
        self.print_over_times(sentence_obj, eval_point, eval_world_times, indent_num, use_colors)
