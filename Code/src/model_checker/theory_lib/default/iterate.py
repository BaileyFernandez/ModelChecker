"""Default theory specific model iteration implementation.

This module provides the DefaultModelIterator implementation which handles:
1. Detecting differences between models using default theory semantics
2. Creating constraints to differentiate models with default theory primitives
3. Checking model isomorphism for default theory models
"""

import z3
import sys
import logging

from model_checker.iterate.core import BaseModelIterator
from model_checker.utils import bitvec_to_substates, pretty_set_print

# Configure logging
logger = logging.getLogger(__name__)
if not logger.handlers:
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter('[DEFAULT-ITERATE] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.WARNING)


class DefaultModelIterator(BaseModelIterator):
    """Model iterator for the default theory.
    
    This class extends BaseModelIterator with default theory-specific
    implementations of the abstract methods required for model iteration.
    It provides specialized difference detection, constraint generation,
    and visualization for default theory models.
    
    The default theory uses a state-based semantics with:
    - States represented as bit vectors
    - Verification and falsification as primitive relations
    - Possible worlds as maximal possible states
    - Part-whole relationships between states
    """
    
    def _calculate_differences(self, new_structure, previous_structure):
        """Calculate differences between two default theory model structures.
        
        For default theory, this focuses on:
        - Changes in which states are worlds
        - Changes in which states are possible
        - Changes in verification and falsification of sentence letters
        - Changes in part-whole relationships
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Structured differences between the models
        """
        # Try to use the theory-specific detect_model_differences method on the structure
        if hasattr(new_structure, 'detect_model_differences'):
            try:
                differences = new_structure.detect_model_differences(previous_structure)
                if differences:
                    return differences
            except Exception as e:
                logger.warning(f"Error in default theory difference detection: {e}")
        
        # Fall back to our own implementation
        differences = self._calculate_default_differences(new_structure, previous_structure)
        
        return differences
    
    def _calculate_default_differences(self, new_structure, previous_structure):
        """Default theory specific implementation of difference detection.
        
        This is more sophisticated than the base _calculate_basic_differences method
        as it understands default theory semantics like verifiers and falsifiers.
        
        Args:
            new_structure: The new model structure
            previous_structure: The previous model structure
            
        Returns:
            dict: Dictionary of differences with default theory semantics
        """
        # Get Z3 models
        new_model = new_structure.z3_model
        previous_model = previous_structure.z3_model
        
        # Initialize default theory-specific differences structure
        differences = {
            "worlds": {"added": [], "removed": []},
            "possible_states": {"added": [], "removed": []},
            "sentence_letters": {},
            "parthood": {}
        }
        
        # Compare worlds and possible states
        old_worlds = set(getattr(previous_structure, "z3_world_states", []))
        new_worlds = set(getattr(new_structure, "z3_world_states", []))
        
        # Find added/removed worlds
        for world in new_worlds:
            if world not in old_worlds:
                differences["worlds"]["added"].append(world)
        
        for world in old_worlds:
            if world not in new_worlds:
                differences["worlds"]["removed"].append(world)
        
        # Compare possible states
        old_states = set(getattr(previous_structure, "z3_possible_states", []))
        new_states = set(getattr(new_structure, "z3_possible_states", []))
        
        # Find added/removed possible states
        for state in new_states:
            if state not in old_states:
                differences["possible_states"]["added"].append(state)
        
        for state in old_states:
            if state not in new_states:
                differences["possible_states"]["removed"].append(state)
        
        # Compare verification and falsification for each sentence letter
        semantics = new_structure.semantics
        for letter in new_structure.sentence_letters:
            old_verifiers = []
            new_verifiers = []
            old_falsifiers = []
            new_falsifiers = []
            
            # Check verifiers
            for state in old_states.union(new_states):
                try:
                    # For previously possible states
                    if state in old_states:
                        if bool(previous_model.eval(semantics.verifies(letter, state), model_completion=True)):
                            old_verifiers.append(state)
                
                    # For currently possible states
                    if state in new_states:
                        if bool(new_model.eval(semantics.verifies(letter, state), model_completion=True)):
                            new_verifiers.append(state)
                            
                    # For falsifiers
                    if state in old_states:
                        if bool(previous_model.eval(semantics.falsifies(letter, state), model_completion=True)):
                            old_falsifiers.append(state)
                    
                    if state in new_states:
                        if bool(new_model.eval(semantics.falsifies(letter, state), model_completion=True)):
                            new_falsifiers.append(state)
                except Exception:
                    # Skip problematic states
                    pass
            
            # Only record differences if something changed
            old_verifiers_set = set(old_verifiers)
            new_verifiers_set = set(new_verifiers)
            old_falsifiers_set = set(old_falsifiers)
            new_falsifiers_set = set(new_falsifiers)
            
            added_verifiers = [state for state in new_verifiers if state not in old_verifiers_set]
            removed_verifiers = [state for state in old_verifiers if state not in new_verifiers_set]
            
            added_falsifiers = [state for state in new_falsifiers if state not in old_falsifiers_set]
            removed_falsifiers = [state for state in old_falsifiers if state not in new_falsifiers_set]
            
            if added_verifiers or removed_verifiers or added_falsifiers or removed_falsifiers:
                differences["sentence_letters"][str(letter)] = {
                    "old": (old_verifiers, old_falsifiers),
                    "new": (new_verifiers, new_falsifiers),
                    "verifiers": {
                        "added": added_verifiers,
                        "removed": removed_verifiers
                    },
                    "falsifiers": {
                        "added": added_falsifiers,
                        "removed": removed_falsifiers
                    }
                }
                
        # Compare part-whole relationships if available
        if hasattr(semantics, 'is_part_of'):
            all_states = list(old_states.union(new_states))
            for i, state1 in enumerate(all_states):
                for j, state2 in enumerate(all_states[i:], i):
                    # Skip identical states
                    if state1 == state2:
                        continue
                        
                    try:
                        # Check if part-whole relationship changed
                        old_parthood = False
                        new_parthood = False
                        
                        if state1 in old_states and state2 in old_states:
                            old_parthood = bool(previous_model.eval(semantics.is_part_of(state1, state2), model_completion=True))
                            
                        if state1 in new_states and state2 in new_states:
                            new_parthood = bool(new_model.eval(semantics.is_part_of(state1, state2), model_completion=True))
                            
                        if old_parthood != new_parthood:
                            state_pair = f"{state1},{state2}"
                            differences["parthood"][state_pair] = {
                                "old": old_parthood,
                                "new": new_parthood
                            }
                    except Exception:
                        # Skip problematic state pairs
                        pass
                
        return differences
    
    def _create_difference_constraint(self, previous_models):
        """Create default theory-specific constraints to differentiate models.
        
        This focuses on the key relationships in default theory:
        - Verification and falsification
        - Part-whole relationships
        - Possible states and worlds
        
        Args:
            previous_models: List of Z3 models to differ from
            
        Returns:
            z3.ExprRef: Z3 constraint requiring difference from previous models
        """
        logger.debug("Creating difference constraints for default theory")
        
        # Get key structures from build_example
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # For each previous model, create a constraint requiring at least one difference
        model_diff_constraints = []
        
        for prev_model in previous_models:
            # Focus on verification and falsification functions
            diff_components = []
            
            # 1. Differences in verification
            for letter in model_structure.sentence_letters:
                for state in model_structure.all_states:
                    try:
                        prev_value = prev_model.eval(semantics.verifies(letter, state), model_completion=True)
                        diff_components.append(semantics.verifies(letter, state) != prev_value)
                    except Exception:
                        pass
            
            # 2. Differences in falsification
            for letter in model_structure.sentence_letters:
                for state in model_structure.all_states:
                    try:
                        prev_value = prev_model.eval(semantics.falsifies(letter, state), model_completion=True)
                        diff_components.append(semantics.falsifies(letter, state) != prev_value)
                    except Exception:
                        pass
            
            # 3. Differences in part-whole relationships
            if hasattr(semantics, 'is_part_of'):
                for state1 in model_structure.all_states:
                    for state2 in model_structure.all_states:
                        try:
                            prev_value = prev_model.eval(semantics.is_part_of(state1, state2), model_completion=True)
                            diff_components.append(semantics.is_part_of(state1, state2) != prev_value)
                        except Exception:
                            pass
            
            # 4. Differences in possible states
            for state in model_structure.all_states:
                try:
                    prev_value = prev_model.eval(semantics.possible(state), model_completion=True)
                    diff_components.append(semantics.possible(state) != prev_value)
                except Exception:
                    pass
            
            # 5. Differences in worlds
            for state in model_structure.all_states:
                try:
                    prev_value = prev_model.eval(semantics.is_world(state), model_completion=True)
                    diff_components.append(semantics.is_world(state) != prev_value)
                except Exception:
                    pass
            
            # The new model must be different in at least one way
            if diff_components:
                model_diff_constraints.append(z3.Or(diff_components))
            
        # The new model must be different from ALL previous models
        if model_diff_constraints:
            return z3.And(model_diff_constraints)
        else:
            raise RuntimeError("Could not create any difference constraints for default theory")
    
    def _create_non_isomorphic_constraint(self, z3_model):
        """Create constraints that force structural differences for default theory.
        
        For default theory models, this focuses on:
        - Different patterns of verification/falsification
        - Different numbers of worlds and possible states
        - Different part-whole relationship patterns
        
        Args:
            z3_model: The Z3 model to differ from
        
        Returns:
            z3.ExprRef: Z3 constraint expression or None if creation fails
        """
        # Get model structure
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # Create constraints to force structural differences
        constraints = []
        
        # Try to force a different number of worlds
        try:
            # Count current worlds
            current_worlds = sum(1 for state in model_structure.all_states 
                               if bool(z3_model.eval(semantics.is_world(state), model_completion=True)))
            
            # Force either more or fewer worlds
            world_count = z3.Sum([z3.If(semantics.is_world(state), 1, 0) 
                                 for state in model_structure.all_states])
            
            if current_worlds > 1:
                constraints.append(world_count < current_worlds)
            
            if current_worlds < len(model_structure.all_states) - 1:
                constraints.append(world_count > current_worlds)
        except Exception as e:
            logger.debug(f"Error creating world count constraint: {e}")
        
        # Try to force different letter valuations
        try:
            for letter in model_structure.sentence_letters:
                # Force different verification pattern
                ver_count = z3.Sum([z3.If(semantics.verifies(letter, state), 1, 0) 
                                   for state in model_structure.all_states])
                
                # Count current verifiers
                current_ver = sum(1 for state in model_structure.all_states 
                                if bool(z3_model.eval(semantics.verifies(letter, state), model_completion=True)))
                
                if current_ver > 1:
                    constraints.append(ver_count < current_ver - 1)
                elif current_ver < len(model_structure.all_states) - 1:
                    constraints.append(ver_count > current_ver + 1)
                
                # Force different falsification pattern
                fals_count = z3.Sum([z3.If(semantics.falsifies(letter, state), 1, 0) 
                                    for state in model_structure.all_states])
                
                # Count current falsifiers
                current_fals = sum(1 for state in model_structure.all_states 
                                 if bool(z3_model.eval(semantics.falsifies(letter, state), model_completion=True)))
                
                if current_fals > 1:
                    constraints.append(fals_count < current_fals - 1)
                elif current_fals < len(model_structure.all_states) - 1:
                    constraints.append(fals_count > current_fals + 1)
        except Exception as e:
            logger.debug(f"Error creating verification constraint: {e}")
        
        # Return the combined constraint if any constraints were created
        if constraints:
            return z3.Or(constraints)
        
        return None
    
    def _create_stronger_constraint(self, isomorphic_model):
        """Create stronger constraints to escape isomorphic models for default theory.
        
        This creates more dramatic constraints when multiple consecutive
        isomorphic models have been found.
        
        Args:
            isomorphic_model: The Z3 model that was isomorphic
        
        Returns:
            z3.ExprRef: Stronger constraint or None if creation fails
        """
        # Get model structure and semantics
        model_structure = self.build_example.model_structure
        semantics = model_structure.semantics
        
        # The approach varies depending on the escape attempt
        escape_attempt = getattr(self, 'escape_attempts', 1)
        
        # Create constraints that force major structural changes
        constraints = []
        
        # 1. Force a dramatically different number of worlds
        try:
            # Count current worlds
            current_worlds = sum(1 for state in model_structure.all_states 
                              if bool(isomorphic_model.eval(semantics.is_world(state), model_completion=True)))
            
            # World count expression
            world_count = z3.Sum([z3.If(semantics.is_world(state), 1, 0) 
                                for state in model_structure.all_states])
            
            # Force minimal or maximal number of worlds
            if escape_attempt == 1:
                # First attempt: force significantly different world count
                if current_worlds > len(model_structure.all_states) // 2:
                    # If many worlds, force few worlds
                    constraints.append(world_count <= 2)
                else:
                    # If few worlds, force many worlds
                    constraints.append(world_count >= len(model_structure.all_states) - 2)
            else:
                # Later attempts: extreme values
                constraints.append(world_count == 1)  # Minimal
                constraints.append(world_count == len(model_structure.all_states))  # Maximal
        except Exception as e:
            logger.debug(f"Error creating world count constraint: {e}")
        
        # 2. Force dramatically different verification/falsification patterns
        try:
            for letter in model_structure.sentence_letters:
                # Verification extremes
                all_verify = z3.And([semantics.verifies(letter, state) 
                                  for state in model_structure.all_states])
                none_verify = z3.And([z3.Not(semantics.verifies(letter, state)) 
                                   for state in model_structure.all_states])
                
                # Falsification extremes
                all_falsify = z3.And([semantics.falsifies(letter, state) 
                                   for state in model_structure.all_states])
                none_falsify = z3.And([z3.Not(semantics.falsifies(letter, state)) 
                                    for state in model_structure.all_states])
                
                # Add constraints for extreme values
                constraints.append(all_verify)
                constraints.append(none_verify)
                constraints.append(all_falsify)
                constraints.append(none_falsify)
        except Exception as e:
            logger.debug(f"Error creating verification extremes: {e}")
        
        # 3. Force changes to parthood if available
        if hasattr(semantics, 'is_part_of'):
            try:
                # Count current parthood relations
                current_parts = 0
                for state1 in model_structure.all_states:
                    for state2 in model_structure.all_states:
                        if state1 != state2:
                            try:
                                if bool(isomorphic_model.eval(semantics.is_part_of(state1, state2), model_completion=True)):
                                    current_parts += 1
                            except Exception:
                                pass
                
                # Parthood count expression
                parthood_count = z3.Sum([z3.If(semantics.is_part_of(s1, s2), 1, 0) 
                                      for s1 in model_structure.all_states 
                                      for s2 in model_structure.all_states 
                                      if s1 != s2])
                
                # Force minimal or maximal parthood
                max_possible = len(model_structure.all_states) * (len(model_structure.all_states) - 1)
                
                if current_parts > max_possible // 2:
                    # If many part relations, force few
                    constraints.append(parthood_count <= max_possible // 4)
                else:
                    # If few part relations, force many
                    constraints.append(parthood_count >= 3 * max_possible // 4)
            except Exception as e:
                logger.debug(f"Error creating parthood constraint: {e}")
        
        # Return the combined constraint if any constraints were created
        if constraints:
            return z3.Or(constraints)
        
        return None
    
    def display_model_differences(self, model_structure, output=sys.stdout):
        """Format differences for display using default theory semantics.
        
        Args:
            model_structure: The model structure with differences
            output: Output stream for writing output
        """
        if not hasattr(model_structure, 'model_differences') or not model_structure.model_differences:
            return
            
        differences = model_structure.model_differences
        
        # TODO: does not seem to be used
        print("\n=== DIFFERENCES FROM PREVIOUS MODEL ===\n", file=output)
        
        # Print world changes
        if 'worlds' in differences and (differences['worlds'].get('added') or differences['worlds'].get('removed')):
            print("World Changes:", file=output)
            
            if differences['worlds'].get('added'):
                for world in differences['worlds']['added']:
                    try:
                        world_str = bitvec_to_substates(world, model_structure.semantics.N)
                        print(f"  + {world_str} (world)", file=output)
                    except:
                        print(f"  + {world} (world)", file=output)
            
            if differences['worlds'].get('removed'):
                for world in differences['worlds']['removed']:
                    try:
                        world_str = bitvec_to_substates(world, model_structure.semantics.N)
                        print(f"  - {world_str} (world)", file=output)
                    except:
                        print(f"  - {world} (world)", file=output)
        
        # Print possible state changes
        if 'possible_states' in differences and (differences['possible_states'].get('added') or differences['possible_states'].get('removed')):
            print("\nPossible State Changes:", file=output)
            
            if differences['possible_states'].get('added'):
                for state in differences['possible_states']['added']:
                    try:
                        state_str = bitvec_to_substates(state, model_structure.semantics.N)
                        print(f"  + {state_str}", file=output)
                    except:
                        print(f"  + {state}", file=output)
            
            if differences['possible_states'].get('removed'):
                for state in differences['possible_states']['removed']:
                    try:
                        state_str = bitvec_to_substates(state, model_structure.semantics.N)
                        print(f"  - {state_str}", file=output)
                    except:
                        print(f"  - {state}", file=output)
        
        # Print proposition changes
        if 'sentence_letters' in differences and differences['sentence_letters']:
            print("\nProposition Changes:", file=output)
            
            for letter, changes in differences['sentence_letters'].items():
                # Get the right letter name
                letter_name = letter
                if hasattr(model_structure, '_get_friendly_letter_name'):
                    try:
                        letter_name = model_structure._get_friendly_letter_name(letter)
                    except:
                        pass
                
                # Print letter changes
                print(f"  {letter_name}:", file=output)
                
                # Handle detailed verifier/falsifier changes
                if isinstance(changes, dict) and 'verifiers' in changes:
                    # Verifier changes
                    if changes['verifiers'].get('added') or changes['verifiers'].get('removed'):
                        if changes['verifiers'].get('added'):
                            added_states = []
                            for state in changes['verifiers']['added']:
                                try:
                                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                                    added_states.append(state_str)
                                except:
                                    added_states.append(str(state))
                            added_str = ', '.join(added_states)
                            print(f"    Verifiers: + {{{added_str}}}", file=output)
                            
                        if changes['verifiers'].get('removed'):
                            removed_states = []
                            for state in changes['verifiers']['removed']:
                                try:
                                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                                    removed_states.append(state_str)
                                except:
                                    removed_states.append(str(state))
                            removed_str = ', '.join(removed_states)
                            print(f"    Verifiers: - {{{removed_str}}}", file=output)
                    
                    # Falsifier changes
                    if changes['falsifiers'].get('added') or changes['falsifiers'].get('removed'):
                        if changes['falsifiers'].get('added'):
                            added_states = []
                            for state in changes['falsifiers']['added']:
                                try:
                                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                                    added_states.append(state_str)
                                except:
                                    added_states.append(str(state))
                            added_str = ', '.join(added_states)
                            print(f"    Falsifiers: + {{{added_str}}}", file=output)
                            
                        if changes['falsifiers'].get('removed'):
                            removed_states = []
                            for state in changes['falsifiers']['removed']:
                                try:
                                    state_str = bitvec_to_substates(state, model_structure.semantics.N)
                                    removed_states.append(state_str)
                                except:
                                    removed_states.append(str(state))
                            removed_str = ', '.join(removed_states)
                            print(f"    Falsifiers: - {{{removed_str}}}", file=output)
                
                # Simpler format showing old and new values
                elif isinstance(changes, dict) and 'old' in changes and 'new' in changes:
                    old_verifiers, old_falsifiers = changes['old']
                    new_verifiers, new_falsifiers = changes['new']
                    
                    try:
                        old_ver_str = pretty_set_print([bitvec_to_substates(v, model_structure.semantics.N) for v in old_verifiers])
                        new_ver_str = pretty_set_print([bitvec_to_substates(v, model_structure.semantics.N) for v in new_verifiers])
                        old_fals_str = pretty_set_print([bitvec_to_substates(f, model_structure.semantics.N) for f in old_falsifiers])
                        new_fals_str = pretty_set_print([bitvec_to_substates(f, model_structure.semantics.N) for f in new_falsifiers])
                        
                        print(f"    Verifiers: {old_ver_str} -> {new_ver_str}", file=output)
                        print(f"    Falsifiers: {old_fals_str} -> {new_fals_str}", file=output)
                    except:
                        # Fall back to simple representation
                        print(f"    Verifiers: {old_verifiers} -> {new_verifiers}", file=output)
                        print(f"    Falsifiers: {old_falsifiers} -> {new_falsifiers}", file=output)
                
                # Handle very simple changes
                else:
                    print(f"    Changed from previous model", file=output)
        
        # Print part-whole relationship changes
        if 'parthood' in differences and differences['parthood']:
            print("\nPart-Whole Relationship Changes:", file=output)
            
            for pair, change in differences['parthood'].items():
                # Try to parse the state pair
                try:
                    states = pair.split(',')
                    if len(states) == 2:
                        state1_bitvec = int(states[0])
                        state2_bitvec = int(states[1])
                        
                        state1_str = bitvec_to_substates(state1_bitvec, model_structure.semantics.N)
                        state2_str = bitvec_to_substates(state2_bitvec, model_structure.semantics.N)
                        
                        if change.get('new'):
                            print(f"  {state1_str} is now part of {state2_str}", file=output)
                        else:
                            print(f"  {state1_str} is no longer part of {state2_str}", file=output)
                        continue
                except:
                    pass
                
                # Fall back to simple representation
                if isinstance(change, dict) and 'old' in change and 'new' in change:
                    status = "now part of" if change['new'] else "no longer part of"
                    print(f"  {pair}: {status}", file=output)
                else:
                    print(f"  {pair}: changed", file=output)


# Wrapper function for use in theory examples
def iterate_example(example, max_iterations=None):
    """Find multiple models for a default theory example.
    
    This function creates a DefaultModelIterator for the given example
    and uses it to find up to max_iterations distinct models.
    
    Args:
        example: A BuildExample instance with a default theory model
        max_iterations: Maximum number of models to find (optional)
        
    Returns:
        list: List of distinct model structures
    """
    # Create the iterator with the example
    iterator = DefaultModelIterator(example)
    
    # Set max iterations if provided
    if max_iterations is not None:
        iterator.max_iterations = max_iterations
    
    # Perform iteration
    return iterator.iterate()
