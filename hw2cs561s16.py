
import sys
import re

#variables are denoted by single lower case letter
# BackwardChaining_ASK:returns a generator of substitutions
def backwardChaining_ask(kb,predicates,query):
	# query can be proved if the kb contains a clause of the form lhs->query
	goal=query
	theta=dict()
	predicate=goal.rsplit('(', 1)[0]
	if predicate not in predicates:
 		return false
 	return backwardChaining_or(kb,predicates,goal,theta)

# BackwardChaining_OR:
# theta: mapping of variables built so far

# ********* if multiple mappings to a variable create a list as the key
def backwardChaining_or(kb,predicates,goal,theta):
	#get the raw predicate without arguments
	predicate=goal.rsplit('(', 1)[0]
	#get the corresponding function with args
	predicate_functions=predicates[predicate]
	for predicate_func in predicate_functions:
		#standardize variables
		updated_dict=standardize_var(goal,predicate_func)
		theta=updated_dict
		print("### dictionary of mapping ##\n")
		print(theta)
		pred=map_to_var(predicate_func,theta)
		print("Ask: "+pred[0])
		#extract the corresponding implications list
		implications_list=kb[predicate_func]
		for rule in implications_list:
			#replace the variables with the new mappings
			conjugates=map_to_var(rule,theta)
			print("\n## Conjugates ##")
			print(conjugates)
			or_ans=backwardChaining_and(kb,predicates,conjugates,theta)
	#extract the corresponding 
	yield or_ans

# BackwardChaining_AND
def backwardChaining_and(kb,predicates,goals,theta):
	#all goals must be proved

	return

def map_to_var(rule,theta):
	#replace each variable in every conjugate with its mapping
	
	new_conju=list()
	premise=rule.split(" && ")
	for conjugate in premise:
		new_var=list()
		var_conju=extract_params(conjugate)
		for var in var_conju:
			var=var.strip()
			if var in theta:
				new_var.append(theta[var])
			else:
				new_var.append(var)
		predicate=conjugate.rsplit('(', 1)[0]
		new_pred=predicate+"("
		for v in new_var[:-1]:
			new_pred+=v+", "
		new_pred+=new_var[-1]+")"
		new_conju.append(new_pred)
	return new_conju

def standardize_var(goal,predicate_func):
	result=dict()
	#extract the variables from both
	variables_in_goal=extract_params(goal)
	variables_in_rule=extract_params(predicate_func)
	#map them
	for (var1,var2) in zip(variables_in_goal,variables_in_rule):
		var1=var1.strip()
		var2=var2.strip()
		#add to dictionary
		if var1.islower() and var2.islower():
			result[var2]="_"
		elif var1.islower():
			result[var1]=var2
		else:
			result[var2]=var1
	return result
def extract_params(predicate):
	variables_in_rule=re.search('\(.*\)',predicate)
	variables_in_rule=variables_in_rule.group()
	variables_in_rule=variables_in_rule.strip('(')
	variables_in_rule=variables_in_rule.strip(')')
	variables_in_rule=variables_in_rule.split(',')
	return variables_in_rule

def main():
	#get the input file
	inputFile=sys.argv[2]
	counter=0
	#hashtable for all predicates
	predicates=dict()
	#conclusion is the key and the premise of conjuctions is the value
	kb=dict()
	with open(inputFile,'r') as f:
		#read the first line to determine query
		query=f.readline()
		#second line is number of clauses
		no_clauses=f.readline()
		no_clauses=int(no_clauses)
		while counter!=no_clauses:
			counter+=1
			clause=f.readline().rstrip()
			# check if clause is a conjuction
			if "=>" in clause:
				premise=clause.rsplit(' =', 1)[0]
				conclusion=clause.rsplit('> ', 1)[1]
				predicate=conclusion.rsplit('(', 1)[0]
			#otherwise clause is a fact with a single atomic sentence
			else:
				premise=""
				conclusion=clause
				predicate=conclusion.rsplit('(', 1)[0]

			if conclusion not in kb:
				kb[conclusion]=list()
			if premise!="":
				kb[conclusion].append(premise)

			if predicate not in predicates:
				predicates[predicate]=list()
			if conclusion not in predicates[predicate]:
				predicates[predicate].append(conclusion)

	print("\n Query:",query)
	print("\n########## predicates ##############\n")
	print(predicates)
	print("\n########## kb ##############\n")
	print(kb)
	print("\n")

	# call function with KB and query
	backwardChaining_ask(kb,predicates,query)

if __name__=="__main__":
	main()