
import sys
import re

#variables are denoted by single lower case letter
# BackwardChaining_ASK:returns a generator of substitutions
def backwardChaining_ask(kb,predicates,query):
	# query can be proved if the kb contains a clause of the form lhs->query
	goal=query
	theta=dict()
	print('Ask: ',goal)
	predicate=goal.rsplit('(', 1)[0]
	if predicate not in predicates:
 		return false
 	return backwardChaining_or(kb,predicates,goal,theta)

# BackwardChaining_OR:yields a substitution
# theta: mapping of variables built so far
def backwardChaining_or(kb,predicates,goal,theta):
	#get the raw predicate without arguments
	predicate=goal.rsplit('(', 1)[0]
	#get the corresponding function with args
	predicate_functions=predicates[predicate]
	for predicate_func in predicate_functions:
		#standardize variables
		updated_dict=standardize_var(goal,predicate_func)
		theta.update(updated_dict)
		print("dictionary of mapping:",theta)
		#store the mapping
		#extract the corresponding implications list
		implications_list=kb[predicate_func]
		#for every premise
		for rule in implications_list:
			print(rule)
			for mapping in theta:
				backwardChaining_and(kb,predicates,rule,theta)
	#extract the corresponding 
	return

# BackwardChaining_AND
def backwardChaining_and(kb,predicates,goals,theta):
	return


def standardize_var(goal,predicate_func):
	result=dict()
	#extract the variables from both
	variables_in_goal=re.search('\(.*\)',goal)
	variables_in_goal=variables_in_goal.group()
	variables_in_goal=variables_in_goal.strip('(')
	variables_in_goal=variables_in_goal.strip(')')
	variables_in_goal=variables_in_goal.split(',')

	variables_in_rule=re.search('\(.*\)',predicate_func)
	variables_in_rule=variables_in_rule.group()
	variables_in_rule=variables_in_rule.strip('(')
	variables_in_rule=variables_in_rule.strip(')')
	variables_in_rule=variables_in_rule.split(',')
	#map the variables
	
	for (var1,var2) in zip(variables_in_goal,variables_in_rule):
		#add to dictionary
		if var1.islower():
			result[var1]=var2
		else:
			result[var2]=var1

	return result

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
	print("\n\n########## predicates ##############\n")
	print(predicates)
	print("\n\n########## kb ##############\n")
	print(kb)

	# call function with KB and query
	backwardChaining_ask(kb,predicates,query)

if __name__=="__main__":
	main()