
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
 	else:
 		generator=backwardChaining_or(kb,predicates,goal,theta)
 	for substitutions in generator:
 		print(substitutions)
 	return 1

# BackwardChaining_OR:yileds a substitution
# theta: mapping of variables built so far
# ********* if multiple mappings to a variable create a list as the key
def backwardChaining_or(kb,predicates,goal,theta):
	print("OR")
	#get the raw predicate without arguments
	predicate=goal.rsplit('(', 1)[0]
	params=extract_params(goal)
	#print(params)
	if predicate not in predicates:
 		return
	#get the corresponding function with args
	predicate_functions=predicates[predicate]
	for predicate_func in predicate_functions:
		#standardize variables
		implications_list=kb[predicate_func]
		first=predicate_func
		if not implications_list:
			if(fact(first)):
				if first in kb:
					actual_param=extract_params(first)
					key=theta.keys()[theta.values().index(params[0])]
					theta[key]=actual_param[0]
					print("True: "+first)
				else:
					print("False: "+first)
				yield theta
		for rule in implications_list:
			flag_unify=unify(goal,predicate_func,theta)
			if flag_unify==0:
				print("False: "+goal)
				return
			pred=map_to_var(predicate_func,theta)
			#replace the variables with the new mappings
			conjugates=map_to_var(rule,theta)
			for gen in backwardChaining_and(kb,predicates,conjugates,theta):
				yield gen
	#extract the corresponding 
# BackwardChaining_AND
def backwardChaining_and(kb,predicates,goals,theta):
	print("AND")
	#all goals must be proved
	if len(goals)==0:
		yield theta
	else:
		first=goals[0]
		rest=goals[1:]
		print("Ask: "+first)
		for theta_1 in backwardChaining_or(kb,predicates,first,theta):
			for theta_2 in backwardChaining_and(kb,predicates,rest,theta_1):
				yield theta_2

def fact(predicate):
	variables_in_predicate=extract_params(predicate)
	for var in variables_in_predicate:
		var=var.strip()
		if var[0].islower():
			return 0
	return 1
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

def unify(goal,predicate_func,result):
	#extract the variables from both
	flag=1
	variables_in_goal=extract_params(goal)
	variables_in_rule=extract_params(predicate_func)
	#map them
	if len(variables_in_goal)!=len(variables_in_rule):
		return 0

	for (var1,var2) in zip(variables_in_goal,variables_in_rule):

		var1=var1.strip()
		var2=var2.strip()
		#print("standardize: "+var1+" && "+var2)
		if var1==var2:
			flag=1
		#if both have variables
		elif var1.islower() and var2.islower():
			if var1 in result:
				result[var2]=result[var1]
			else:
				result[var1]=var2
		#if it is constant
		elif var1[0].isupper() and var2[0].isupper():
			if var1!=var2:
				flag=0

		elif var1.islower() and var2[0].isupper():
			result[var1]=var2
		elif var2.islower() and var1[0].isupper():
			result[var2]=var1

		elif var1.islower() or var1=="_":
			result[var1]=var2

		elif var2.islower() or var2=="_":
			result[var2]=var1

	return flag
def extract_params(predicate):
	variables_in_rule=re.search('\(.*\)',predicate)
	variables_in_rule=variables_in_rule.group()
	variables_in_rule=variables_in_rule.strip('(')
	variables_in_rule=variables_in_rule.strip(')')
	variables_in_rule=variables_in_rule.split(',')
	return variables_in_rule

def standardize_variables(clause,var_dict,index):
	variables=set()
	temp_dict=dict()
	premise=clause.rsplit(' =', 1)[0]
	premises=premise.split(" && ")
	for conjugate in premises:
		var_conju=extract_params(conjugate)
		for i in var_conju:
			if i.islower():
				i=i.strip()
				variables.update(i)
	conclusion=clause.rsplit('> ', 1)[1]
	var_in_con=extract_params(conclusion)
	for i in var_in_con:
			if i.islower():
				i=i.strip()
				variables.update(i)
	for v in variables:
		if v not in var_dict:
			var_dict[v]=1
		else:
			new_name=v+str(index)
			temp_dict[v]=new_name
			var_dict[new_name]=1

	new_conju=map_to_var(premise,temp_dict)	
	new_conclusion=map_to_var(conclusion,temp_dict)
	new_premise=""
	for conj in new_conju[:-1]:
		new_premise+=conj+" && "
	new_premise+=new_conju[-1]
	return new_premise,new_conclusion[0]
def main():
	#get the input file
	inputFile=sys.argv[2]
	counter=0
	index=0
	var_dict=dict()
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
				conclusion=clause.rsplit('> ', 1)[1]
				predicate=conclusion.rsplit('(', 1)[0]
				index+=1
				premise,conclusion=standardize_variables(clause,var_dict,index)
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


	# call function with KB and query
	backwardChaining_ask(kb,predicates,query)

if __name__=="__main__":
	main()