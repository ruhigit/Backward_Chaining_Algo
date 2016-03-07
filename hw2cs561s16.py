# first line of input: Query
import sys

def main():
	#get the input file
	inputFile=sys.argv[2]
	counter=0
	#contains all the facts from KB from top to bottom
	assertions=list()
	#contains premise to reach the conclusion 
	implications=dict()
	
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
				if conclusion not in implications:
					implications[conclusion]=list()
				implications[conclusion].append(premise)
				assertions.append(conclusion)
			#otherwise clause is a fact with a single atomic sentence
			else:
				assertions.append(clause)

	#print(implications)
	print(assertions) 

if __name__=="__main__":
	main()