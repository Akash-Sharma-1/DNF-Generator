################### Q1 PART B - BONUS
###### AKASH SHARMA , 2017327

'''
ASSUMPTIONS-----------------------------------------------
Symbols to used in the input propositional logic:

1) + for disjunction 
2) . for conjunction
3) ~ for negation
4) * for implication
5) = for bi-implication
6) Additional terms like '(' and ')'
7) small ascii characters as binary variables

[NO SPACES IN BETWEEN TO BE USED and NO NULL PROPOSITION]
----------------------------------------------------------

ADDITIONAL PART OF Q1B) BONUS -> 
'''

#importing modules
from tabulate import tabulate
import copy

#Helper functions

def flip(x):
	#fliping the bit
	if(x==1):
		return 0
	else:
		return 1

def generateTT(vars,values,varmap):
	#tabulate the truth table
	varss=vars
	for i in range(len(values)):
		varss[i].append(values[i])
	print(tabulate(varss, headers=list(varmap.keys())+["Result"]))

def generateSOP(vars,values,varmap):
	#generating DNF (or SOP)
	ans=""
	miniansarr=[]
	for i in range(len(values)):
		if(values[i]==1):
			minians=""
			for j in range(len(vars[i])-1):
				if(vars[i][j]==1):
					minians+=str(list(varmap.keys())[j])+"."
				else:
					minians+="~"+str(list(varmap.keys())[j])+"."
			minians=minians[:len(minians)-1]
			miniansarr.append("("+minians+")")
	for i in miniansarr:
		ans+=(i+"+")
	ans=ans[:len(ans)-1]
	if(ans==""):
		print("0")
	else:
		print(ans)
	print(ans)

#Reduced DNF using Quine-McCluskey Method

def reducedDNF(varmap,values,no_of_variables):
	reducedTruths=[]
	reducedTruths.append({})

	numbered_truth_vals=[]
	for i in range(len(values)):
		if(values[i]==1):
			numbered_truth_vals.append(bin(i)[2:].zfill(no_of_variables))

	for i in range(len(numbered_truth_vals)):
		reducedTruths[0][numbered_truth_vals[i]]=False

	ind=0
	finishit=0
	while(finishit==0):
		reducedTruths.append({})
		redtruthsNow=reducedTruths[ind]
		#ind+=1
		for i,ii in redtruthsNow.items():
			for j,jj in redtruthsNow.items():
				differentbits=0
				redudantbitrem=""
				for k in range(len(i)):
					if i[k]!=j[k]:
						differentbits+=1
						redudantbitrem+=("-")
					else:
						redudantbitrem+=(i[k])

				if(differentbits==1):
					reducedTruths[ind][i]=True
					reducedTruths[ind+1][redudantbitrem]=False

		for i,j in redtruthsNow.items():
			if(j==False):
				reducedTruths[ind+1][i]=False

		if reducedTruths[ind]==reducedTruths[ind+1]:
			reducedTruths.pop()
			break

		ind+=1

		# pretty(reducedTruths)

	strq=""
	for i,j in (reducedTruths[len(reducedTruths)-1].items()):
		strq+="("
		for k in range(len(i)):
			if i[k]=="0":
				strq+=("~"+varmap[k])
				strq+="."
			elif i[k]=="1":
				strq+=(varmap[k])
				strq+="."
		strq=strq[:-1]
		strq+=")+"
	strq=strq[:len(strq)-1]

	if(strq==")"):
		return "1"
	elif (strq==""):
		return "0"
	else:
		return strq

# Main Function <----
print("Enter the proposition with appropriate syntax")
inp=input()

#preprocessing of string -> "==" into "="
inp=inp.replace("==","=")
#preprocessing - reading chars, storing variables 
props=inp
no_of_variables=0
var=[]
varmap={}
#calculating number of variables
for i in range(len(inp)):
	if(ord(inp[i])>=97 and ord(inp[i])<=122) and inp[i] not in varmap:
		no_of_variables+=1
		var.append(0)
		varmap[inp[i]]=no_of_variables-1

'''
-------------------------------------------------------------------------------
Operator precedence in propositional logic used in creating the postfix order

1)~
2).
3)+
4)*
5)==
'(' and ')' parenthesis are given the highest priority pairwise

-------------------------------------------------------------------------------
'''

#infix to postfix formation using stack
outp=[]
stack=[]
precedence={'~':5,'.':4,'+':3,'*':2,'=':1,'(':0,')':0}
for i in range(len(inp)):
	if (ord(inp[i])>=97 and ord(inp[i])<=122):
		outp.append(inp[i])
	elif(inp[i]=='('):
		stack.append(inp[i])
	elif(inp[i]==')'):
		x=stack.pop()
		while x!='(' and len(stack)>0:
			outp.append(x)
			x=stack.pop()
	else:
		while len(stack)>0 and precedence[stack[len(stack)-1]]>=precedence[inp[i]]:
			x= stack.pop()
			outp.append(x)
		stack.append(inp[i])
while len(stack)>0:
	outp.append(stack.pop())

# evaluating postfix expression with all possible binary combinations
vartable=[]
values=[]
number_of_values=(2**no_of_variables)
#forming  2**n generations (n -> no of variables) and each generation will have unique binary combination for each variable
for i in range(number_of_values):
	valuesInString=bin(i)[2:].zfill(no_of_variables)
	for j in range(len(valuesInString)):
		var[j]= int(valuesInString[j])
	evalexpr=[]
	# replacing variables with binary values
	for j in range(len(outp)):
		if (ord(outp[j])>=97 and ord(outp[j])<=122):
			evalexpr.append(var[varmap[outp[j]]])
		else:
			if outp[j]=="~":
				evalexpr.append(outp[j])
			else:
				evalexpr.append(outp[j])


	result=[]
	#evaluating the final result 
	for j in range(len(evalexpr)):
		if ((evalexpr[j])==1) or ((evalexpr[j])==0):
			result.append(evalexpr[j])
		else:
			a1=0
			a2=0
			if(evalexpr[j]=='~'):
				result[len(result)-1]=(flip(result[len(result)-1]))
			else:
				a2=result.pop()
				a1=result.pop()

			if(evalexpr[j]=='.'):
				result.append(a1&a2)
			if(evalexpr[j]=='+'):
				result.append(a1|a2)
			if(evalexpr[j]=='*'):
				result.append(flip(a1)|a2)
			if(evalexpr[j]=='='):
				result.append((a1&a2)|(flip(a1)&flip(a2)))

	a=copy.deepcopy(var)
	vartable.append(a)
	values.append(result.pop())

# generating final results	
print("\n")
print("Generating Truth Table --------------")
generateTT(vartable,values,varmap)
print("\n")
print("Generating DNF -----------------")
generateSOP(vartable,values,varmap)

print("Generating Reduced DNF -----------------")
s=reducedDNF(list(varmap.keys()),values,no_of_variables)
print(s)











		









