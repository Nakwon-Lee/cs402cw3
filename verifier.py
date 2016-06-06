import sys
import os

def isType(token): # check whether the token is type keyword or not
	result = False
	if token == "int":
		result = True
	elif token == "boolean":
		result = True
	elif token == "void":
		result = True
	else:
		pass

	return result

def isValidName(token): # check whether the token is valid name of method or not
	result = False
	if token[0] != '<':
		result = True
	else:
		pass
	
	return result

def isTargetMethod(st_line): # check whether the string line is target method or not

	result = False

	tokens = st_line.split()
	if len(tokens) <= 0:
		pass
	else:
		if tokens[0] == "public":
			if isType(tokens[1]):
				if isValidName(tokens[2]):
					result = True

	return result

def isAssignment(line): # check whether the given line is assignment or not
	result = False

	# is not := but is =
	if line.find(":=") == -1 and line.find("=") != -1: 
		result = True

	return result

def isAssertion(line): # check whether the given line is start of assertion or not
	result = False

	if line.find("$assertionsDisabled") != -1:
		result = True

	return result

def isReturn(token): # check whether the given token has return statement
	result = False

	if token.find("return") != -1:
		result = True

	return result

def isIf(token): # check whether the given token is if
	result = False

	if token == "if":
		result = True

	return result

def isLabel(token): # check whether the given token has label
	result = False

	# containing "label" and finish with :
	if token.find("label") != -1 and token[len(token)-1] == ':':
		result = True

	return result

def isGoto(token): # check whether the given token is goto only statement
	result = False

	# if the token is goto, it is goto only statement
	if token == "goto":
		result = True

	return result

def isParenthesisNumberLine(token): # check whether the given token is (?)
	result = False

	# if the token is wrapped with ( and ), it is (?)
	if token[0] == '(' and token[len(token)-1] == ')':
		result = True

	return result

def isThrow(token): # check whether the given token is throw
	result = False

	if token == "throw":
		result = True

	return result

def isSemanticAssign(line): # check whether the given line is semantic assignment
	result = False

	if line.find(":=") != -1:
		result = True

	return result

def whatLine(line): # determine what actions are needed for given line

	result = 0
	tokens = line.split()

	if len(tokens) <= 0:
		pass
	else:
		# if the line is start with parenthesisNumber (num 9)
		if isParenthesisNumberLine(tokens[0]):
			result = 9
		elif isSemanticAssign(line): # if the line is semantic assignment (num 11)
			result = 11
		elif isAssertion(line): # if the line is start of assertion (num 3)
			result = 3
		elif isIf(tokens[0]): # if the line is if statement (num6)
			result = 6
		elif isGoto(tokens[0]): # if the line is goto statement (goto only) (num 8)
			result = 8
		elif isThrow(tokens[0]): # if the line is throw only statement (num 10)
			result = 10
		elif isLabel(tokens[0]): # if the line is label statement (num 7)
			result = 7
		elif isType(tokens[0]): # if first token is type, it is declation of variables (num 1)
			result = 1
		elif isAssignment(line): # if the line is assignment (num 2)
			result = 2
		elif isTargetMethod(line): # if the line is start of target method (num 4)
			result = 4
		elif isReturn(tokens[0]): # if the first token is return statement (num 5)
			result = 5
		else:
			pass

	return result

def writeFormDVars(line, filename, varset): # write the variable declaration smt formula

	# given line should be the variable declaration statement  
	tokens = line.split()
	
	for i in range(1, len(tokens)):
		var = tokens[i]
		if var.find(',') != -1:
			var = var[0:len(var)-1]
		if var.find(';') != -1:
			var = var[0:len(var)-1]

		if var not in varset:
			varset.add(var)

			if tokens[0] == "int":
				smtf = open(filename,'a')
				data = "(declare-const %s Int)\n" % var
				smtf.write(data)
				smtf.close()
			elif tokens[0] == "boolean":
				smtf = open(filename,'a')
				data = "(declare-const %s Bool)\n" % var
				smtf.write(data)
				smtf.close()

def writeFormAssignPhi(filename, right, data, left):
	right = right[right.find('(')+1:len(right)-1]
	tokens = right.split(',')

	totokens = []
	for i in range(len(tokens)):
		totokens.append(tokens[i].split())

	for i in range(len(totokens)):
		temptoken = totokens[i]
		temptoken[1] = temptoken[1][1:len(temptoken)]

		data2 = data + "(=> tempbool" + temptoken[1] + " (= " + left + " " + temptoken[0] + "))" + "))\n"
		smtf = open(filename, 'a')
		smtf.write(data2)
		smtf.close()

	# print totokens

def writeFormAssign(line, filename, varset, conddic, clabel):

	tokens = line.split('=')

	assert len(tokens) == 2, "writeFormAssign: len(tokens) is not two"

	left = tokens[0]
	left = left.lstrip()
	left = left.rstrip()
	right = tokens[1]
	right = right.lstrip()
	right = right.rstrip()

	if right.find(';') != -1:
		right = right[0:len(right)-1] # remove the semicolon
	# print "l:", left, "  r:", right

	data = None

	# prefix
	if conddic[clabel] == "":
		data = "(assert (=> true "
	else:
		data = "(assert (=> " + conddic[clabel] + " "

	# assumption! right of assignment statement is expression of only one 
	# binary operator or just a variable or Phi

	if right.find('+') != -1:
		righttokens = right.split('+')
		writeFormAssignRightSub(filename, righttokens, data, left, "(+ ")
	elif right.find('-') != -1:
		righttokens = right.split('-')
		writeFormAssignRightSub(filename, righttokens, data, left, "(- ")
	elif right.find('*') != -1:
		righttokens = right.split('*')
		writeFormAssignRightSub(filename, righttokens, data, left, "(* ")
	elif right.find('/') != -1:
		righttokens = right.split('/')
		writeFormAssignRightSub(filename, righttokens, data, left, "(mydiv ")
	elif right.find("Phi") != -1:
		writeFormAssignPhi(filename, right, data, left)
	else: 
		temptokens = right.split()
		if temptokens[0] == "new": # not a binary operator. class initiation
			pass
		else: # it may be assignment of jsut a variable, right may be just a variable
			righttokens = []
			righttokens.append(right)
			writeFormAssignRightSub(filename, righttokens, data, left, None)

def writeFormAssignRightSub(filename, righttokens, prefix, left, opst):

	data = ""

	rightleft = righttokens[0]
	rightleft = rightleft.lstrip()
	rightleft = rightleft.rstrip()
	if len(righttokens) == 2:
		rightright = righttokens[1]
		rightright = rightright.lstrip()
		rightright = rightright.rstrip()

		data = prefix + "(= " + left + " " + opst + rightleft + " " + rightright + "))" + "))\n"

	else:
		data = prefix + "(= " + left + " " + rightleft + ")" + "))\n"

	smtf = open(filename,'a')
	smtf.write(data)
	smtf.close()

# get label for safe asserting from if statement which is appeared first since assertion start
def getLabelHint(line):

	issafelabel = None
	labelhint = None
	tokens = line.split("goto")

	# assumption! tokens have two elements
	if tokens[0].find("!=") != -1: # label is safe label
		issafelabel = True
	elif tokens[0].find("==") != -1: # label is unsafe label
		issafelabel = False

	resultlabel = tokens[1]
	resultlabel = resultlabel.lstrip()
	resultlabel = resultlabel.rstrip()
	if resultlabel.find(';') != -1: # remove the semicolon
		resultlabel = resultlabel[0:len(resultlabel)-1]
	labelhint = resultlabel

	return issafelabel, labelhint

def getLabelHintFromGotoOnly(line):

	issafelabel = True
	labelhint = None
	tokens = line.split()

	# assumption! tokens have two elements
	assert len(tokens) == 2, "label hint from goto only: len(tokens) is not two"

	resultlabel = tokens[1]
	resultlabel = resultlabel.lstrip()
	resultlabel = resultlabel.rstrip()
	if resultlabel.find(';') != -1: # remove the semicolon
		resultlabel = resultlabel[0:len(resultlabel)-1]
	labelhint = resultlabel

	return issafelabel, labelhint

def subFormGen(token, varset):
	result = ""
	result2 = ""
	ttokens = None

	if token.find("==") != -1:
		result = "(= "
		result2 = ")"
		ttokens = token.split("==")
	elif token.find("!=") != -1:
		result = "(not (= "
		result2 = "))"
		ttokens = token.split("!=")
	elif token.find(">=") != -1:
		result = "(>= "
		result2 = ")"
		ttokens = token.split(">=")
	elif token.find("<=") != -1:
		result = "(<= "
		result2 = ")"
		ttokens = token.split("<=")
	elif token.find(">") != -1:
		result = "(> "
		result2 = ")"
		ttokens = token.split(">")
	elif token.find("<") != -1:
		result = "(< "
		result2 = ")"
		ttokens = token.split("<")

	# ttokens should be length two
	assert len(ttokens) == 2

	ttokens[0] = ttokens[0].lstrip()
	ttokens[0] = ttokens[0].rstrip()

	ttokens[1] = ttokens[1].lstrip()
	ttokens[1] = ttokens[1].rstrip()

	# variable names must be valid (but tokens cannot be variable)

	data = result + ttokens[0] + " " + ttokens[1] + result2

	# print data,

	return data

def formgenSafeNFound(token, varset):
	result = ""
	data = subFormGen(token, varset)
	result = "(assert " + data + ")\n"
	return result

def formgenSafeFound(token, varset):
	result = ""
	data = subFormGen(token, varset)
	result = "(assert (not " + data + "))\n"	
	return result

def formgenUSafeNFound(token, varset):
	result = ""
	data = subFormGen(token, varset)
	result = "(assert (not " + data + "))\n"	
	return result

def formgenUSafeFound(token, varset):
	result = ""
	data = subFormGen(token, varset)
	result = "(assert " + data + ")\n"	
	return result

def writeFormAssertIf(line, filename, varset, issafeassert, labelhint):
	
	tokens = line.split("goto")

	# assumption! in assert if line, there must be a goto and a target label.
	# So, len(tokens) must be two
	assert len(tokens) == 2, "writeformassertif: len(tokens) must be two"
	
	# assumption! split with if must produce two tokens [whitespaces] and [logical relation]

	lefttokens = tokens[0].split("if",1)
	assert len(lefttokens) == 2, "writeformassertif: len(lefttokens must be two)"
	lefttokens[1] = lefttokens[1].lstrip()
	lefttokens[1] = lefttokens[1].rstrip()

	# print lefttokens[1],

	if issafeassert: # hint label is safe label
		if tokens[1].find(labelhint) != -1: # safe label found!
			# print "safe label found!",
			# string generation for safe found statement (only one logical relation operator)
			data = formgenSafeFound(lefttokens[1], varset)
		else: # safe label not found!
			# print "safe label not found!",
			# string generation for safe not found statement (only one logical relation operator)
			data = formgenSafeNFound(lefttokens[1], varset)

	else: # hint label is unsafe label
		if tokens[1].find(labelhint) != -1: # unsafe label found!
			# print "unsafe label found!",
			# string generation for unsafe found statement (only one logical relation operator)
			data = formgenUSafeFound(lefttokens[1], varset)
		else: # unsafe label not found!
			# print "unsafe label not found!",
			# string generation for unsafe not found statement (only one logical relation operator)
			data = formgenUSafeNFound(lefttokens[1], varset)
	
	# print data,

	smtf = open(filename, 'a')
	smtf.write(data)
	smtf.close()

def extractCond(line, varset):
	tokens = line.split("goto")

	# assumption! in assert if line, there must be a goto and a target label.
	# So, len(tokens) must be two
	assert len(tokens) == 2, "writeformassertif: len(tokens) must be two"
	
	# assumption! split with if must produce two tokens [whitespaces] and [logical relation]

	lefttokens = tokens[0].split("if",1)
	assert len(lefttokens) == 2, "writeformassertif: len(lefttokens must be two)"
	lefttokens[1] = lefttokens[1].lstrip()
	lefttokens[1] = lefttokens[1].rstrip()

	# print lefttokens[1],

	return subFormGen(lefttokens[1], varset)

def fileCut(filename):
	result = ""
	tokens = filename.split(".java")

	# print tokens
	
	# tokens should be length of one
	assert len(tokens) == 2

	result = tokens[0]

	# print result

	return result

def initiationOfVeri(conddic):

	conddic["label0"] = ""

	return "label0"

def getLabelFromStatement(lines, conddic):
	tokens = lines.split()

	assert len(tokens) == 1, "getLabelFromStatement: label statement must have one token"
	assert tokens[0].find(':') != -1, "getLabelFromStatement: token must have colon"

	token = tokens[0]

	token = token[0:len(token)-1]

	assert token in conddic, "getLabelFromStatement: label must be added before finding"

	return token

def addLabelToCondDic(conddic, line):
	tokens = line.split()

	# assumption! tokens have two elements
	assert len(tokens) == 2, "label hint from goto only: len(tokens) is not two"

	resultlabel = tokens[1]
	resultlabel = resultlabel.lstrip()
	resultlabel = resultlabel.rstrip()
	if resultlabel.find(';') != -1: # remove the semicolon
		resultlabel = resultlabel[0:len(resultlabel)-1]
	labelst = resultlabel

	if labelst not in conddic:
		conddic[labelst] = ""

	return labelst

def addLabelToCondDicIf(conddic, line):
	tokens = line.split("goto")

	assert len(tokens) == 2, "addlabeltoconddicif: len(tokens) must be two"

	righttoken = tokens[1]

	righttoken = righttoken.lstrip()
	righttoken = righttoken.rstrip()
	
	assert righttoken.find(';') != -1, "addlabeltoconddicif: righttoken must have semicolon"

	righttoken = righttoken[0:len(righttoken)-1]

	if righttoken not in conddic:
		conddic[righttoken] = ""

	return righttoken

def addLabelToCondDicLabel(conddic, line):
	tokens = line.split()

	assert len(tokens) == 1, "addlabeltoconddiclabel: len(tokens) must be one"

	tokens[0] = tokens[0][0:len(tokens[0])-1]

	if tokens[0] not in conddic:
		conddic[righttoken] = ""

	return tokens[0]

def updateCondAnd(clabel, newcond, conddic): # update condition of current label with not newcond

	assert clabel in conddic, "updatecondand: label must be in conddic"

	assert newcond != "", "updatecondand: newcond must be a proposition"

	if conddic[clabel] == "": # current label is no cond
		conddic[clabel] = "(not " + newcond + ")"
	else:
		conddic[clabel] = "(and " + conddic[clabel] + " " + "(not " + newcond + "))"

	# print "condic and ", newcond, conddic[clabel]

def updateCondOr(tlabel, clabel, conddic): # update condition of label (or)

	assert tlabel in conddic and clabel in conddic, "updateCondOr: labels must be in conddic"

	if conddic[clabel] == "": # current label is no cond
		pass
	else:
		if conddic[tlabel] == "": # target label is no cond
			conddic[tlabel] = conddic[clabel]
		else: # both labels have cond
			conddic[tlabel] = "(or " + conddic[tlabel] + " " + conddic[clabel] + ")"

	# print "condic or ", conddic[clabel], conddic[tlabel]

def updateCondNewOr(tlabel, clabel, newcond, conddic): # update condition of label with newcond (or)

	assert tlabel in conddic and clabel in conddic, "updateCondNewOr: labels must be in conddic"

	assert newcond != "", "updatecondnewor: newcond must be a proposition"

	if conddic[clabel] == "": # current label is no cond
		if conddic[tlabel] == "": # target label is no cond
			conddic[tlabel] = newcond
		else: # target label has cond
			conddic[tlabel] = "(or " + conddic[tlabel] + " " + newcond + ")"
	else:
		if conddic[tlabel] == "": # target label is no cond
			conddic[tlabel] = "(and " + conddic[clabel] + " " + newcond + ")"
		else: # both labels have cond
			conddic[tlabel] = "(or " + conddic[tlabel] + " " + "(and " + conddic[clabel] + " " + newcond + "))"

	# print "condic new or ", newcond, conddic[clabel], conddic[tlabel]

def writeFormParen(token, clabel, conddic, parenvarset, filename):
	# token may be the form (??
	tokens = token.split('(')
	assert len(tokens) == 2, "writeformparen: len(tokens) must be two"
	parenvarset.add(int(tokens[1]))
	data1 = "(declare-const tempbool" + tokens[1] + " Bool)\n"
	data2 = "(assert (= " + conddic[clabel] + " tempbool" + tokens[1] + "))\n"

	smtf = open(filename, 'a')
	smtf.write(data1)
	smtf.write(data2)
	smtf.close()

def writeTheAssertionProperty(clabel, conddic, filename):
	data = "(assert (not "
	last = "))\n"

	data = data + conddic[clabel] + last

	smtf = open(filename, 'a')
	smtf.write(data)
	smtf.close()

def identifyParameter(line, paramvarset):
	tokens = line.split(":=")

	assert len(tokens) == 2, "identifyparameter: len(tokens) must be two"

	if tokens[1].find("@parameter") != -1: # the statement is semantic assignment of parameter
		tokens[0] = tokens[0].lstrip()
		tokens[0] = tokens[0].rstrip()
		paramvarset.add(tokens[0])

def verify(filename):

	inbody = False
	inassert = False
	labelget = False
	endofmethod = False

	smtfilename = "verifile.smt2"
	issafelabel = None
	labelhint = None

	classname = fileCut(filename)

	string = "./soot.sh " + classname

	jimplename = classname + ".shimple"

	tf = open(jimplename, 'w')

	tf.close()

	os.remove(jimplename)

	os.system(string)

	defineMydiv = "(define-fun mydiv ((x Int) (y Int)) Int (if (not (= y 0)) (div x y) 0))\n"

	smtf = open(smtfilename, 'w')
	smtf.write(defineMydiv)
	smtf.close()

	varset = set()
	parenvarset = set()
	paramvarset = set()

	labelconddic = {}

	currentlabel = ""

	key = 0

	lines = open(jimplename).readlines()
	
	i = 0

	while (not endofmethod): # each line including newline
		
		key = whatLine(lines[i])

		if key == 1: # declaration of variables
			if inbody:
				writeFormDVars(lines[i], smtfilename, varset)
				# print varset
				# print "var decl"

		elif key == 2: # assignment
			if inbody:
				writeFormAssign(lines[i], smtfilename, varset, labelconddic, currentlabel)
				# print "assign"

		elif key == 3: # start of assertion
			if inbody:
				inassert = True
				# print "st assert"

		elif key == 4: # start of target method
			inbody = True
			currentlabel = initiationOfVeri(labelconddic)
			# print labelconddic, currentlabel,
			# print "st target method"

		elif key == 5: # return statement
			if (inbody and inassert):
				inbody = False
				inassert = False
				endofmethod = True
				# print "return"
		elif key == 6: # if statement
			if inbody:
				t_label = addLabelToCondDicIf(labelconddic, lines[i])
				# print labelconddic
				if inassert:
					if labelget:
						# writeFormAssertIf(lines[i], smtfilename, varset, issafelabel, labelhint)
						newcond = extractCond(lines[i], varset)
						updateCondNewOr(t_label, currentlabel, newcond, labelconddic)
						updateCondAnd(currentlabel, newcond, labelconddic)
						# print "assert if"
					else:
						issafelabel, labelhint = getLabelHint(lines[i])
						# print issafelabel, labelhint,
						# print "label hint if"
						if issafelabel:
							labelget = True
				else:
					newcond = extractCond(lines[i], varset)
					updateCondNewOr(t_label, currentlabel, newcond, labelconddic)
					updateCondAnd(currentlabel, newcond, labelconddic)
					# print "if\n"
		elif key == 7: # label statement
			if inbody:
				if currentlabel != "": # be reached from current label
					t_label = addLabelToCondDicLabel(labelconddic, lines[i])
					updateCondOr(t_label, currentlabel, labelconddic)
					del labelconddic[currentlabel]
					currentlabel = ""

				currentlabel = getLabelFromStatement(lines[i],labelconddic)

				if inassert:
					if currentlabel == labelhint: # clabel is safe label!
						writeTheAssertionProperty(currentlabel, labelconddic, smtfilename)
					# print labelconddic
					# print "assert label"

				# if current label is only one label, it has no condition
				if len(labelconddic) == 1:
					labelconddic[currentlabel] = ""
				# print currentlabel
				# print labelconddic

		elif key == 8: # goto only statement
			if inbody:
				t_label = addLabelToCondDic(labelconddic, lines[i])
				# print labelconddic
				if inassert:
					# if inassert and if not labelget, it should be unsafe label
					if not labelget:
						issafelabel, labelhint = getLabelHintFromGotoOnly(lines[i])
						labelget = True
						# print issafelabel, labelhint,
						# print "assert goto"
					else:
						updateCondOr(t_label, currentlabel, labelconddic)
						# print "assert labelget goto"
				else:
					updateCondOr(t_label, currentlabel, labelconddic)
					# print "goto"
				del labelconddic[currentlabel]
				currentlabel = ""
		elif key == 9: # (?) statement
			if inbody:
				# print "(?)",
				tempsplit = lines[i].split(')', 1)
				assert len(tempsplit) == 2, "(?) statement must be splitted with two parts"
				writeFormParen(tempsplit[0], currentlabel, labelconddic, parenvarset, smtfilename)
				lines[i] = tempsplit[1]
				# print lines[i],
				i = i - 1
		elif key == 10: # throw only statement
			if inbody:
				# print "throw"
				del labelconddic[currentlabel]
				currentlabel = ""
		elif key == 11: # semantic assginment statement
			if inbody:
				identifyParameter(lines[i], paramvarset)
				# print ":="
		else:
			pass

		i = i + 1

	# print paramvarset
	getvalueparam = "(get-value ("

	for i in paramvarset:
		getvalueparam = getvalueparam + i + " "
	getvalueparam = getvalueparam[0:len(getvalueparam)-1] + "))\n" 

	smtf = open(smtfilename, 'a')
	smtf.write("(check-sat)\n")
	smtf.write(getvalueparam)
	smtf.close()

	outputfilename = "z3output"

	outputfile = open(outputfilename, 'w')
	outputfile.close()

	os.system("z3 -smt2 \"verifile.smt2\" >> z3output")

	showResults(outputfilename)

def showResults(filename):
	lines = open(filename).readlines()

	if lines[0].find("unsat") != -1: # result is unsat valid!!!
		print "VALID"
	else:
		for i in range(1,len(lines)):
			print lines[i],

if __name__ == '__main__':
	
	verify(sys.argv[1])
