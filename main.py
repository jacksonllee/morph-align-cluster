# Morphological alignment and clustering
# May 2014
# Jackson Lee
# jsllee.phon@gmail.com
#
# Paper:
#
# Lee, Jackson L. 2014. Automatic morphological alignment and clustering.
# Technical report TR-2014-07, Department of Computer Science, University of Chicago.
#
#####################################################

import math
import itertools
import time
import random
import numpy
import copy
import codecs
import re
import subprocess

#####################################################

#############
# Data source
#############

fname = 'spanishPresentIndicative.csv'
delimiter = ','
latexfilename = 'spanish.tex'
COLUMNS = 6
ROWS = 50

#fname = 'englishverbsCOCA100phonemes.csv'
#latexfilename = 'english.tex'
#delimiter = ' '
#COLUMNS = 5
#ROWS = 50


#####################################################

# Cost parameters

STEM_USED = 4
STEM_NOT_USED = 3
AFFIX_USED = 1
AFFIX_NOT_USED = 2
EXTRA = 10

AFFIX_DIFF = 5

LAMBDA_BITS = 5 # lambda

#####################################################

###############
## Functions ##
###############

def readCSV(fname, delim=',;\t| '):
    import csv
    with open(fname, 'rU') as csvfile:
        dialect = csv.Sniffer().sniff(csvfile.read(), delimiters=delim)
        csvfile.seek(0)
        data = csv.reader(csvfile, dialect)
        return list(data)

#----------------------------------------------------------------#

def choose(n,k):
    'n choose k'
    import math
    return math.factorial(n)/(math.factorial(k)*math.factorial(n-k))

#----------------------------------------------------------------#

def null(s):
    if s:
        return s
    else:
        return '\\O'

#----------------------------------------------------------------#

def unorder(s):
    'takes a string and returns its alphabetized version'
    return ''.join(sorted(list(iter(s))))

#----------------------------------------------------------------#

def reorder(s, sample):
    'takes a string s and re-orders its characters according to "sample"'
    result = ''
    for character in sample:
        if character in s:
            result += character
            s = s.replace(character,'',1)
    if result:
        return result
    else:
        return '{\\O}'

#----------------------------------------------------------------#

def union(s):
    'takes a list of strings and returns its union'
    temp = unorder(''.join(s))
    letters = list(set(sorted([x for x in temp])))
    result = ''
    for l in letters:
        c = 0
        for word in s:
            if word.count(l) > c:
                c = word.count(l)
        result += l*c
    return result

#----------------------------------------------------------------#

def cost(stem,affix,target):
    'calculates the cost of a (stem, affix, target) trio and returns the 5-dimensional cost vector'

    stemUsed = 0 # count of stem letters used
    stemNotUsed = 0  # count of stem letters not used
    affixUsed = 0  # count of affix letters used
    affixNotUsed = 0  # count of affix letters not used
    extra = 0  # count of extra letters needed
    tempStem = str(stem)
    tempAffix = str(affix)

    for l in target:
        if l in tempStem:
            stemUsed += 1
            tempStem = tempStem.replace(l,'',1)
        elif l in tempAffix:
            affixUsed += 1
            tempAffix = tempAffix.replace(l,'',1)
        else:
            extra += 1
    stemNotUsed = len(stem) - stemUsed
    affixNotUsed = len(affix) - affixUsed

    return numpy.array([STEM_USED*stemUsed, STEM_NOT_USED*stemNotUsed,
             AFFIX_USED*affixUsed, AFFIX_NOT_USED*affixNotUsed, EXTRA*extra])

#----------------------------------------------------------------#

def shortest(L):
    'finds the shortest string(s) in a list'
    c = min([len(w) for w in L]) # shortest length in L
    return [x for x in L if len(x) == c]


#----------------------------------------------------------------#


def createUnionAffixes(affixLists):
    'takes a list of lists of affixes, and returns the list of union affixes'
    return [unorder(union(x)) for x in zip(*affixLists)]
#    return map(lambda x,y: unorder(union([x,y])), group1, group2)


#----------------------------------------------------------------#

def sublist(L, indices):
    'takes a list L and outputs a sublist from L whose indices in L are specified'
    tempList = list()
    for i in indices:
        tempList.append(L[i])
    return tempList

#----------------------------------------------------------------#

def improvedSourceWord(sourceWord, bestIndexList):
    # to color-code the stem, prefix, infix, and suffix in the "improvedSourceWord"
    # in the surface word, the best stem characters are in black
    s = ''
    for (k,c) in enumerate(sourceWord):
        if k not in bestIndexList:
            # if c is an affix letter

            # check where c is
            # (on all stem letters' left-hand side? on the right? or sandwiched in-between?)
            stemLetterPreceding = False
            stemLetterFollowing = False
            for j in bestIndexList:
                if j < k:
                    stemLetterPreceding = True
                    break
            for j in bestIndexList:
                if j > k:
                    stemLetterFollowing = True
                    break

            if stemLetterPreceding and stemLetterFollowing:
                s += '{\\bf \\color{OliveGreen}' + c + '}'
            elif stemLetterPreceding:
                s += '{\\bf \\color{Blue}' + c + '}'
            elif stemLetterFollowing:
                s += '{\\bf \\color{Red}' + c + '}'
            else:
                s += '{\\bf \\color{RedOrange}' + c + '}'
        else:
            # if c is a stem letter
            s += c
    return s



#----------------------------------------------------------------#
class node:
    def __init__(self, i, daughterLeaves=None, mother=None, daughter1=None, daughter2=None,
                 leftDaughterLeaves=None, rightDaughterLeaves=None, costSaved=None):
        self.MyIndex = i
        self.MyMother = mother
        self.MyDaughterLeaves = daughterLeaves
        self.MyLeftDaughter = daughter1
        self.MyRightDaughter = daughter2
        self.MyLeftDaughterLeaves = leftDaughterLeaves
        self.MyRightDaughterLeaves = rightDaughterLeaves
        self.MyCostSaved = costSaved


#----------------------------------------------------------------#
class Stemplex:
    def __init__(self, L, rowNumber):
        self.MyDirtyFlag = False

        self.MySourceRowList = [L[1:]]
        self.MyRowNumberList = [rowNumber]

        # alphabetize all source words in the paradigm
        unorderL = [unorder(x) for x in L[1:]]

        # find the stem
        shortWord = shortest(L[1:])[0] # need shortWord for function "reorder"
        shortWordUnorder = unorder(shortWord)
        stem = ''
        for l in shortWordUnorder:
            AllExist = True # whether l exists in each of the words in unorderL
            for w in unorderL:
                if l not in w:
                    AllExist = False
                    break
            if AllExist:
                stem += l
                unorderL = [w.replace(l,'',1) for w in unorderL]

        self.MyStemList = [stem]
        self.MyTargetsList = [[unorder(x) for x in L[1:]]]
        self.MyOriginalAffixesList = [unorderL]
        self.MyAffixes = unorderL

        ###########################################################################
        # compute the 'improved' source row with coloring of the surface word forms
        # for stem, prefix, infix, suffix
        ###########################################################################

        ###########################################################################
        # ALGORITHM 1:
        # use bags of letters from stem, find their best match in each word form

        sourceRow = L[1:]
        stemSet = ''.join(set(unorder(stem)))
        improvedSourceRow = list()
        indicesToLocateStemCharMasterList = list()

        # for every surface word
        for sourceWord in sourceRow:
            indicesToLocateStemCharList = [[]]
            candidateStemList = list()

            # go through every character in the set of stem characters and see where it is in the surface word
            # indicesToLocateStemCharList is a list of the index lists
            temp = False
            for stemChar in stemSet:
                sourceWordLetterIndices = [k for (k,c) in enumerate(sourceWord) if c == stemChar]
                numberOfCharInStem = stem.count(stemChar)
                combinationsList = list(itertools.combinations(sourceWordLetterIndices, numberOfCharInStem))

                if sourceWord == 'xxx':
                    temp = True
                    print 'sourceWord', sourceWord
                    print 'stem', self.MyStemList[e]
                    print 'stemChar', stemChar
                    print 'sourceWordLetterIndices', sourceWordLetterIndices
                    print 'numberOfCharInStem', numberOfCharInStem
                    print 'combinationsList', combinationsList
                    print 'tempIndices', indicesToLocateStemCharList
                while len(indicesToLocateStemCharList) < len(combinationsList):
                    indicesToLocateStemCharList.append(indicesToLocateStemCharList[0])
                while len(combinationsList) < len(indicesToLocateStemCharList):
                    combinationsList.append(combinationsList[0])
                if temp:
                    print 'temp2-indices', indicesToLocateStemCharList
                for (k,combin) in enumerate(combinationsList):
                    indicesToLocateStemCharList[k] = indicesToLocateStemCharList[k] + list(combin)
                if temp:
                    print 'indices-endOfIteration', indicesToLocateStemCharList
                    print

            if temp:
                print '\nindices', indicesToLocateStemCharList
                raw_input()

            # sort each index list in indicesToLocateStemCharList
            # also create the stem according to each set of indices
            for (k,indexList) in enumerate(indicesToLocateStemCharList):
                indicesToLocateStemCharList[k] = sorted(indexList)
                s = ''
                for i in indicesToLocateStemCharList[k]:
                    s += sourceWord[i]
                candidateStemList.append(s)
                indicesToLocateStemCharMasterList.append(indicesToLocateStemCharList)

            # find the best list of indices of characters in surface word that correspond to stem characters
            # "best" defined as the case where all stem letters are the most close/adjacent to one another
            cList = list()
            for indexList in indicesToLocateStemCharList:
                c = 0
                for k in range(1,len(indexList)):
                    c += indexList[k] - indexList[k-1]
                cList.append(c)

            # check if there are ties in cList
            if temp:
                print 'cList.count(min(cList)) <= 1', cList.count(min(cList)) <= 1
            if cList.count(min(cList)) <= 1:
                # if there are no ties:
                bestIndexList = indicesToLocateStemCharList[cList.index(min(cList))]
            else:
                # if there are ties:
                candidateIndexList = [indicesToLocateStemCharList[k] for (k,c) in enumerate(cList) if c == min(cList)]
                candidateStemInSourceWordList = list()
                for candidateIndices in candidateIndexList:
                    tempWord = ''
                    for i in candidateIndices:
                        tempWord += sourceWord[i]
                    candidateStemInSourceWordList.append(tempWord)
                candidateScoreList = list()
                if temp:
                    print 'candidateIndexList', candidateIndexList
                    print 'candidateStemInSourceWordList',candidateStemInSourceWordList
                for candidateStem in candidateStemInSourceWordList:
                    c = 0
                    for s in sourceRow:
                        if candidateStem in s:
                            c += 1
                    candidateScoreList.append(c)
                bestIndexList = candidateIndexList[candidateScoreList.index(max(candidateScoreList))]
            if temp:
                print 'cList', cList
                print 'bestIndexList', bestIndexList
                raw_input()

            improvedSourceRow.append(improvedSourceWord(sourceWord, bestIndexList))

        self.MyImprovedSourceRowList = [improvedSourceRow]

        # based on indicesToLocateStemCharMasterList, 

        improvedSourceRowBagOfSymbols = list()
        for (sourceWord, multipleIndexList) in zip(sourceRow, indicesToLocateStemCharMasterList):
            tempList = list()
            for indexList in multipleIndexList:
                tempList.append(improvedSourceWord(sourceWord, indexList))
            improvedSourceRowBagOfSymbols.append(tempList)

        self.MyImprovedSourceRowBagOfSymbolsList = [improvedSourceRowBagOfSymbols]
        # [ [xxx, xxx, ..]_forSourceWord1, [xxx, xxx, ..]_forSourceWord2, .. ]

        ### end of ALGORITHM 1 ###
        #####################################################################

        #####################################################################
        # ALGORITHM 2:
        # among all word forms in a paradigm, find the longest common subsequence(s)

        KEYstemVALUEindicesInWordDICT = dict()
            # { (stemletter1, stemletter2, ... ) : [ indexList1, indexList2 ] }
            # ideally, there's only one tuple of (stemletter1, stemletter2, ... ), for only one longest common subsequence

        improvedSourceRowDict = dict()
            # { (stemletter1, stemletter2, ... ) : [ improvedWord1, improvedWord2 ] }
            # ideally, there's only one tuple of (stemletter1, stemletter2, ... ), for only one longest common subsequence

        lenOfLongestCommonSubsequence = 0
        found = False # whether a longest common subsequence is found or not

        for k in range(len(shortWord),0,-1):

            # exit this loop, if found is true and if all possibilities of the same longest stem length are checked
            if ( k < lenOfLongestCommonSubsequence ) and found:
                break

            stem_NchooseK_list = list(itertools.combinations(shortWord,k))

            # for all combinations of k stem letters, where k decrements from len(shortWord) to 1 inclusive
            for stem_NchooseK in stem_NchooseK_list:
                badCombination = False

                masterIndexList = list()
                for word in sourceRow:
                    indexList = list()
                    for letter in stem_NchooseK:
                        if letter not in word:
                            badCombination = True
                            break
                        else:
                            tempList = list()
                            for i in range(len(word)):
                                if word[i] == letter:
                                    tempList.append(i)
                            indexList.append(tempList)
                    if badCombination:
                        break
                    else:
                        masterIndexList.append(indexList)


                if badCombination:
                    continue
                else:
                    found = True
                    lenOfLongestCommonSubsequence = k
                    
                    KEYstemVALUEindicesInWordDICT[stem_NchooseK] = masterIndexList

        for stem_sequence in KEYstemVALUEindicesInWordDICT.keys():
            for (j, letterIndexList) in enumerate(KEYstemVALUEindicesInWordDICT[stem_sequence]):
                #e.g., letterIndexList:
                #[ [1,2], [3,6], [4] ]
                #size = 4 (2 x 2 x 1, multiplicative product of lengths of all sublists)

                letterIndexListByLen = [len(x) for x in letterIndexList]
                size = reduce(lambda x,y: x*y,letterIndexListByLen)

                indexMatrix = numpy.zeros((size,len(letterIndexList)), dtype=int)

                for (e,letterIndices) in enumerate(letterIndexList):

                    repeat = int(size)
                    for i in range(e+1):
                        repeat = repeat / len(letterIndexList[i])

                    counter = 0
                    while counter < size:
                        for letterIndex in letterIndices:
                            for i in range(repeat):
                                indexMatrix[counter,e] = letterIndex
                                counter += 1

                tempWordList = list()
                improvedSourceRowDict[stem_sequence] = list()

                for i in range(size):
                    numToStrList = [str(x) for x in list(indexMatrix[i])]
                    ascending = numToStrList == sorted(numToStrList)

                    if ascending:
                        tempWordList.append(improvedSourceWord(sourceRow[j],list(indexMatrix[i])))

                improvedSourceRowDict[stem_sequence].append(tempWordList)

        self.MyImprovedSourceRowDictList = [improvedSourceRowDict]



        # end of ALGORITHM 2
        #####################################################################

        #####################################################################
        # ALGORITHM 3:
        # among all word forms in a paradigm, find the longest common substring(s)

        goodStemList = list()

        for k in range(len(shortWord),0,-1):

            numOfPossibleStems = len(shortWord)-k+1
            # if len(shortWord) == 5 and k == 5, there's 1 possible stem
            # if len(shortWord) == 5 and k == 4, there are 2 possible stems

            possibleStemList = [shortWord[i:i+k] for i in range(numOfPossibleStems)]

            for possibleStem in possibleStemList:
                good = True # whether a possible stem is a substring common to ALL words in a paradigm
                for sourceWord in sourceRow:
                    if possibleStem not in sourceWord:
                        good = False
                        break
                if good:
                    goodStemList.append(possibleStem)

        try:
            lenOfLongestCommonSubstring = len(max(goodStemList, key=len))
            goodStemList = filter(lambda x : len(x) == lenOfLongestCommonSubstring, goodStemList)
        except ValueError:
            goodStemList = ['']
            lenOfLongestCommonSubstring = 0

        improvedSourceRowDict = dict()
            # { stem : [ [improvedWord1, improvedWord2, ...]_forSourceWord1, [improvedWord1, improvedWord2, ...]_forSourceWord2, ... ] }
            # ideally, there's only one stem, for only one longest common substring

        for goodStem in goodStemList:
            improvedWordMasterList = list()
            for sourceWord in sourceRow:
                improvedWordList = list()

                indexOfOccurrenceList = list()
                indexRecord = -1
                while True:
                    if sourceWord.find(goodStem, indexRecord+1) > -1:
                        indexOfOccurrenceList.append(sourceWord.find(goodStem, indexRecord+1))
                        indexRecord = sourceWord.find(goodStem, indexRecord+1) + 1
                    else:
                        break

                for indexOfOccurrence in indexOfOccurrenceList:
                    indices = [i for i in range(indexOfOccurrence, indexOfOccurrence+lenOfLongestCommonSubstring)]
                    improvedWordList.append(improvedSourceWord(sourceWord, indices))

                improvedWordMasterList.append(improvedWordList)

            improvedSourceRowDict[goodStem] = improvedWordMasterList

        self.MyImprovedSourceRowSubstringDictList = [improvedSourceRowDict]

        # end of ALGORITHM 3
        #####################################################################

        self.MyGrammarCost = 0
        self.MyCostMatrixList = []
        self.MyDataCost = 0
        self.MyTotalCost = 0
        self.updateEverything()

        # use the first word form in the data (usually the infinitive) as the paradigm's leaf
        self.MyTree = L[0]
        self.MyBareTree = L[0]
        self.MyCollapsedBareTree = L[0]
        self.MyLeaveList = [L[0]]
        self.MyCollapsedTree = ''

        # encode this stemplex as a node in a tree
        self.MyNodeIndex = 0

    #class Stemplex------------------------------------------------------------#

    def updateEverything(self):
        self.computeGrammarCost()
        self.computeCostMatrixList()
        self.computeDataCost()
        self.computeTotalCost()
        self.MyDirtyFlag = False

    def leaves(self):
        return self.MyLeaveList

#    def nodeIndex(self):
#        return self.MyNodeIndex

#    def nodeDaughters(self):
#        return self.MyNodeDaughters

#    def nodeMother(self):
#        return self.MyNodeMother

    def rowNums(self):
        return self.MyRowNumberList

    def sourceRows(self):
        return self.MySourceRowList

    def improvedSourceRows(self):
        return self.MyImprovedSourceRowList

    def improvedSourcedRowDictList(self):
        return self.MyImprovedSourceRowDictList

    def improvedSourceRowBagOfSymbolsList(self):
        return self.MyImprovedSourceRowBagOfSymbolsList

    def improvedSourcedRowSubstringDictList(self):
        return self.MyImprovedSourceRowSubstringDictList

    def stems(self):
        return self.MyStemList

    def targets(self):
        return self.MyTargetsList

    def originalAffixes(self):
        return self.MyOriginalAffixesList

    def affixes(self):
        return self.MyAffixes

    def tree(self):
        return self.MyTree

    def bareTree(self):
        return self.MyBareTree

    def collapsedBareTree(self):
        return self.MyCollapsedBareTree

    def collapsedTree(self):
        return self.MyCollapsedTree

    #class Stemplex------------------------------------------------------------#

    def affixMatrix(self):
        return numpy.array(self.affixes())

    #class Stemplex------------------------------------------------------------#

    def grammarCost(self):
        if self.MyDirtyFlag:
            self.updateEverything()
        return self.MyGrammarCost

    def computeGrammarCost(self):
#        self.MyGrammarCost = LAMBDA_BITS * (len(''.join(self.MyStemList)) + self.MyStemList.count('') + len(''.join(self.MyAffixes)) + self.MyAffixes.count('') + COLUMNS)
        self.MyGrammarCost = LAMBDA_BITS * (len(''.join(self.MyStemList)) + len(''.join(self.MyAffixes)) + COLUMNS)

    #class Stemplex------------------------------------------------------------#

    def costMatrixList(self):
        if self.MyDirtyFlag:
            self.updateEverything()
        return self.MyCostMatrixList

    def computeCostMatrixList(self):
        matrixList = list()
        for (e, stem) in enumerate(self.MyStemList):
            matrixForEachStem = numpy.zeros((COLUMNS,5), dtype=int)
            try:
                for k in range(COLUMNS):
                    matrixForEachStem[k] = cost(stem, self.MyAffixes[k], self.MyTargetsList[e][k])
            except:
                print 'self.MySourceRowList', self.MySourceRowList
                print 'matrixForEachStem', matrixForEachStem
                print 'e', e
                print 'k', k
                print 'COLUMNS', COLUMNS
                print 'self.MyAffixes', self.MyAffixes
                print 'self.MyTargetsList', self.MyTargetsList
                print 'self.MyAffixes[k]', self.MyAffixes[k]
                print 'matrixForEachStem[k]', matrixForEachStem[k]
                print 'self.MyTargetsList[e][k]', self.MyTargetsList[e][k]
                raw_input()
            matrixList.append(matrixForEachStem.T)
        self.MyCostMatrixList =  matrixList

    #class Stemplex------------------------------------------------------------#

    def dataCost(self):
        if self.MyDirtyFlag:
            self.updateEverything()
        return self.MyDataCost

    def computeDataCost(self):
        self.MyDataCost = sum([matrixForEachStem.sum() for matrixForEachStem in self.costMatrixList()])

    #class Stemplex------------------------------------------------------------#

    def totalCost(self):
        if self.MyDirtyFlag:
            self.updateEverything()
        return self.MyTotalCost

    def computeTotalCost(self):
        self.MyTotalCost = self.grammarCost() + self.dataCost()

    #class Stemplex------------------------------------------------------------#


    def merge(self, stmplx, newAlignment, mergeCount=None, costSaved=None, nodeDict=None, leftLeaves=None, rightLeaves=None):
        # When mergeCount==None, this merge() function is only *pretending* to merge two stemplexes,
        # because in this case the focus is the total cost (if merged), not really doing the merge.

        self.MyLeaveList += stmplx.leaves()
        self.MyStemList += stmplx.stems()
        self.MyRowNumberList += stmplx.rowNums()

        self.MySourceRowList += [[s[i] for i in newAlignment] for s in stmplx.sourceRows()]
        self.MyImprovedSourceRowList += [[s[i] for i in newAlignment] for s in stmplx.improvedSourceRows()]
        self.MyTargetsList += [[s[i] for i in newAlignment] for s in stmplx.targets()]
        self.MyOriginalAffixesList += [[s[i] for i in newAlignment] for s in stmplx.originalAffixes()]

        # createUnionAffixes() takes a list of two lists.
        # The second affix list is in its new alignment.
        self.MyAffixes = createUnionAffixes([self.affixes(), [stmplx.affixes()[i] for i in newAlignment]])

        self.updateEverything()

        if costSaved < 0:
            costSavedStr = '{\\color{red}' + str(costSaved) + '}'
        else:
            costSavedStr = str(costSaved)

        self.MyTree = '[.{' + str(mergeCount) + '$_{' + costSavedStr + '}$} ' + self.MyTree + ' ' + stmplx.tree() + ' ]'
        self.MyBareTree = '[ ' + self.MyBareTree + ' ' + stmplx.bareTree() + ' ]'

        # updating tree node information
#        self.MyNodeDaughters = (self.MyNodeIndex, stmplx.MyNodeIndex)
        self.MyNodeIndex = mergeCount


        if nodeDict:

            self.MyCollapsedTree = self.MyTree

            ###################################################################
            # create a collapsed tree, where paradigms that are morphologically
            # identical collapse if the following two conditions are met:
            #   1. they all are in the same subtree in self.MyTree
            #   2. their saved costs at each mother node inside are the same
            ###################################################################

            # locate nodes which:
            #  1. have only one leaf as left daughter and only one leaf as right daughter
            #  2. are the *right* daughter of another node
            #  3. have a sister node that consists only of one single leaf
            #
            #        mother
            #         /  \
            #      leaf  *SELF* <== locate
            #             /  \
            #           leaf  leaf

            candidateNodeList = list()

            for k in filter(lambda x: x < ROWS, nodeDict.keys()):
                print 'k', k
                print 'nodeDict[k].MyLeftDaughterLeaves', nodeDict[k].MyLeftDaughterLeaves
                print 'nodeDict[k].MyRightDaughterLeaves', nodeDict[k].MyRightDaughterLeaves
                print 'nodeDict[k].MyMother', nodeDict[k].MyMother
                if (nodeDict[k].MyLeftDaughterLeaves and nodeDict[k].MyRightDaughterLeaves and nodeDict[k].MyMother) and \
                   (len(nodeDict[k].MyLeftDaughterLeaves) == len(nodeDict[k].MyRightDaughterLeaves) == 1) and \
                   (nodeDict[nodeDict[k].MyMother].MyRightDaughter == k) and \
                   (len(nodeDict[nodeDict[k].MyMother].MyLeftDaughterLeaves) == 1):
                    candidateNodeList.append(k)

            print '\ncandidateNodeList', candidateNodeList

            collapseNodeList = [0] * len(candidateNodeList)
            # ^-- will contain the node indices for nodes to collapse, after the following for-loop

            for (e,k) in enumerate(candidateNodeList):
                currentNodeIndex = k
                currentNodeCostSaved = nodeDict[k].MyCostSaved

                while True and nodeDict[currentNodeIndex].MyMother:
                    motherNodeIndex = nodeDict[currentNodeIndex].MyMother
                    motherNodeCostSaved = nodeDict[nodeDict[currentNodeIndex].MyMother].MyCostSaved

                    # if...
                    #    1. my own cost saved == my mum's cost saved
                    #    2. my sister consists only of a single leaf
                    # then:
                    #    signal the merging of my mum and myself
                    # else:
                    #    leave this while loop

                    if (currentNodeCostSaved == motherNodeCostSaved) and \
                       (len(nodeDict[motherNodeIndex].MyLeftDaughterLeaves) ==  1):
                        collapseNodeList[e] = motherNodeIndex
                    else:
                        break

                    currentNodeIndex = motherNodeIndex
                    currentNodeCostSaved = motherNodeCostSaved

            print '\ncollapseNodeList:'
            print collapseNodeList#; raw_input()

            # collapseNodeList contains node indices for nodes to collapse
            # if node index == 0 in collapseNodeList, ignore it. (No node index can be 0.)

            # for each node to collapse
            #     find the corresponding subtree '[ ... ]' in self.MyTree (use technique of matching parentheses)

            for nodeIndex in filter(lambda x: x, collapseNodeList):
                search_str = '[.{' + str(nodeIndex) + '$'
                try:
                    subtree = self.MyTree[self.MyTree.index(search_str):]
                except ValueError: # when this nodeIndex is not relevant to the current merge
                    continue

                paren_count = 0
                for (e,char) in enumerate(subtree):
                    if char == '[':
                        paren_count += 1
                    elif char == ']':
                        paren_count -= 1
                    if paren_count == 0:
                        matchParenIndex = e
                        break

                replacee = subtree[:matchParenIndex+1]

#                print '\nreplacee', replacee; raw_input()

                replacer = '{\\begin{tabular}{|ll|} \\hline ' + \
                            ''.join([x+' \\\ ' if e % 2 else x+' & ' for (e,x) in enumerate(nodeDict[nodeIndex].MyDaughterLeaves)]) + \
                            '#\\hline \\end{tabular}} '
                if len(nodeDict[nodeIndex].MyDaughterLeaves) % 2:
                    replacer = replacer.replace('#','\\\ ')
                else:
                    replacer = replacer.replace('#',' ')

                self.MyCollapsedTree = self.MyCollapsedTree.replace(replacee, replacer)
                if '[' not in self.MyCollapsedTree:
                    self.MyCollapsedTree = '[ ' + self.MyCollapsedTree + ' ]'

        self.MyCollapsedBareTree = ' '.join([x if x[0] != '[' else '[' for x in self.MyCollapsedTree.split()])

    #class Stemplex------------------------------------------------------------#

    def printTerminal(self):
        print 'Row numbers:', self.rowNums()
        print 'Source rows:', self.sourceRows()
        print 'Number of rows:', len(self.rowNums())
        print 'Stems:', self.stems()
        print 'Targets:', self.targets()
        print 'Original affixes:', self.originalAffixes()
        print 'Affixes:', self.affixes()
        print 'grammar cost:', self.grammarCost()
        print 'data cost:', self.dataCost()
        print 'total cost:', self.totalCost()
        print 'tree:', self.tree()
        print 'cost matrix:', self.costMatrixList()
        print


    #class Stemplex------------------------------------------------------------#


    def printlatex(self, latexfile):

        # -----------------------------------
        #  print the tree
        # -----------------------------------
        #latexfile.write('\\begin{landscape}\n')
        latexfile.write('%s\n\n' % (latexfile.name))
        latexfile.write('\\normalsize{\n\n')
        latexfile.write('\\Tree ')
        latexfile.write(self.tree())
        latexfile.write('\\\ \n\n')
        latexfile.write('\\Tree ')
        latexfile.write(self.collapsedTree())
        latexfile.write('\\\ \n\n')
        latexfile.write('\\Tree ')
        latexfile.write(self.bareTree())
        latexfile.write('\\\ \n\n')
        latexfile.write('\\Tree ')
        latexfile.write(self.collapsedBareTree())
        latexfile.write('\\\ \n')
        latexfile.write('} % end of non-normal font size\n')
        latexfile.write('\\end{landscape}\n')
#        latexfile.write('\\newpage\n')

        latexfile.write('\\begin{longtable}[l]{%s}\n\\toprule\n' % ('l'+'l'*(COLUMNS*2)))

        # -----------------------------------
        #  print alignment results in words
        # -----------------------------------
        for (stem, rowSourceWords) in zip(self.stems(), self.improvedSourceRows()):
            latexfile.write('{\\color{red} %s} & ' % (null(stem)))
            latexfile.write('%s \\\ \n' %
               (' & '.join(['\\multicolumn{2}{r}{'+x+'}' for x in rowSourceWords])))
        latexfile.write('\\toprule\n')

        # ---------------------
        #  print union affixes
        # ---------------------
        for unionAffix in self.affixes():
            latexfile.write('& \\multicolumn{2}{r}{\\color{red}-%s-} ' % (null(unionAffix)))
        latexfile.write('\\\ \n\\toprule\n')

        # ---------------------------------------------------------------------
        #  for each paradigm, print:
        #
        #  STEM     (AFFIX,TARGET)  (AFFIX,TARGET)  (AFFIX,TARGET)...
        #            __________________________________________________
        #           |            5xk cost matrix here                  |
        #           |__________________________________________________|
        # ---------------------------------------------------------------------
        for (e, stem) in enumerate(self.stems()):
            if e:
                latexfile.write('\\toprule\n')

            # print Stem 
            latexfile.write('{\\color{red} %s} ' % (null(stem)))

            # print { (Affix,Target), (Affix,Target), ...}
            for k in range(COLUMNS):
                latexfile.write('& (%s, & %s) ' % (null(self.originalAffixes()[e][k]),
                                                   self.targets()[e][k]))
            latexfile.write('\\\ \n')

            # print costMatrix
            costMatrix = self.costMatrixList()[e]
            wordDataCostVector = costMatrix.sum(axis=0) # axis=0 to get vertical sums
            for line in costMatrix: # there are 5 lines in self.costMatrixList()[e]
                for pointCost in line: # pointCost = cell cost in costMatrix
                    latexfile.write('& & %d ' % (pointCost))
                latexfile.write('\\\ \n')
            latexfile.write('\\midrule\n')
            latexfile.write('{\\color{blue} %d} ' % (self.costMatrixList()[e].sum()))
            for wordDataCost in wordDataCostVector:
                latexfile.write('& & %d ' % (wordDataCost))
            latexfile.write('\\\ \n')

        latexfile.write('\\bottomrule\n\\end{longtable}\n\n')

        # ----------------------
        # -- print cost summary
        # ----------------------

#        latexfile.write('Data cost = %d ({\\color{blue}%d}+{\\color{blue}%d}+{\\color{blue}%d})\\\ '
#                % (sum(dataCost), dataCost[0], dataCost[1], dataCost[2]))
        latexfile.write('Total cost = %d\n\n' % (self.totalCost()))
        latexfile.write('Grammar cost = %d\n\n' % (self.grammarCost()))
        latexfile.write('Data cost = %d\n\n' % (self.dataCost()))


        # latexfile.write('\\end{landscape}\n')
        latexfile.write('\\break\n\n')

    # END of class Stemplex----------------------------------------------------#


################################################################################

######################
#### Main Program ####
######################

#----------------#
# initialization #
#----------------#

"""
Initialize:

    source          : list of original paradigm data

    stemplexList    : list of stemplexes

    pairSavedCost    : key   = cost saved after collapse
                      value = (rowNumber1, rowNumber2)

"""


doAlignment = raw_input('do alignment? (\'y\' for yes) ')


##--- end of initialization ----------------------------------------------------#


print '\ndata file:', fname
print

###########################
# write the latex preamble in "latexfile"

latexfile = open(latexfilename, 'w')

latexfile.write('\\documentclass{article}\n')
latexfile.write('\\usepackage{longtable}\n')
latexfile.write('\\usepackage[paperwidth=17in, paperheight=22in, margin=.1in]{geometry}\n')
#latexfile.write('\\usepackage{arydshln}\n')
latexfile.write('\\usepackage[usenames,dvipsnames]{color}\n')
latexfile.write('\\usepackage{qtree}\n')
latexfile.write('\\usepackage{lscape}\n')
latexfile.write('\\usepackage{booktabs}\n\n')
latexfile.write('\\setlength{\\parindent}{0pt}\n\n')

latexfile.write('\\begin{document}\n\n')

latexfile.write('\\qtreepadding=0.5pt\n')

#latexfile.write('\\normalsize{\n\n')

#latexfile.write('\\begin{landscape}\n')

# end of writing the latex preamble
###########################

# get data from .txt to the list "source"
source = readCSV(fname)

print 'ROWS:', ROWS
print 'COLUMNS:', COLUMNS

#    raw_input()
#    source = source[:ROWS]

costSavedMasterList = []


# initialize all stemplexes
stemplexList = []
treeNodeList = list()
treeNodeDict = dict()
for i in range(ROWS):
    StcxComplex = Stemplex(source[i],i)
    StcxComplex.MyNodeIndex = i+ROWS
    stemplexList.append(StcxComplex)
    treeNodeList.append(node(i+ROWS, [StcxComplex.tree()]))
    treeNodeDict[i+ROWS] = node(i+ROWS, [StcxComplex.tree()])

stemplexListCopy = copy.deepcopy(stemplexList)

stemList = [stemplexList[n].tree() for n in range(ROWS)]
for i in range(len(stemList)):
    if stemList[i] == '{\\O}':
        stemList[i] = 'NULL'

pairSavedCost = dict() # key: (rowNum1, rowNum2)      value: cost
rowNumPairList = list(itertools.combinations(range(ROWS),2))
permAlignments = [list(x) for x in list(itertools.permutations(range(COLUMNS)))]
if doAlignment != 'y':
    permAlignments = [range(COLUMNS)]

c = 0
rowToUpdate = -1
costSavedList = []

while True:

    # for rows {1,2,..,5}, we have 10 pairs of rows (by n choose 2)
    # when rows (1,2) have been merged
    # -- update (1,3), (1,4), (1,5), because all these involve rowNum1
    # -- delete (2,3), (2,4), (2,5), because all these involve rowNum2
    # -- and it's useful to keep all other pairs (esp. when n is large)

    # functions of the for-loop below:
    # -- 1. initialize all entries in pairSavedCost when c == 1 (i.e., only the very first while-loop iteration)
    # -- 2. when c > 1, update only entries in pairSavedCost which:
    #       --- involves rowToUpdate (the row that has just been updated in the preceding while-loop iteration), and
    #       --- does NOT involve all rows that have already been deleted (i.e., set as "None")

    c += 1
    print 'Merge count =', c
    for (x, y) in rowNumPairList:
        print 'Merge count: %d, pair: (%d, %d)' % (c,x,y)
        if (c == 1) or ( (c > 1) and (x == rowToUpdate) and (stemplexList[y] != None) ):
            costNoCollapse = stemplexList[x].totalCost() + stemplexList[y].totalCost()
#                    costCollapse = 10000
            costCollapse = costNoCollapse + 10000

            # goal of this for-loop below: minimize costCollapse
#                    kFactorialCostDict = dict()
            for (e,indices) in enumerate(permAlignments):
                clonedStemplex = copy.deepcopy(stemplexList[x])
                clonedStemplex.merge(stemplexList[y], indices)
#                        kFactorialCostDict[e] = clonedStemplex.totalCost()
                if clonedStemplex.totalCost() < costCollapse:
                    costCollapse = clonedStemplex.totalCost()
                    bestIndices = indices
                    largestStmplxSize = len(clonedStemplex.leaves())
#                        elif clonedStemplex.totalCost() == costCollapse:
#                            print 'tie!!'
#                            print bestIndices, indices
#                            raw_input()
#                    print sorted([(v,k) for (k,v) in kFactorialCostDict.items()]); raw_input()

            pairSavedCost[((x, y), tuple(bestIndices), largestStmplxSize)] = costNoCollapse - costCollapse

    if c == 1:
        stemplexSimilarity = dict()
        for (k,v) in pairSavedCost.items():
            stemplexSimilarity[k[0]] = v



    ## each member of pairSavedCost_sorted: ( saved cost, ( (rowNum1,rowNum2), indices, largestStmplxSize ) )
    pairSavedCost_sorted = sorted([(v,k) for (k,v) in pairSavedCost.items()], reverse=True)
#            print pairSavedCost_sorted[:3]

    ## check if lowest saved cost is unique
    savedCostList = [x[0] for x in pairSavedCost_sorted]
    stmplxSizeList = [x[1][2] for x in pairSavedCost_sorted]

    lowestSavedCostList = [savedCostList[0]]
    for savedCost in savedCostList[1:]:
        if savedCost == lowestSavedCostList[0]:
            lowestSavedCostList.append(savedCost)
        else:
            break

    ## if lowest saved cost is not unique, pick pairToCollapse by largest stemplex size
    if len(lowestSavedCostList) > 1:
        stmplxSizeSublist = stmplxSizeList[:len(lowestSavedCostList)]
        best = pairSavedCost_sorted[stmplxSizeSublist.index(max(stmplxSizeSublist))]
    else:
        best = pairSavedCost_sorted[0]

    costSaved = best[0]
    print 'Cost saved:',
    print costSaved
    costSavedList.append(costSaved)

    PairToCollapse = best[1][0] # ( saved cost, ( ***(rowNum1,rowNum2)***, indices, largestStmplxSize ) )
    rowToUpdate = PairToCollapse[0]
    rowToDelete = PairToCollapse[1]
    newIndices = list(best[1][1])  # ( saved cost, ( (rowNum1,rowNum2), ***indices***, largestStmplxSize ) )

    print 'rowToUpdate:', rowToUpdate
    print 'rowToDelete:', rowToDelete
    print

    # get new tree node info before actual merging
    newLeftDaughterIndex = stemplexList[rowToUpdate].MyNodeIndex
    newRightDaughterIndex = stemplexList[rowToDelete].MyNodeIndex

#        newLeftDaughterLeaves = stemplexList[rowToUpdate].MyLeaveList
#        newRightDaughterLeaves = stemplexList[rowToDelete].MyLeaveList

    newLeftDaughterLeaves = treeNodeDict[newLeftDaughterIndex].MyDaughterLeaves
    newRightDaughterLeaves = treeNodeDict[newRightDaughterIndex].MyDaughterLeaves

    for treeNode in treeNodeList:
        if treeNode.MyIndex in [newLeftDaughterIndex, newRightDaughterIndex]:
            treeNode.MyMother = c
    for k in treeNodeDict.keys():
        if k in [newLeftDaughterIndex, newRightDaughterIndex]:
            treeNodeDict[k].MyMother = c

#    def __init__(self, i, daughterLeaves=None, mother=None, daughter1=None, daughter2=None, leftDaughterLeaves=None, rightDaughterLeaves=None, costSaved=None):

    treeNodeList.append(node(c, newLeftDaughterLeaves+newRightDaughterLeaves, None, newLeftDaughterIndex, newRightDaughterIndex, newLeftDaughterLeaves, newRightDaughterLeaves, costSaved))
    treeNodeDict[c] = node(c, newLeftDaughterLeaves+newRightDaughterLeaves, None, newLeftDaughterIndex, newRightDaughterIndex, newLeftDaughterLeaves, newRightDaughterLeaves, costSaved)

#        print newLeftDaughterIndex
#        print newRightDaughterIndex
#        print newLeftDaughterLeaves
#        print newRightDaughterLeaves
#        raw_input()

    # **********************
    # *** ACTUAL MERGING ***
    # **********************

    # use Merge in stemplex class to get the first "grouplex"
    # e.g., If (9,10) is best to merge, update stemplex rowNum 9 with new materials from rowNum 10

    stemplexList[rowToUpdate].merge(stemplexList[rowToDelete], newIndices, c, costSaved, treeNodeDict)

#       print stemplexList[rowToUpdate].tree()
#       print filter(lambda x: x[0] not in ['[', ']'], stemplexList[rowToUpdate].tree().split())

#    printTerminal(stemplexList[rowToUpdate])
#    raw_input()

    # print data filename and cost parameters to latex
    latexfile.write('\\begin{landscape}\n')
    latexfile.write('%s\n\n' % (time.strftime("%Y-%m-%d %H:%M:%S", time.localtime()) + ' CST'))

    latexfile.write('data: %s\n\n' % (fname))

    latexfile.write('StemUsed = %d\n\n' % (STEM_USED))
    latexfile.write('StemNotUsed = %d\n\n' % (STEM_NOT_USED))
    latexfile.write('AffixUsed = %d\n\n' % (AFFIX_USED))
    latexfile.write('AffixNotUsed = %d\n\n' % (AFFIX_NOT_USED))
    latexfile.write('Extra = %d\n\n' % (EXTRA))

    # if randomClustering is 'y':
    #       print stuff to latex only when it is the *final* tree
    stemplexList[rowToUpdate].printlatex(latexfile)

    # delete the stemplex that has been merged to another stemplex (e.g., delete rowNum10)
    stemplexList[rowToDelete] = None

    # delete also entries that contain the deleted row (e.g. rowNum 10) in pairSavedCost
    for entry in pairSavedCost_sorted:
        rowPair = list(entry[1][0])
        key = entry[1]
        if rowToDelete in rowPair:
            del pairSavedCost[key]

    # merging is done if there's only one stemplex left
    if len(set(stemplexList)) <= 2:
        break

costSavedMasterList.append(costSavedList)
print 'Costs saved:', sorted(costSavedList, reverse=True)
print 'Total cost saved =', sum(costSavedList)

# raw_input()





# print tree node info to text file

#fnode = open('nodesFinal.csv','w')
#print >>fnode, 'index\tmother\tdaughters1\tdaughters2\tleaves1\tleaves2'
#nodeList = sorted(treeNodeDict.items())[:ROWS-1]
#for (nodeIndex, nodeContent) in nodeList:
#    print >>fnode, nodeIndex, '\t', nodeContent.MyMother, '\t', nodeContent.MyLeftDaughter, '\t', nodeContent.MyRightDaughter, '\t',
#    if nodeContent.MyLeftDaughterLeaves:
#        print >>fnode, ' '.join(nodeContent.MyLeftDaughterLeaves), '\t',
#    else:
#        print >>fnode, nodeContent.MyLeftDaughterLeaves, '\t',
#    if nodeContent.MyRightDaughterLeaves:
#        print >>fnode, ' '.join(nodeContent.MyRightDaughterLeaves)
#    else:
#        print >>fnode, nodeContent.MyRightDaughterLeaves
#fnode.close()


latexfile.write('\\end{document}\n')
latexfile.close()


print 'All done!\n'
print 'latex file name: ', latexfilename
print


subprocess.call(('latex', latexfilename))
subprocess.call(('latex', latexfilename))
subprocess.call(('dvipdf', latexfilename[:-4]+'.dvi'))
