import math
import time
from pprint import pprint
import copy
from itertools import combinations

start_time = time.time()
f = open("input10.txt","r")

query_List = []
kb_List = []

iter = 0
deadline_for_queries = 0
deadline_for_statements = 0
flag_input = True

set_KB = set()
Dict_Quer = dict()
rev_Dict = dict()

for line in f.readlines():
    if (iter == 0 and flag_input):
        deadline_for_queries = int(line)
        flag_input = False
    elif (iter < deadline_for_queries):
        query = line.rstrip()
        query = query.replace(" ","")
        query_List.append(query)
        iter += 1
    elif (iter == deadline_for_queries):
        deadline_for_statements = int(line)
        iter += 1
    elif (iter < deadline_for_statements+deadline_for_statements+2):
        statement = line.rstrip()
        statement = statement.replace(" ","")
        kb_List.append(statement)
        iter += 1


# definition of isLower
def is_variable(x):
    get_first_char = x[0]
    if(get_first_char.islower()):
        return True
    else:
        return False


def negate_Pred_imp(x):
    to_ret = ""
    first_Elem = x[0]
    if(first_Elem  == '~'):
        to_ret = x[1:]
    else:
        to_ret = "~"+x
    return to_ret

def standardize_Initial(var_List,Sno,subst_List,var_hm,curr_position):
    c = 0
    for var in var_List:
        if (is_variable(var)):
            if (var in var_hm):
                get_sub = var_hm[var]
                to_add = get_sub + str(Sno)
                var_List[c] = to_add
            else:
                substitution = subst_List[curr_position[0]]
                curr_position[0] = curr_position[0] + 1
                var_hm[var] = substitution
                var_List[c] = substitution + str(Sno)
        c += 1


def add_to_dict_imp(x,implication_Const,sentence_no):
    temp_list = x.partition(implication_Const)
    # partitioned at implication sign and we got 3 terms

    before_implication = temp_list[0]
    # first part which we have to do negate for all predicate and they all will be in or form

    after_implication = temp_list[2]
    # second half after the implication sign which will be a single predicate

    before_implication = before_implication.split('&')
    # split the first half at all the and

    sentence_set = set()
    # for every element in before implication that is every predicate and var relation

    # All of the following for standardization
    var_hm = dict()
    curr_position = [0,"currpos"]
    subst_List = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t","u", "v", "w", "x", "y", "z"]

    for elem in before_implication:

        temp = elem.partition("(")
        # predicate  is literally the predicate

        predicate = temp[0]
        predicate = negate_Pred_imp(predicate)

        new_part = temp[2].partition(")")
        # THIS IS THE PART x,y) this one
        # new part has all the variables of the predicate
        var_and_const = new_part[0].split(",")

        standardize_Initial(var_and_const,sentence_no,subst_List,var_hm,curr_position)
        # curr_position[0] = 0

        is_simplified = True

        for all_var in var_and_const:
            if(is_variable(all_var)):
                is_simplified = False
                break

        var_and_const = tuple(var_and_const)
        # print(var_and_const)
        tuple_for_singlepred = (predicate,var_and_const,is_simplified)

        sentence_set.add(tuple_for_singlepred)
        # new part is an array of all the var or constants

    # print(after_implication," after implication")
    rhs = after_implication.partition("(")
    pred_rhs = rhs[0]

    var_rhs = rhs[2].partition(")")[0].split(",")

    standardize_Initial(var_rhs, sentence_no, subst_List, var_hm, curr_position)

    is_simp_rhs = True
    for all_v in var_rhs:
        if(is_variable(all_v)):
            is_simp_rhs = False
            break
    var_rhs = tuple(var_rhs)
    tup_rhs = (pred_rhs,var_rhs,is_simp_rhs)
    sentence_set.add(tup_rhs)

    sentence_set = frozenset(sentence_set)
    # print(set_KB)
    set_KB.add(sentence_set)
    # Dict_KB[sentence_no] = sentence_set

def add_to_dict_general(x,sentence_no):
    var_hm = dict()
    curr_position = [0, "currpos"]
    subst_List = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t","u", "v", "w", "x", "y", "z"]

    # print("I am a mess")
    temp_list = x.partition("(")
    # partitioned at ( and we got 3 constants
    pred = temp_list[0]
    # first part which we have predicate

    var_sent = temp_list[2]
    # second half

    all_var_list = var_sent.partition(')')[0].split(",")
    # split the first half at all the and

    standardize_Initial(all_var_list, sentence_no, subst_List, var_hm, curr_position)

    sentence_set = set()

    is_Simplified = True

    for vari in all_var_list:
        if(is_variable(vari)):
            is_Simplified = False
            break

    all_var_list = tuple(all_var_list)

    tuple_for_sent_k = (pred,all_var_list,is_Simplified)
    sentence_set.add(tuple_for_sent_k)

    sentence_set = frozenset(sentence_set)
    set_KB.add(sentence_set)


def get_sentence_Dict():
    statement_number = 1
    implication_Const = "=>"

    for x in kb_List:
        # first check if it is a sentence with implication
        if(implication_Const in x):
            add_to_dict_imp(x,implication_Const,statement_number)
        else:
            add_to_dict_general(x,statement_number)
        statement_number += 1

    # print(set_KB)

def get_query_Dict():
    quer_no = 1
    for quer in query_List:
        temp = quer.partition("(")
        pred_of_quer = negate_Pred_imp(temp[0])
        # pred_of_quer = "~"+temp[0]
        # get the variables of the query
        var_of_quer = temp[2].partition(")")[0].split(",")
        is_Simplified = True
        for vari in var_of_quer:
            if (len(vari) == 1 and vari.islower()):
                is_Simplified = False
                break

        var_of_quer = tuple(var_of_quer)
        tuple_of_quer = (pred_of_quer,var_of_quer,is_Simplified)
        Dict_Quer[quer_no] = tuple_of_quer

        quer_no += 1


get_query_Dict()
get_sentence_Dict()


def is_var(val):
    valcheck = val[0]
    if(valcheck.islower()):
        return True
    else:
        return False

def unification(list_x,list_y):
    theta = dict()
    for i,j in zip(list_x,list_y):
        unify(i+",0",j+",1",theta)

    # list_x is 0 indexed and list_y is 1 indexed
    zero_indexed_List = list()
    one_indexed_List = list()

    zero_indexed_List = copy.deepcopy(list_x)
    one_indexed_List = copy.deepcopy(list_y)

    c = 0
    for vals in zero_indexed_List:
        # agar vo var hai to uski jo replacement ai h daaldo
        if (is_variable(vals)):
            toS = vals+",0"
            if toS in theta:
                replacement = theta[toS]
                zero_indexed_List[c] = replacement


        c += 1

    # print(zero_indexed_List,"Zero")

    c = 0
    for vals in one_indexed_List:
        if (is_variable(vals)):
            toS = vals + ",1"
            if toS in theta:
                replacement = theta[toS]
                # print(replacement, "this is the replcaement for FOR YOUU BITCHHH ", toS)
                one_indexed_List[c] = replacement


        c += 1
    # print(one_indexed_List,"One")

    # print(zero_indexed_List,"0 l and 1 l",one_indexed_List)
    checker = True

    for yaya,kolo in zip(zero_indexed_List,one_indexed_List):
        if "," in yaya:
            temp_x = yaya.split(",")
            yaya = temp_x[0]
            # print(yaya)
        if "," in kolo:
            temp_y = kolo.split(",")
            kolo = temp_y[0]

        # check for the constant --> If both constant and not equal
        if((not is_variable(yaya)) and (not is_variable(kolo)) and yaya != kolo):
            return (False,None)


    return (True,theta)


def unify(x, y, subst):
    if subst is None:
        return None
    elif x == y:
        return subst
    elif is_var(x):
        return unify_variable(x,y,subst)
    elif is_var(y):
        return unify_variable(y,x,subst)


def unify_variable(v,x,subst):
    if v in subst:
        return unify(subst[v],x,subst)
    elif is_var(x) and x in subst:
        return unify(v,subst[x],subst)
    else:
        subst[v] = x
        return subst


print(unification(["a0","b0","a0","a0","b0"],["Tim","a1","b1","b1","c1"]),"kolo toure 9")
print(unification(["a0","a0"],["Tim","Kanta"]),"Solo lole 2")
print(unification(["a0","a0"],["a1","b1"]),"Solo lole 233")


def negate_Pred(x):
    to_ret = ""
    first_Elem = x[0]
    if(first_Elem  == '~'):
        to_ret = x[1:]
    else:
        to_ret = x
    return to_ret

def add_to_KBcopy(sentenceSet,query_FS):
    sentenceSet.add(query_FS)

def is_Opp(pred1,pred2):
    if (pred1 == negate_Pred_imp(pred2)):
        return True
    elif (negate_Pred_imp(pred1) == pred2):
        return True
    else:
        return False

def get_Subval(subst_dict, v):

    while True:
        value = subst_dict[v]
        v = value
        if v not in subst_dict:
            return value

def standardize_Sent(sentence,id,substitution_Dict,check):
    # print("lolfgtghthgththythythyhnyhyhyhythtybhyb----------->>>>>>>>>")
    if(len(sentence)==0):
        return set()
    # if(id =="1"):
    #     print("id 2 hai")

    new_sentence = set()

    for predicate in sentence:
        # print("loop")
        new_Predlist = list()
        variable_List = list(predicate[1])

        # print(variable_List)
        ct = 0

        for var in variable_List:

            standardize_var = var + "," + id
            if (is_variable(var)):
                if standardize_var in substitution_Dict:
                    val = get_Subval(substitution_Dict,standardize_var)
                    variable_List[ct] = val.split(",")[0]
            else:
                variable_List[ct] = var


            ct += 1

        is_simplified = True
        for allVar in variable_List:
            if(is_variable(allVar)):
                is_simplified = False
                break
        new_pred = (predicate[0], tuple(variable_List), is_simplified)
        # new_pred = (predicate[0], tuple(variable_List), predicate[2])
        new_sentence.add(new_pred)

    return new_sentence


def substitution(sentence1,sentence2,substitution_Dict,pred_Res1,pred_Res2):
    count = 0
    # here I got 2 Frozen sets now convert them into list
    sentence1 = list(sentence1)
    sentence2 = list(sentence2)


    for pred in sentence1:
        if (pred == pred_Res1):
            del(sentence1[count])
            break
        count += 1

    count = 0

    for pred in sentence2:
        if(pred == pred_Res2):
            del(sentence2[count])
            break
        count += 1


    if(len(sentence1) == 0 and len(sentence2) == 0):
        return (True,{})

    first_Half = standardize_Sent(sentence1,"0",substitution_Dict,True)
    second_Half = standardize_Sent(sentence2,"1",substitution_Dict,False)

    final_ans = set()
    for i in first_Half:
        final_ans.add(i)
    for j in second_Half:
        final_ans.add(j)

    final_ans = frozenset(final_ans)

    return (False,final_ans)


def Resolve(sent1,sent2):
    to_return = set()

    # sentence1 and 2 are frozen sets frozenset({(pred,(tup of var),T/F),(pred2,(tup of var),T/F)})
    # Converting the Frozen set to List --> Have done that in substitution
    copyof_S1 = (copy.deepcopy(sent1))
    copyof_S2 = (copy.deepcopy(sent2))


    for pred1 in copyof_S1:
        for pred2 in copyof_S2:

            # print(pred2,"<--2 1-->",pred1)

            string_of_pred1 = pred1[0]
            string_of_pred2 = pred2[0]

            listof_Pred1var = list(pred1[1])
            listof_Pred2var = list(pred2[1])

            if(is_Opp(string_of_pred1,string_of_pred2)):

                tuple_of_unification = unification(listof_Pred1var,listof_Pred2var)
                # first one will be whether unification is possible or not and the second one will be the dictionary of substitutions
                unif_Possible = tuple_of_unification[0]
                substitution_dict = tuple_of_unification[1]
                if(unif_Possible):
                    # print("copy",copyof_S1)
                    new_fact = substitution(copyof_S1,copyof_S2,substitution_dict,pred1,pred2)
                    debugger = [("~C",("John","Bob"),True)]
                    debugger2 = [("~D",("John","Bob"),True)]
                    if (new_fact[0]):
                        return (True,{})
                    to_return.add(new_fact[1])

    return (False,to_return)

# the below function will destd the var and ret us a ipvar list
def get_Stdvar(ip_varList,var_hm,subst_List,curr_position):
    c = 0
    for v in ip_varList:
        if(is_variable(v)):
            if v in var_hm:
                ip_varList[c] = var_hm[v]
            else:
                pos = curr_position[0]
                ip_varList[c] = subst_List[pos]
                var_hm[v] = subst_List[pos]
                curr_position[0] += 1
                if curr_position[0] > 25:
                    curr_position[0] = 0
        else:
            ip_varList[c] = v
        c += 1
    return ip_varList

def make_DStandsent(x):
    # x = list(x)
    sentence_Set = set()
    # list of predicates in a sentence that are tuples
    var_hm = dict()
    curr_position = [0, "currpos"]
    subst_List = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t","u", "v", "w", "x", "y", "z"]
    x  = sorted(x, key=lambda temp: (temp[0], temp[2], temp[1]))
    for pred in x:
        temp = list(pred)
        pred_String = temp[0]
        allVar = list(temp[1])
        is_Simp = temp[2]
        new_var = get_Stdvar(allVar,var_hm,subst_List,curr_position)
        # here I will get a new var list
        new_tuple_Var = tuple(new_var)
        new_predicate = (pred_String,new_tuple_Var,is_Simp)
        sentence_Set.add(new_predicate)

    sentence_Set = frozenset(sentence_Set)
    return sentence_Set




def destandardize_Set(input):

    # convert the frozen set in list and then get all the variables of the predicate and then remove all 0 and 1s
    # low I will have a list of tuples that are predicates

    new_tuple = tuple
    input = list(input)
    newKB = set()
    for clauses in input:
        temp = list(clauses)
        new_Sent = make_DStandsent(temp)
        newKB.add(new_Sent)
    return newKB

# ----------------------------------------------------- YAHA SE NEECHE ANSWER ANE SHURU HAI MATLAB UPAR ALAG CODE H NEECHE alag-------#

def make_StdVar(ip_varList,sentence_No,curr_position,var_hm,subst_List):
    c = 0
    for v in ip_varList:
        if (is_variable(v)):
            if v in var_hm:
                ip_varList[c] = var_hm[v]
            else:
                pos = curr_position[0]

                ip_varList[c] = subst_List[pos]+str(sentence_No)
                var_hm[v] = subst_List[pos]+str(sentence_No)
                curr_position[0] += 1
        else:
            ip_varList[c] = v
        c += 1
    return ip_varList



def again_StdKB(val,sentence_No):

    # list is tuples of predicates in a sentence which are in conjunction
    var_hm = dict()
    curr_position = [0, "currpos"]
    subst_List = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t","u", "v", "w", "x", "y", "z"]
    sentence_Set = set()
    for pred in val:
        temp = list(pred)
        name_Pred = temp[0]
        var_List = list(temp[1])
        is_V = temp[2]

        stdList = make_StdVar(var_List,sentence_No,curr_position,var_hm,subst_List)

        stdList = tuple(stdList)
        pred_S = (name_Pred,stdList,is_V)
        sentence_Set.add(pred_S)

    sentence_Set = frozenset(sentence_Set)
    return sentence_Set


def std_KnowB(KB):
    KB = list(KB)
    # set of frozen sets hai kb and in frozen sets there are tuples
    new_KB = set()
    sentence_No = 0
    for i in KB:
        clause = list(i)
        # making list of the frozen set
        new_Sent = again_StdKB(clause,sentence_No)
        sentence_No += 1
        new_KB.add(new_Sent)
    return new_KB


def Resolution(query,all_Sentences):
    sentences_set = set()
    for i in all_Sentences:
        sentences_set.add(i)
    sentences_set.add(frozenset(query))

    # make a deep copy of your kb and name it as clauses

    clauses = copy.deepcopy(sentences_set)
    # set of frozen sets

    resolvents = set()
    temp_ans = tuple()

    time_of_start = time.process_time()

    set_of_UsedSentences = set()
    while (len(clauses)<10000):
        new_Set = set()
        for sentence1 in clauses:
            for sentence2 in clauses:
                if((time.process_time()-time_of_start)>120):
                    return False
                if (sentence1 != sentence2):
                    tuple_of_2_sentences = (sentence1,sentence2)
                    if(tuple_of_2_sentences not in set_of_UsedSentences):
                        rev_tuples_of2Sentences = (sentence2,sentence1)
                        set_of_UsedSentences.add(tuple_of_2_sentences)
                        set_of_UsedSentences.add(rev_tuples_of2Sentences)

                        temp_ans = Resolve(sentence1,sentence2)

                        if(temp_ans[0]):
                            return True
                        new_Set = new_Set.union(temp_ans[1])

        len_of_in = len(clauses)
        clauses = clauses.union(new_Set)

        destd_KB = destandardize_Set(clauses)

        # print("DESTD DICT")
        # pprint(destd_KB)
        # ---> Implement here

        std_KB = std_KnowB(destd_KB)
        clauses = std_KB

        len_after = len(clauses)

        if(len_after<=len_of_in):
            return False

        print(len(clauses))
    return False

def file_writer(ans_List):
    iceland = ""
    for answers in ans_List:
        iceland += str(answers)
        iceland += "\n"
    with open("output.txt","w") as filo:
        filo.write(iceland)


def start_ALGO():
    ans_List = []

    copy_setKB = copy.deepcopy(set_KB)

    copy_QueryDict = copy.deepcopy(Dict_Quer)

    quer_Val = copy_QueryDict.values()

    all_Sentences = list(copy_setKB)

    for quer in quer_Val:
        temp = set()
        temp.add(quer)
        tempo_ans = Resolution(temp,all_Sentences)
        ans_List.append(tempo_ans)

    for ans in ans_List:
        print(ans,"ANS YE HAI")
    file_writer(ans_List)

start_ALGO()
