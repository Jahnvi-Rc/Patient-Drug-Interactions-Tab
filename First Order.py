
FAIL = "Fail"
TRUE = "True"
visited_KB = {}



def read_kb(file_ip):
    
    kb = {}
    kb_limit = int(file_ip.readline())
    for i in range(kb_limit):                                                                                                                                       
        kb_clause = file_ip.readline().strip()
        kb_clause = kb_clause.replace(" ", "")
        if ">" in kb_clause:
            kb_clause.split(">")
            split_id = kb_clause.find(">")
            clause_RHS = kb_clause[split_id+1:len(kb_clause)]
            clause_LHS = kb_clause[0:split_id-1]
            
            std_list1 = []
            args1 = coumpund_arguments(clause_RHS).split(",")
            for arg in args1:
                if arg.islower() and len(arg) == 1 and not "," in arg and arg.isalpha() and not "(" in arg:
                    std_list1.append(arg + str(i))
                else:
                    std_list1.append(arg)
            cl_end1 = clause_RHS.find("(")
            new_std_list1 = ",".join(std_list1)
            clause_RHS = clause_RHS[0:cl_end1] + "("+new_std_list1+")"
            compund_key = clause_RHS 
            
            
            RHS_inLHS_split = []
            for clause in clause_LHS.split("&"):
                std_list = []
                args = coumpund_arguments(clause).split(",")
                for arg in args:
                    if arg.islower() and len(arg) == 1 and not "," in arg and arg.isalpha() and not "(" in arg:
                        std_list.append(arg + str(i))
           
                    else:
                        std_list.append(arg)
                cl_end = clause.find("(")
                new_std_list = ",".join(std_list)
                clause = clause[0:cl_end] + "("+new_std_list+")"
                RHS_inLHS_split.append(clause)
                
            kb_rhs_new = "&".join(RHS_inLHS_split)
           
            kb.setdefault(compund_key, []).append(kb_rhs_new)
        else:
            end_val = kb_clause.find(")")
            simple_key = kb_clause[0:end_val+1]
            RHS_split = TRUE
            kb.setdefault(simple_key, []).append(RHS_split)
    
    return kb

def coumpund_arguments(clause):
    if "(" in clause:
        clause_start = clause.find("(")        
        return clause[clause_start+1:len(clause)-1]  

    
def main():
    file_ip = open("input.txt", "r")
    file_op = open('output.txt', 'w')
    queries = []
    query_limit = int(file_ip.readline())
    for i in range(query_limit):
        queries.append(file_ip.readline().strip())
    kb = read_kb(file_ip)
    for query in queries:
        try:
            result= "FALSE"   
            s = {}
            visited_KB.clear()
            sl = check_algo(kb, query, s)
            for k in sl:
                if FAIL in k:
                    continue
                elif TRUE in k and FAIL not in k:
                    result = "TRUE"
        except:
            result= "FALSE"
        file_op.write(result+"\n")

def check_algo(kb, goal, subst):
    op = goal[0:goal.find("(")]
    flag = 0
    unification_list = []
    fact_check = True
    for i in coumpund_arguments(goal).split(","):
        if i.islower() and not "," in i and not "(" in i:
            fact_check = False
    if goal in visited_KB:
        subst[FAIL] = FAIL
        unification_list.append(subst)
        return unification_list
    if fact_check:
        visited_KB[goal] = TRUE
    if goal in kb and TRUE in kb[goal]:
        subst[TRUE] = TRUE
        visited_KB.pop(goal, None)
        unification_list.append(subst)
        return unification_list
    rules = {k: v for k, v in kb.items() if op == k[0:k.find("(")]}
    for rhs, lhs in rules.items():
        flag = 1
        for l in lhs:
            temp_subs = {}
            if l != TRUE:
                unification_algorithm(rhs, goal, temp_subs)
                algo_and(kb, l, temp_subs)
            else:
                unification_algorithm(rhs, goal, temp_subs)
                algo_and(kb, goal, temp_subs)
            if FAIL not in temp_subs and TRUE in temp_subs:
                visited_KB.pop(goal, None)
                temp_subs.update(subst)
                unification_list.append(temp_subs)
    if flag == 0 or not unification_list:
        subst[FAIL] = FAIL
        unification_list.append(subst)
    return unification_list

def algo_and(kb, goals, temp_list):
    if temp_list and FAIL in temp_list:
        return temp_list
    elif len(goals) == 0:
        return temp_list
    else:
        gl = goals.split("&")
        first = gl[0]
        gl.remove(first)
        rest = "&".join(gl)
        first = substitute(first, temp_list)
        res_l = check_algo(kb, first, temp_list)
        f = 1
        for s in res_l:
            if rest and FAIL not in s:
                algo_and(kb, rest, s)
            if FAIL not in s and TRUE in s:
                temp_list.update(s)
                f = 0
        if f == 1:
            temp_list[FAIL] = FAIL
        return temp_list


def unification_algorithm(x, y, substitution):
    if substitution:
        if FAIL in substitution:
            return substitution
    if x == y:
        return substitution
    if x.islower() and not "," in x and not "(" in x:
        unification_algorithm_var(x, y, substitution)
    elif y.islower() and not "," in y and not "(" in y:
        unification_algorithm_var(y, x, substitution)
    elif "(" in x and "(" in y:
        unification_algorithm(x[0:x.find("(")], y[0:y.find("(")], substitution)
        return unification_algorithm(coumpund_arguments(x), coumpund_arguments(y), substitution)
    elif "," in x and "," in y:
        if "(" in x[0:x.find(",")]:
            x_first = x[0:x.find(")")+1]
            x_rest = x[x.find(")")+2:len(x)]
        else:
            x_first = x[0:x.find(",")]
            x_rest = x[x.find(",")+1:len(x)]
        if "(" in y[0:y.find(",")]:
            y_first = y[0:y.find(")")+1]
            y_rest = y[y.find(")")+2:len(y)]
        else:
            y_first = y[0:y.find(",")]
            y_rest = y[y.find(",")+1:len(y)]
        unification_algorithm(x_first, y_first, substitution)
        return unification_algorithm(x_rest, y_rest, substitution)
    else:
        substitution[FAIL] = FAIL
        return substitution


def unification_algorithm_var(var, x, substitution):
    if var in substitution.keys():
        return unification_algorithm(substitution[var], x, substitution)
    elif check_occurance(var, x, substitution):
        substitution[FAIL] = FAIL
    else:
        if "(" in x:
            str_args = coumpund_arguments(x)
            args = str_args.split(",")
            for arg in args:
                if not arg.islower() and not "," in arg and not "(" in arg:
                    args.remove(arg)
            for i in arg:
                if i in substitution.keys():
                    x = replace_var_with_val(x, i, substitution[i])
        substitution[var] = x


def check_occurance(var, x, s):
    if var == x:
        return True
    elif x.islower() and not "," in x and not "(" in x and x in s:
        return check_occurance(var, s[x], s)
    elif "(" in x:
        return (check_occurance(var, x[0:x.find("(")], s) or
                check_occurance(var, coumpund_arguments(x), s))
    else:
        return False

def substitute(line, slist):
    args = coumpund_arguments(line).split(',')
    for a in args:
        if "(" in a:
            substitute(line, slist)
        elif a.islower() and not "," in a and not "(" in a:
            if a in slist.keys():
                substitution_value = slist[a]
                if substitution_value.islower() and not "," in substitution_value and not "(" in substitution_value and substitution_value in slist:
                    substitution_value = slist[substitution_value]
                for n, i in enumerate(args):
                    if i == a:
                        args[n] = substitution_value
                line = line[0:line.find("(")] + '(' + ','.join(args) + ')'
    return line

def replace_var_with_val(x, var, val):
    if "(" in x:
        u_arg = []
        for arg in coumpund_arguments(x).split(","):
            if arg.islower() and not "," in arg and not "(" in arg and arg == var:
                u_arg.append(val)
            elif "(" in arg:
                u_arg.append(replace_var_with_val(arg, var, val))
            else:
                u_arg.append(arg)
        x = x[0:x.find("(")]+"("+",".join(u_arg)+")"
    return x

def loop_detect(query):
    for item in visited_KB:
        if item == query:
            if visited_KB.count(item) > 2:
                return True
            
if __name__ == "__main__":
	main()