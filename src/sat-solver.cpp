// SAT Solver
// 105061171 Kuan-Hung Chen
// Implementation of a simple SAT Solver.

#include <iostream>
#include <sstream>
#include <vector>
#include <set>
#include <unordered_set>

using namespace std;

int numClauses = -1;
int numVariables = -1;
vector<set<int> > clauses;
vector<int> assignments;
vector<vector<set<int>*> > watched_lits;
vector<int> pures;

int parseInt(string&);
void parseInfo(int&, int&);
void parseClausesMain(vector<set<int> >&, int&);
void parseClauses(vector<set<int> >&);

void printInformation(int, int, vector<set<int> >&);
void printWatchedInt();

bool unitPropagation(vector<set<int> >&, vector<int>&);
void pureLiteralElimination(vector<set<int> >&, vector<int>&);
bool solve(vector<set<int> >&, vector<int>, vector<int>&, bool);
int chooseNext(vector<int>&, int);
bool AllSatisfied(vector<int>&);
void initWatchedLits(vector<set<int> >&, vector<int>&);
int updateWatchedLits(vector<int>&, set<int>&);

void printWatchedInt() {
    /*********************************************************
     * 
     * A debugging function to see the watching literals of each clause.
     * 
     ********************************************************/
    for (int i = 1; i <= numVariables; ++i) {
        cout << "Watching " << i << ": ";
        for (auto& cls: watched_lits[i]) {
            cout << cls << ", ";
        }
        cout << endl;
    }
}

int updateWatchedLits(vector<int>& assgms, set<int>& cls) {
    /******************************************************************************
     * 
     * Call this function right after assigning value for cls's watching lit.
     * Note: MAKE SURE WATCHED LITS IS TWO (OTHERWISE CANNOT BACKTRACK)!!!
     * 
     * a. There exists an un-assigned and un-watched literal:
     *      update to watch it, return 1 (remove from current watched lits)
     * 
     * b. There is only an un-assigned but watched literal:
     *      no need to update, return 2 (trigger unit propagation)
     * 
     * c. There exists a SAT literal:
     *      no need to update, return 3 (do nothing, this clause is done)
     * 
     * d. There is no un-assigned literal, and no literals is satisfied:
     *      current assignment leads to conflict, return -1 (false assignment)
     * 
     ******************************************************************************/

    bool watched = false;
    bool unassigned = false;
    for (auto& v: cls) {
        if ((assgms[(v > 0) ? v : -v] * v) > 0) {
            // case c.
            return 3;
        } else if (assgms[(v > 0) ? v : -v] == 0) {
            // exists an un-assigned literal
            watched = false;
            unassigned = true;
            for (auto& xcls: watched_lits[(v > 0) ? v : -v]) {
                if (xcls == &cls) {
                    // it's watched
                    watched = true;
                    break;
                }
            }
            if (!watched) {
                // not watched, case a.
                watched_lits[(v > 0) ? v : -v].push_back(&cls);
                return 1;
            }
        }
    }
    if (unassigned) {
        // the unassigned literal is watched, case b.
        return 2;
    } else {
        // no unassigned literals, and all assigned literals are not SAT, case d.
        return -1;
    }
}

void initWatchedLits(vector<set<int> >& clss, vector<int>& assgms) {
    /************************************************************
     * Initialize two watching literals for each clause.
     ***********************************************************/
    int cnt;
    for (auto& cls: clss) {
        cnt = 0;
        for (auto& v: cls) {
            if (assgms[(v > 0) ? v : -v] * v != -1) { // unassigned, set as watched lit
                watched_lits[(v > 0) ? v : -v].push_back(&cls);
                ++cnt;
                if (cnt == 2) break; // already choose two, go to next clause
            }
        }
    }
}

void printInformation(int numC, int numV, vector<set<int> >& clss) {
    /************************************************************
     * A debugging function to check clauses are correctly parsed.
     ***********************************************************/

    cout << "Number of clauses: " << numC << endl;
    cout << "Number of variables: " << numV << endl;
    for (int i = 0; i < clss.size(); ++i) {
        cout << "(" << i + 1 << ") ";
        for (set<int>::iterator itr = clss[i].begin(); itr != clss[i].end(); ++itr) {
            cout << *itr << " ";
        }
        cout << "(" << &clss[i] << ")" << endl;
    }
}

bool AllSatisfied(vector<int>& assgms) {
    /************************************************************
     * When all variables are assigned, return true; otherwise return false.
     ***********************************************************/

    for (int i = 1; i < assgms.size(); ++i) {
        if (assgms[i] == 0) return false;
    }
    return true;
}

bool solve(vector<set<int> >& clss, vector<int> assgms, vector<int>& targets) {
    /************************************************************
     * 
     * This function is the main function of solving the CNF.
     * Each time we assign value for the target variables, check the watched lits and update them if needed.
     * Once we have unit clause, we do unit propagation; if we have conflict, go back to previous level
     * 
     * TODO: Add Conflict Driven Clause Learning (CDCL)
     * 
     * @param: clss: vector of clauses
     * @param: assgms: assignments for this level (PASS BY VALUE)
     * @param: targets: new assignment for this level
     *  
     ***********************************************************/
    
    for (auto& target : targets) {
        if (((target > 0) ? target : -target) > numVariables) return false;
        assgms[(target > 0) ? target : -target] = ((target > 0) ? 1 : -1);
    }
    set<int> units;
    for (auto& target : targets) {
        for (vector<set<int>*>::iterator it = watched_lits[(target > 0) ? target : -target].begin(); it != watched_lits[(target > 0) ? target : -target].end(); ++it) {
            if ((**it).find(-target) != (**it).end()) {
                // need to update
                switch (updateWatchedLits(assgms, **it))
                {
                    case 1: // watch to new literals, remove from current watched lits
                        watched_lits[(target > 0) ? target : -target].erase(it);
                        --it;
                        break;
                    case 2: // only an un-assigned lit, but it's watched -> unit propagation
                        for (auto& v: **it) {
                            if (assgms[(v > 0) ? v : -v] == 0) {
                                if (units.find(-v) != units.end()) {
                                    // conflict                        
                                    return false;
                                } else {
                                    units.insert(v);
                                    break;
                                }
                            }
                        }
                        break;
                    case 3: // exists a SAT literal, do nothing
                        break;
                    case -1: // no un-assigned lits, and all lits are not SAT -> conflicts
                        return false;
                    default:
                        break;
                }
            }
        }
    }
    
    if (AllSatisfied(assgms))  {
        return true;
    }
    if (units.size() != 0) {
        vector<int> us(units.begin(), units.end());
        return solve(clss, assgms, us);
    }
    // try next variable
    vector<int> next1, next2;
    next1.push_back(chooseNext(assgms, 0));
    next2.push_back(-chooseNext(assgms, 0));
    return solve(clss, assgms, next1) || solve(clss, assgms, next2);
}

bool unitPropagation(vector<set<int> >& clss, vector<int>& assgms) {
    /************************************************************
     * 
     * This is only for removing unit clauses before solving.
     * If there is a unit clause, assign value for the literal; if there is conflict, return true and this CNT is UNSAT.
     * 
     ************************************************************/

    bool keep = true;
    while (keep) {
        keep = false;
        for (auto& cls: clss) {
            if (cls.size() == 1) { // unit clause
                if (assgms[(*cls.begin() > 0) ? *cls.begin() : -*cls.begin()] * *cls.begin() < 0) {
                    return true; // conflict unit clauses exist, this CNF is UNSAT
                } else { // assign it truth value directly
                    assgms[(*cls.begin() > 0) ? *cls.begin() : -*cls.begin()] = (*cls.begin() > 0) ? 1 : -1;
                }
            }
        }
    }
    return false;
}

void pureLiteralElimination(vector<set<int> >& clss, vector<int>& assgms) {
    /************************************************************
     * 
     * This function is only called before solving.
     * If there is a variable that only in positive or in negative, then just assign a value to make it true.
     * 
     ************************************************************/

    for (int i = 1; i <= numVariables; ++i) {
        if (pures[i] == 1) {
            assgms[i] = 1;
        } else if (pures[i] == -1) {
            assgms[i] = -1;
        }
    }
}

int chooseNext(vector<int>& assgms, int cur) {
    ++cur;
    while (assgms[cur] != 0) {
        ++cur;
        if (cur > numVariables) cur -= numVariables;
    }
    return cur;
}

void parseInfo(int& numC, int& numV) {
    string line;
    string word;
    for (; getline(cin, line); ) {
        istringstream iss(line);
        iss >> word;
        if (word != "p") continue;        
        while (iss >> word) {
            if (word == "cnf") continue;
            if (numV == -1) {
                numV = parseInt(word);
            } else {
                numC = parseInt(word);
                break;
            }
        }
        break;
    }
}

void parseClausesMain(vector<set<int> >& clss, int& range) {
    for (int i = 0; i < range; ++i) {
        parseClauses(clss);
    }
}

void parseClauses(vector<set<int> >& clss) {
    string line;
    int num = 0;
    string word;
    set<int> newClause;
    for (; getline(cin, line); ) {
        istringstream iss(line);
        while (iss >> word) {
            num = parseInt(word);
            if (num != 0) {
                if (num > 0) {
                    if (pures[num] == 0) pures[num] = 1;
                    else if (pures[num] == -1) pures[num] = 2;
                } else if (num < 0) {
                    if (pures[-num] == 0) pures[-num] = -1;
                    else if (pures[-num] == 1) pures[-num] = 2;
                }
                newClause.insert(num);
            } else {
                clss.push_back(newClause);
                return;
            }
        }
    }
}

int parseInt(string& w) {
    int res = 0, idx = 0;
    bool neg = false;
    if (w[0] == '-') {
        neg = true;
        ++idx;
    }
    while (idx < w.length()) {
        res = res * 10 + (w[idx] - '0');
        ++idx;
    }
    return neg ? -res : res;
}

int main() {
    parseInfo(numClauses, numVariables);
    pures = vector<int> (numVariables + 1, 0);
    parseClausesMain(clauses, numClauses);
    // printInformation(numClauses, numVariables, clauses);

    assignments = vector<int> (numVariables + 1, 0); // 1: true, -1: false, 0: not decide
    watched_lits = vector<vector<set<int>*> > (numVariables + 1);
    
    bool unsatBeforeSolving = (unitPropagation(clauses, assignments));
    if (unsatBeforeSolving) { // unit clauses have conflict
        cout << "unsat" << endl;
    } else {
        pureLiteralElimination(clauses, assignments);
        pures.clear();
        initWatchedLits(clauses, assignments);
        vector<int> next1, next2;
        next1.push_back(chooseNext(assignments, 0));
        next2.push_back(-chooseNext(assignments, 0));
        bool ans = solve(clauses, assignments, next1) || solve(clauses, assignments, next2);
        if (ans) {
            cout << "sat" << endl;
        }
        else cout << "unsat" << endl;
    }
    
    return 0;
}