/**
 * Propositional Tableaux
*/

#include<list>
#include<cassert>
#include<stdexcept>

enum PFType {ATOM, AND, OR, NOT, IF, IFF} ;

// Propositional Formula
struct PF{
    PFType tag;
    char atom; //Could do a union here 
    struct PF* arg1, *arg2;
};

//Constructors

PF* newPF(PFType tag, char c, PF* p1, PF* p2){
    return new PF{tag, c, p1, p2};
};

PF* Atom(char c){
    return newPF(ATOM, c, nullptr, nullptr);
};

PF* Not(PF* p){
    return newPF(NOT, '\0', p, nullptr);
};

PF* And(PF* p1, PF* p2){
    return newPF(AND, '\0', p1, p2);
};

PF* Or(PF* p1, PF* p2){
    return newPF(OR, '\0', p1, p2);
};

PF* If(PF* p1, PF* p2){
    return newPF(IF, '\0', p1, p2);
};

PF* Iff(PF* p1, PF* p2){
    return newPF(IFF, '\0', p1, p2);
};

// p1 and p2 are equal if they have the same tag, atom and arguments
bool operator==(PF p1, PF p2){
    return p1.tag == p2.tag && 
           p1.atom == p2.atom &&
           *p1.arg1 == *p2.arg1 &&
           *p1.arg2 == *p2.arg2;
}

// p1 contradicts p2 if p1 is the negation of p2 or vice versa
bool contradictory(PF* p1, PF* p2){
    return (p2->tag == NOT && *p1 == *p2->arg1) ||
           (p1->tag == NOT && *p2 == *p1->arg1);
}

// Returns iff the branch contains a contradiction (if the branch is trivially inconsistent)
//O(n^2)
bool branchContradictory(std::list<PF*> branch){
    for(auto p1 : branch){
        for(auto p2 : branch){
            if(p1 != p2 && contradictory(p1, p2)){
                return true;
            }
        }
    }
    return false;
}

bool tableauxAux(std::list<PF*> branch, std::list<PF*> others = {}){
    branch.insert(branch.end(), others.begin(), others.end());
    //Base case
    if(branch.empty()){
        return false;
    }
    //Recursive case
    PF* p = branch.front();
    branch.pop_front();
    switch (p->tag){
        case ATOM:
            return branchContradictory(branch) || tableauxAux(branch);
        case AND:
            return tableauxAux(branch, {p->arg1, p->arg2});
        case OR:
            return tableauxAux(branch, {p->arg1}) && tableauxAux(branch, {p->arg2});
        case IF:
            return tableauxAux(branch, {Not(p->arg1)}) && tableauxAux(branch, {p->arg2});
        case IFF:
            return tableauxAux(branch, {If(p->arg1, p->arg2), If(p->arg2, p->arg1)});
        case NOT:{
            PF* p1 = p->arg1;
            switch (p->arg1->tag)
            {
                case ATOM:
                    return branchContradictory(branch) || tableauxAux(branch);
                case NOT:
                    return tableauxAux(branch, {p1->arg1});
                case AND:
                    return tableauxAux(branch, {Not(p1->arg1)}) && tableauxAux(branch, {Not(p1->arg2)});
                case OR:
                    return tableauxAux(branch, {Not(p1->arg1), Not(p1->arg2)});
                case IF:
                    return tableauxAux(branch, {p1->arg1, Not(p1->arg2)});
                case IFF:
                    return tableauxAux(branch, {Not(If(p1->arg1, p1->arg2)), Not(If(p1->arg2, p1->arg1))});
                default:
                    throw std::runtime_error("Bad formula");
            }
        }
        default:
            throw std::runtime_error("Bad formula");
    }
}

bool tableaux(PF* p){
    return tableauxAux({Not(p)});
}

int main(){
    //Testing tableaux for basic tautologies and contradictions:
    //Tautologies
    assert(tableaux(If(Atom('p'), Atom('p'))));
    assert(tableaux(Iff(Atom('p'), Atom('p'))));
    assert(tableaux(If(Atom('p'), If(Atom('q'), Atom('p')))));
    
    //Contradictions
    assert(!tableaux(And(Atom('p'), Not(Atom('p')))));
    assert(!tableaux(If(Atom('p'), Not(Atom('p')))));
    assert(!tableaux(Iff(Atom('p'), Not(Atom('p')))));
    assert(!tableaux(If(Atom('p'), If(Atom('q'), Not(Atom('p'))))));
}