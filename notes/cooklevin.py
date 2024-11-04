from tock import *
import itertools
import formulas

def make_tableau(path, t):
    """Construct the tableau of size (t+1) x (t+4) for the given path."""
    if len(path) > t+1:
        raise ValueError("path is longer than the allotted time")
    table = []

    # Create one row for each configuration in the path.
    for (state, tape) in path:
        [state] = state.values
        head = tape.position
        tape = list(tape.values)
        table.append(['#'] + tape[:head] + [state] + tape[head:] + [syntax.BLANK] * (t+1-len(tape)) + ['#'])
        
    # Fill the rest of the tableau with copies of the last row.
    while len(table) < t+1:
        table.append(table[-1])
    return Table(table, num_header_cols=0, num_header_rows=0)

def transitions(m):
    """Convert from Tock's internal format to tuples (q, a, r, b, d), where
    - q is the current state
    - a is the symbol read
    - r is the new state
    - b is the symbol written
    - d (-1 or 1) is the direction moved
    """
    tuples = []
    for t in m.get_transitions():
        (q,), (a,) = t.lhs
        (r,), bstore = t.rhs
        tuples.append((q, a, r, bstore[0], bstore.position))
    return tuples

def tape_alphabet(m):
    """Return the tape alphabet (Gamma) of m."""
    gamma = {syntax.BLANK}
    for _, a, _, b, _ in transitions(m):
        gamma.add(a)
        gamma.add(b)
    return gamma

def make_formula(m, w, t):
    """Convert the run of NTM m on input w to a Boolean formula 
    that is satisfiable iff m accepts w in at most t steps."""
    q0 = m.get_start_state()
    [qf] = m.get_accept_states()
    
    n = len(w)

    # The cell alphabet
    gamma = tape_alphabet(m)
    C = gamma | m.states | {"#"}

    # The tableau has t+1 rows and t+4 columns.
    # Create a variable for each cell and each symbol that can fill the cell.
    x = {}
    for i in range(t+1):
        for j in range(t+4):
            for s in C:
                x[i,j,s] = formulas.var(f"x[{i},{j},{s}]")

    phi_cell = True

    # For each cell,
    for i in range(t+1):
        for j in range(t+4):
            
            # the cell must have a value
            at_least_one = False
            for s in C:
                at_least_one |= x[i,j,s]

            # and the cell must have at most one value
            at_most_one = True
            for s1 in C:
                for s2 in C:
                    if s1 != s2:
                        at_most_one &= ~x[i,j,s1] | ~x[i,j,s2]

            phi_cell &= at_least_one & at_most_one

    # The first row should be the initial configuration
    phi_start = True
    phi_start &= x[0,0,"#"]              # endmarker
    phi_start &= x[0,1,q0]               # head
    for j in range(n):
        phi_start &= x[0,j+2,w[j]]       # input symbols
    for j in range(n+2, t+3):
        phi_start &= x[0,j,syntax.BLANK] # blank symbols
    phi_start &= x[0,t+3,"#"]            # endmarker

    # Each row should be a legal successor configuration of the row above it
    phi_move = True

    # For each 2x3 window,
    for i in range(t):
        for j in range(t+1):

            phi_legal = False

            # The part of the tape not being changed by the head
            for u1 in gamma | {"#", qf}:
                for u2 in gamma | {qf}:
                    for u3 in gamma | {"#", qf}:
                        phi_legal |= (x[i,j,  u1] & x[i,j+1,  u2] & x[i,j+2,  u3] &
                                      x[i+1,j,u1] & x[i+1,j+1,u2] & x[i+1,j+2,u3])

            for q, b, r, c, d in transitions(m):
                if d == -1: # move left: uaqbv becomes uracv
                    for u1 in gamma | {"#"}:
                        for u2 in gamma:
                            for a in gamma:
                                phi_legal |= (x[i,  j,u1] & x[i,  j+1,u2] & x[i,  j+2,a] &
                                              x[i+1,j,u1] & x[i+1,j+1,u2] & x[i+1,j+2,r])

                    for u2 in gamma | {"#"}:
                        for a in gamma:
                            phi_legal |= (x[i,  j,u2] & x[i,  j+1,a] & x[i,  j+2,q] &
                                          x[i+1,j,u2] & x[i+1,j+1,r] & x[i+1,j+2,a])

                    for a in gamma:
                        phi_legal |= (x[i,  j,a] & x[i,  j+1,q] & x[i,  j+2,b] &
                                      x[i+1,j,r] & x[i+1,j+1,a] & x[i+1,j+2,c])
                        
                    # special case: if head is at left end, it does not move (qbv becomes rcv)
                    phi_legal |= (x[i,  j,"#"] & x[i,  j+1,q] & x[i,  j+2,b] &
                                  x[i+1,j,"#"] & x[i+1,j+1,r] & x[i+1,j+2,c])

                    for a in gamma:
                        for v1 in gamma | {"#"}:
                            phi_legal |= (x[i,  j,q] & x[i,  j+1,b] & x[i,  j+2,v1] &
                                          x[i+1,j,a] & x[i+1,j+1,c] & x[i+1,j+2,v1])

                            # special case again
                            phi_legal |= (x[i,  j,q] & x[i,  j+1,b] & x[i,  j+2,v1] &
                                          x[i+1,j,r] & x[i+1,j+1,c] & x[i+1,j+2,v1])

                    for a in gamma:
                        for v1 in gamma:
                            for v2 in gamma | {"#"}:
                                phi_legal |= (x[i,  j,b] & x[i,  j+1,v1] & x[i,  j+2,v2] &
                                              x[i+1,j,c] & x[i+1,j+1,v1] & x[i+1,j+2,v2])

                elif d == +1: # move right: uaqbv becomes uacrv
                    for a in gamma:
                        for u in gamma | {"#"}:
                            phi_legal |= (x[i,  j,u] & x[i,  j+1,a] & x[i,  j+2,q] &
                                          x[i+1,j,u] & x[i+1,j+1,a] & x[i+1,j+2,c])

                    for a in gamma | {"#"}:
                        phi_legal |= (x[i,  j,a] & x[i,  j+1,q] & x[i,  j+2,b] &
                                      x[i+1,j,a] & x[i+1,j+1,c] & x[i+1,j+2,r])

                    for v1 in gamma:
                        phi_legal |= (x[i,  j,q] & x[i,  j+1,b] & x[i,  j+2,v1] &
                                      x[i+1,j,c] & x[i+1,j+1,r] & x[i+1,j+2,v1])

                    for v1 in gamma:
                        for v2 in gamma | {"#"}:
                            phi_legal |= (x[i,  j,b] & x[i,  j+1,v1] & x[i,  j+2,v2] &
                                          x[i+1,j,r] & x[i+1,j+1,v1] & x[i+1,j+2,v2])

                else:
                    raise ValueError("invalid direction")
            
            phi_move &= phi_legal

    # The last configuration should be accepting
    phi_accept = False
    for j in range(1, t+2):
        phi_accept |= x[t,j,qf]

    return phi_cell & phi_start & phi_move & phi_accept

if __name__ == "__main__":
    m = read_csv("ntm-primes.csv")
    w = ["1"]*4
    t = 20
    tableau = make_tableau(run(m, w).shortest_path(), t)
    phi = make_formula(m, w, t)

    asst = {x: False for x in phi.vars()}
    for (i, row) in enumerate(tableau.rows):
        for (j, cell) in enumerate(row):
            asst[f'x[{i},{j},{cell}]'] = True
    print(phi.evaluate(asst))

    import random
    for trial in range(10):
        asst = {x: random.choice([False, True]) for x in phi.vars()}
        for (i, row) in enumerate(tableau.rows):
            for (j, cell) in enumerate(row):
                asst[f'x[{i},{j},{cell}]'] = True
        print(phi.evaluate(asst))
