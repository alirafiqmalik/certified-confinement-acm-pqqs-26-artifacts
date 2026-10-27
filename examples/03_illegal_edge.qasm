OPENQASM 3.0;
include "stdgates.inc";
qubit[12] q;
// cz q[0],q[6] is NOT a ring edge (0 and 6 are not adjacent) → hardware-illegal.
// It also touches forbidden qubit 6. Rejected on legality (and confinement). → REJECT.
x q[0];
cz q[0], q[6];
