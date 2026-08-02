OPENQASM 3.0;
include "stdgates.inc";
qubit[12] q;
// The money example at QASM level: cz q[5],q[6] is a REAL ring edge (hardware-legal)
// yet qubit 6 is in the forbidden co-tenant region F = {6..11}. Legal but unsafe → REJECT.
x q[0];
cz q[4], q[5];
cz q[5], q[6];
