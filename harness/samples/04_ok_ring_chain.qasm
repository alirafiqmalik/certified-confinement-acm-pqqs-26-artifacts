OPENQASM 3.0;
include "stdgates.inc";
qubit[12] q;
// A longer nearest-neighbour chain entirely inside the tenant slot {0..5}. → ACCEPT.
sx q[0];
cz q[0], q[1];
cz q[1], q[2];
cz q[2], q[3];
cz q[3], q[4];
cz q[4], q[5];
rz(1.5707963267948966) q[2];
id q[5];
