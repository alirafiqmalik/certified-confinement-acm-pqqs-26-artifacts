OPENQASM 3.0;
include "stdgates.inc";
qubit[12] q;
// Tenant circuit confined to the allowed slot A = {0..5}; all cz are ring edges.
x q[0];
sx q[1];
cz q[0], q[1];
cz q[1], q[2];
rz(0.5) q[3];
cz q[3], q[4];
cz q[4], q[5];
