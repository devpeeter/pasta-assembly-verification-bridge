adds x0, x0, x4
adcs x1, x1, x5
adcs x2, x2, x6
adc x3, x3, x7
subs x11, x0, x8
sbcs x12, x1, x9
sbcs x13, x2, xzr
sbcs x14, x3, x10
csel x0, x11, x0, cs
csel x1, x12, x1, cs
csel x2, x13, x2, cs
csel x3, x14, x3, cs