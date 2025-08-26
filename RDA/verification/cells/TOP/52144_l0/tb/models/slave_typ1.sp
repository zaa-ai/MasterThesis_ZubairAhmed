*Custom Compiler Version P-2019.06-SP1-5
*Thu Jan 19 16:54:24 2023


********************************************************************************
* Library          : L0
* Cell             : slave_typ1
* View             : schematic
* View Search List : hspice hspiceD cmos.sch cmos_sch schematic veriloga
* View Stop List   : hspice hspiceD veriloga
********************************************************************************
.subckt slave_typ1 en_us gnd_1 vs
rpin2 vsup vsup_i r=0.2
rpin1 vdrv vdrv_i r=0.2
rdrv vs vdrv r=15
rsup vs vsup r=82
cdrv vdrv gnd_1 c=100u
csup vsup gnd_1 c=1u
c2 vs gnd_1 c=2.2n
e18 vs_ok gnd_1 vcvs vsup_i vth 10000 max=5 min=0 abs=0
g10 vsup_i gnd_1 vccs vs_ok gnd_1 3m max=20m min=0 abs=0
g14 vdrv_i gnd_1 vccs en_us gnd_1 0.1 abs=0
v17 vth gnd_1 dc=0 pwl ( 0 0.0 1u 5 )
.ends slave_typ1


