
**------------------------------------------------
** Power Supply
**------------------------------------------------

rvsup vsup_p gnd 1k

**------------------------------------------------
** Switch Transistor
**------------------------------------------------

xghsout0 hsin0_p gate0 hsout0_p gnd nld36_g5b_mac l=0.4u w=0.01 ad=16.0299n as=3.2n pd=0.012585 ps=0.020064 nf=100 dti=0 multi=3
xghsout1 hsin1_p gate1 hsout1_p gnd nld36_g5b_mac l=0.4u w=0.01 ad=16.0299n as=3.2n pd=0.012585 ps=0.020064 nf=100 dti=0 multi=3
  *ghsout0 hsin0_p hsout0_p vcr pwl(1) vcp0 hsout0_p 0.5,1e9 1,1k 1.5,1 4.5,'2/3'
  *ghsout1 hsin1_p hsout1_p vcr pwl(1) vcp1 hsout1_p 0.5,1e9 1,1k 1.5,1 4.5,'2/3'

**------------------------------------------------
** Gate-Source Protection
**------------------------------------------------

xghsout0_prot_pos vcp0 hsout0_p hsout0_p gnd nld36_g5b_mac l=0.4u w=100u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1
xghsout1_prot_pos vcp1 hsout1_p hsout1_p gnd nld36_g5b_mac l=0.4u w=100u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1

*----------

xghsout0_prot_neg vcp0_i vcp0 vcp0 gnd nld36_g5b_mac l=0.4u w=100u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1
xghsout1_prot_neg vcp1_i vcp1 vcp1 gnd nld36_g5b_mac l=0.4u w=100u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1

**------------------------------------------------
** Passive Off-Switching
**------------------------------------------------

*rghsout0_pull vcp0 hsout0_p 1000k
*rghsout1_pull vcp1 hsout1_p 1000k

**------------------------------------------------
** Charge Pump Mean Model
**------------------------------------------------

*evcp0 vcp0_i hsout0_p hsin0_en gnd 1
*  rvvcp0 vcp0_i vcp0     100k
*  cvvcp0 vcp0   hsout0_p 100f

*evcp1 vcp1_i hsout1_p hsin1_en gnd 1
*  rvvcp1 vcp1_i vcp1     100k
*  cvvcp1 vcp1   hsout1_p 100f

**------------------------------------------------
** Charge Pump
**------------------------------------------------

.param fp=100k
.param cp=10p

*----------

vclk clk gnd pwl 0,0 1n,5 '0.5/fp',5 '0.5/fp+1n',0 '1/fp',0 r

*----------
  
rclk0 clk  clk0 10k
cclk0 clk0 gnd  10f
gclk0_en clk0 gnd vcr pwl(1) hsin0_en gnd 2.4,1 2.6,1e9
  
rclk1 clk  clk1 10k
cclk1 clk1 gnd  10f
gclk1_en clk1 gnd vcr pwl(1) hsin1_en gnd 2.4,1 2.6,1e9

*----------

xcp0_i hsout0_p cpi0     diode_ideal vf=0.1 r=10k
xcp0_o cpi0     vcp0     diode_ideal vf=0.1 r=10k
ccp0   clk0     cpi0     'cp'

xcp1_i hsout1_p cpi1     diode_ideal vf=0.1 r=10k
xcp1_o cpi1     vcp1     diode_ideal vf=0.1 r=10k
ccp1   clk1     cpi1     'cp'

*----------

rgate0 vcp0 gate0 100k
rgate1 vcp1 gate1 100k

**------------------------------------------------
** Gate Discharge
**------------------------------------------------

vdisch0 disch0_5v gnd pwl 0,0 1u,5
gdisch0 vcp0 gnd  disch0_5v hsin0_en '10u/5'

vdisch1 disch1_5v gnd pwl 0,0 1u,5
gdisch1 vcp1 gnd  disch1_5v hsin1_en '10u/5'

**------------------------------------------------
** Current Limitation
**------------------------------------------------

xghsout0_mirr hsin0_mirr vcp0 hsout0_p gnd nld36_g5b_mac l=0.4u w=25u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1

xilim0     hsin0_mirr  hsin0_ilim hsin0_p i_pmirror m=1
rilim0     hsin0_ilim  gnd 3k
rilim0_flt hsin0_ilim  hsin0_ilim2 500k
cilim0_flt hsin0_ilim2 gnd 10p
gilim0     gate0       gnd hsin0_ilim2 gnd '1u/1.0'

xilim0_lim_pos hsin0_ilim2 gnd         diode_ideal vf=5.5 r=10k
xilim0_lim_neg gnd         hsin0_ilim2 diode_ideal vf=0.7 r=10k

xghsout1_mirr hsin1_mirr vcp1 hsout1_p gnd nld36_g5b_mac l=0.4u w=25u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1

xilim1     hsin1_mirr  hsin1_ilim hsin1_p i_pmirror m=1
rilim1     hsin1_ilim  gnd 3k
rilim1_flt hsin1_ilim  hsin1_ilim2 500k
cilim1_flt hsin1_ilim2 gnd 10p
gilim1     gate1       gnd hsin1_ilim2 gnd '1u/1.0'

xilim1_lim_pos hsin1_ilim2 gnd         diode_ideal vf=5.5 r=10k
xilim1_lim_neg gnd         hsin1_ilim2 diode_ideal vf=0.7 r=10k

**------------------------------------------------
** Current Measurement
**------------------------------------------------

xghsout0_meas hsin0_p gate0 hsout0_meas gnd nld36_g5b_mac l=0.4u w=25u ad=0.400368n as=3.2p pd=0.00015704 ps=21.28u nf=2 dti=0 multi=1

gmeas0_ota hsout0_meas hsout0_vmeas hsout0_p hsout0_meas '-100u/1m' min=-1m max=1m
rmeas0 hsout0_vmeas gnd 3k
cmeas0 hsout0_vmeas gnd 10p

eadc hsout0_adc gnd hsout0_vmeas gnd '4096/5' min=0 max=4095

**------------------------------------------------
**------------------------------------------------
