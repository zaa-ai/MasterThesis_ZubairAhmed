
*********************************************************************************
** Stand-alone StarRC Reference Methodology 				       **
** Gate Level Flow							       **
** Version: N-2017.12-SP2 (April 23, 2018)                                       **
** Copyright (C) 2010-2018 Synopsys, Inc. All rights reserved.		       **
*********************************************************************************

define(IN,`$1_$2')
define(OUT,`$1.starrc.spef.$2')
***********	SETUP	  ********** 

* Specify block name for parasitic extraction
* BLOCK:  chip_finish_icc
BLOCK:  outputs_icc

* Provide the input Milkyway design database 
MILKYWAY_DATABASE:  ../layout/IN(TOPLEVEL,LIB)

* Specify nxtgrd file which consists of capacitance models
TCAD_GRD_FILE:  TCAD

* Provide the mapping file in which design layers mapped to process layers 
MAPPING_FILE:   MAP

* Reduction setting fro STA Analysis
REDUCTION: NO_EXTRA_LOOPS 

* Use '*' to extract all signal nets in the design. Otherwise, provide the net names to be extracted separated by a space. Wildcards '?' and '!' are accepted for net names
NETS: *

* Use 'RC' to perform resistance and capacitance extraction on the nets
EXTRACTION: RC 

* Provide operating temperature in degree celsius at which extraction is performed
OPERATING_TEMPERATURE: TEMP 


***********     FLOW SELECTION       **********

* Choose maximum of 2 cores for designs less than 100k nets, 4 to 6 cores for designs around 1Million nets and 8 to 16 cores for designs around 10Million nets
NUM_CORES: 

* Provide settings to distribute StarRC job on Gridwire or LSF. Use Command Reference manual for reference
STARRC_DP_STRING: 
* Simultaneous Multicorner Extraction is supported with Distributed Processing and Rapid3D extractions
* Temperature sensitivity extraction is now integrated into SMC
* Define all corners at the project level in the following syntax in corners.smc file:
*   CORNER_NAME: CWorst_TWC
*   TCAD_GRD_FILE: CWorst.nxtgrd
*   OPERATING_TEMPERATURE: TWC
*   CORNER_NAME: CTypical_TTP
*   TCAD_GRD_FILE: CTypical.nxtgrd
*   OPERATING_TEMPERATURE: TTP
*   CORNER_NAME: CBest_TBC
*   TCAD_GRD_FILE: CBest.nxtgrd
*   OPERATING_TEMPERATURE: TBC
* Provide the defined corners.smc file
*CORNERS_FILE: corners.smc
* List all corners to be extracted separated by a space
*SELECTED_CORNERS: CWorst_TWC CTypical_TTP CBest_TBC
* Enable the SMC feature
SIMULTANEOUS_MULTI_CORNER: NO


***********     SKIPPING ALL CELLS **********

SKIP_CELLS: * 


* Metal fill database type will be aligned to skip cells additional layout file type if skip cell addtional layout contents is selected

***********     FILL HANDLING      **********

MILKYWAY_ADDITIONAL_VIEWS: FILL

* Provide the setting how the metal fill needs to be treated, FLOATING or GROUNDED
METAL_FILL_POLYGON_HANDLING:  AUTOMATIC


***********     PARASITIC OUTPUT       **********

COUPLE_TO_GROUND: NO 

COUPLING_ABS_THRESHOLD: 3E-16
COUPLING_REL_THRESHOLD: 0.10
NETLIST_COMPRESS_COMMAND: gzip
NETLIST_FORMAT: SPEF 

* Provide the name of a file to which output parasitic netlist is written
NETLIST_FILE: ./results/OUT(TOPLEVEL,CORNER).gz 


* Provide the name of a summary file to which runtime and memory usage is written
SUMMARY_FILE: ./logs/OUT(TOPLEVEL,CORNER).sum 

* Provide the working directory name to which StarRC internal information is written in binary
STAR_DIRECTORY: starrc_wrk


