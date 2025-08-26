`ifndef EDF_EPM_MODEL_PKG_SV
`define EDF_EPM_MODEL_PKG_SV
// @SuppressProblem -type fully_unread_class_field -file current
// @SuppressProblem -type assign_int_to_real -file current

package edf_epm_model_pkg;

	interface class edf_parameter;
		
		pure virtual function string get_name();
		
		pure virtual function real get_min();
		
		pure virtual function int get_min_as_int();
		
		pure virtual function real get_typ();
		
		pure virtual function int get_typ_as_int();
		
		pure virtual function real get_max();
		
		pure virtual function int get_max_as_int();
		
		pure virtual function time get_time_scale();
		
	endclass
	
	class edf_parameter_base implements edf_parameter;
		
		function new();
			// nothing to do here
		endfunction
		
		virtual function string get_name();
		endfunction
		
		virtual function real get_min();
		endfunction
		
		virtual function real get_typ();
		endfunction
		
		virtual function real get_max();
		endfunction
		
		virtual function time get_time_scale();
		endfunction

		virtual function int get_min_as_int();
			return int'(get_min());
		endfunction
		
		virtual function int get_typ_as_int();
			return int'(get_typ());
		endfunction
		
		virtual function int get_max_as_int();
			return int'(get_max());
		endfunction
		
		virtual function time get_min_time();
			return get_min() * get_time_scale();
		endfunction
		
		virtual function time get_typ_time();
			return get_typ() * get_time_scale();
		endfunction
		
		virtual function time get_max_time();
			return get_max() * get_time_scale();
		endfunction
	endclass

	class epm_IC_REV extends edf_parameter_base;
		const string name = "IC_REV";
		const real min = 1178;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class epm_V__DIO_OL__ extends edf_parameter_base;
		const string name = "V__DIO,OL__";
		const string unit = "V__IO__";
		const real min = 0.0;
		const real max = 0.2;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__DIO_OH__ extends edf_parameter_base;
		const string name = "V__DIO,OH__";
		const string unit = "V__IO__";
		const real min = 0.8;
		const real max = 1.0;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DIO_LEAK__ extends edf_parameter_base;
		const string name = "I__DIO,LEAK__";
		const string unit = "µA";
		const real min = -1;
		const real max = 1;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_R__DIO_PU__ extends edf_parameter_base;
		const string name = "R__DIO,PU__";
		const string unit = "k$$\Omega$$";
		const real min = 60;
		const real max = 140;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_R__DIO_PD__ extends edf_parameter_base;
		const string name = "R__DIO,PD__";
		const string unit = "k$$\Omega$$";
		const real min = 50;
		const real max = 160;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__orf__ extends edf_parameter_base;
		const string name = "t__orf__";
		const string unit = "ns";
		const real min = 1;
		const real max = 9;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__DIO_TH__ extends edf_parameter_base;
		const string name = "V__DIO,TH__";
		const string unit = "V__IO__";
		const real min = 0.3;
		const real max = 0.7;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__DIO_TH_18__ extends edf_parameter_base;
		const string name = "V__DIO,TH,18__";
		const string unit = "V__IO__";
		const real min = 0.25;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_C__DIO_IO__ extends edf_parameter_base;
		const string name = "C__DIO_IO__";
		const string unit = "pF";
		const real max = 6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__RESB_deb__ extends edf_parameter_base;
		const string name = "t__RESB,deb__";
		const string unit = "µs";
		const real min = 0.7;
		const real typ = 0.9;
		const real max = 1.6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__VSUP__ extends edf_parameter_base;
		const string name = "I__VSUP__";
		const string unit = "mA";
		const real min = 5;
		const real max = 32;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__VIO_idle__ extends edf_parameter_base;
		const string name = "I__VIO,idle__";
		const string unit = "µA";
		const real min = -10;
		const real max = 10;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VCC__ extends edf_parameter_base;
		const string name = "V__VCC__";
		const string unit = "V";
		const real min = 4.75;
		const real typ = 5;
		const real max = 5.25;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__VCC_SHORT__ extends edf_parameter_base;
		const string name = "I__VCC,SHORT__";
		const string unit = "mA";
		const real min = -50;
		const real max = -20;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VCC_UV_fall__ extends edf_parameter_base;
		const string name = "V__VCC,UV,fall__";
		const string unit = "V";
		const real min = 4.2;
		const real typ = 4.35;
		const real max = 4.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VCC_UV_rise__ extends edf_parameter_base;
		const string name = "V__VCC,UV,rise__";
		const string unit = "V";
		const real min = 4.35;
		const real typ = 4.5;
		const real max = 4.65;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VCC_UV_hyst__ extends edf_parameter_base;
		const string name = "V__VCC,UV,hyst__";
		const string unit = "mV";
		const real min = 100;
		const real typ = 150;
		const real max = 200;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__VCC_UV_deb__ extends edf_parameter_base;
		const string name = "t__VCC,UV,deb__";
		const string unit = "µs";
		const real min = 70;
		const real typ = 75;
		const real max = 80;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VDD__ extends edf_parameter_base;
		const string name = "V__VDD__";
		const string unit = "V";
		const real min = 1.7;
		const real typ = 1.8;
		const real max = 1.9;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__VDD_SHORT__ extends edf_parameter_base;
		const string name = "I__VDD,SHORT__";
		const string unit = "mA";
		const real min = -50;
		const real max = -20;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VDD_POR_Fall__ extends edf_parameter_base;
		const string name = "V__VDD,POR,Fall__";
		const string unit = "V";
		const real min = 1.4;
		const real typ = 1.5;
		const real max = 1.6;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VDD_POR_Rise__ extends edf_parameter_base;
		const string name = "V__VDD,POR,Rise__";
		const string unit = "V";
		const real min = 1.5;
		const real typ = 1.6;
		const real max = 1.7;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VDD_POR_HYST__ extends edf_parameter_base;
		const string name = "V__VDD,POR,HYST__";
		const string unit = "mV";
		const real min = 50;
		const real typ = 100;
		const real max = 150;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__CLDO__ extends edf_parameter_base;
		const string name = "V__CLDO__";
		const string unit = "V";
		const real min = 5.5;
		const real typ = 5.8;
		const real max = 6;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__CLDO_SHORT__ extends edf_parameter_base;
		const string name = "I__CLDO,SHORT__";
		const string unit = "mA";
		const real min = -235;
		const real max = -120;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_r__CLDO_UV_rise__ extends edf_parameter_base;
		const string name = "r__CLDO,UV,rise__";
		const real min = 0.85;
		const real typ = 0.89;
		const real max = 0.93;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_r__CLDO_UV_fall__ extends edf_parameter_base;
		const string name = "r__CLDO,UV,fall__";
		const real min = 0.76;
		const real typ = 0.8;
		const real max = 0.84;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CLDO_UV__ extends edf_parameter_base;
		const string name = "t__CLDO,UV__";
		const string unit = "µs";
		const real min = 8;
		const real typ = 10;
		const real max = 12;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__startup__ extends edf_parameter_base;
		const string name = "t__startup__";
		const string unit = "ms";
		const real typ = 2;
		const real max = 4;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ms;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI_restart__ extends edf_parameter_base;
		const string name = "t__DSI,restart__";
		const string unit = "µs";
		const real min = 0;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_T__J_OT_warn_on__ extends edf_parameter_base;
		const string name = "T__J,OT,warn,on__";
		const string unit = "°C";
		const real min = 125;
		const real max = 150;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_T__J_OT_warn_off__ extends edf_parameter_base;
		const string name = "T__J,OT,warn,off__";
		const string unit = "°C";
		const real min = 110;
		const real max = 135;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm____Delta__T__J_we__ extends edf_parameter_base;
		const string name = "$$\Delta$$T__J,we__";
		const string unit = "K";
		const real min = 12;
		const real typ = 15;
		const real max = 20;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_T__J_OT_err__ extends edf_parameter_base;
		const string name = "T__J,OT,err__";
		const string unit = "°C";
		const real min = 140;
		const real max = 170;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_T__J_OT_err_off__ extends edf_parameter_base;
		const string name = "T__J,OT,err,off__";
		const string unit = "°C";
		const real min = 125;
		const real max = 155;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__temp__ extends edf_parameter_base;
		const string name = "V__temp__";
		const string unit = "mV";
		const real min = 1000;
		const real typ = 1100;
		const real max = 1200;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_tk__Vtemp__ extends edf_parameter_base;
		const string name = "tk__Vtemp__";
		const string unit = "mV/K";
		const real typ = -6.5;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class epm_t__OT_deb__ extends edf_parameter_base;
		const string name = "t__OT,deb__";
		const string unit = "µs";
		const real min = 5;
		const real typ = 10;
		const real max = 15;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__temp_OT_err__ extends edf_parameter_base;
		const string name = "V__temp_OT,err__";
		const string unit = "V";
		const real min = 0.89;
		const real typ = 0.925;
		const real max = 0.95;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__temp_OT_err_off__ extends edf_parameter_base;
		const string name = "V__temp_OT,err,off__";
		const string unit = "V";
		const real min = 1.00;
		const real typ = 1.035;
		const real max = 1.07;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__temp_OT_warn__ extends edf_parameter_base;
		const string name = "V__temp_OT,warn__";
		const string unit = "V";
		const real min = 1.00;
		const real typ = 1.035;
		const real max = 1.07;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__temp_OT_warn_off__ extends edf_parameter_base;
		const string name = "V__temp_OT,warn,off__";
		const string unit = "V";
		const real min = 1.08;
		const real typ = 1.125;
		const real max = 1.16;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VBG__ extends edf_parameter_base;
		const string name = "V__VBG__";
		const string unit = "V";
		const real min = 1.2;
		const real typ = 1.25;
		const real max = 1.3;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__5u_untrimmed__ extends edf_parameter_base;
		const string name = "I__5u_untrimmed__";
		const string unit = "µA";
		const real min = -6.25;
		const real typ = -5;
		const real max = -3.75;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__5u_trimmed__ extends edf_parameter_base;
		const string name = "I__5u_trimmed__";
		const string unit = "µA";
		const real min = -5.2;
		const real typ = -5;
		const real max = -4.8;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__BP10U__ extends edf_parameter_base;
		const string name = "I__BP10U__";
		const string unit = "µA";
		const real min = -15;
		const real typ = -10;
		const real max = -5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VRR_UV__ extends edf_parameter_base;
		const string name = "V__VRR_UV__";
		const string unit = "V";
		const real min = 2.2;
		const real typ = 2.4;
		const real max = 2.6;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__VRR_OV__ extends edf_parameter_base;
		const string name = "V__VRR_OV__";
		const string unit = "V";
		const real min = 3.4;
		const real typ = 3.6;
		const real max = 3.8;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__VBGerr_deb__ extends edf_parameter_base;
		const string name = "t__VBGerr,deb__";
		const string unit = "µs";
		const real min = 60;
		const real typ = 75;
		const real max = 90;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__DSI_HIGH__ extends edf_parameter_base;
		const string name = "V__DSI,HIGH__";
		const string unit = "V";
		const real min = 4.1;
		const real typ = 4.5;
		const real max = 4.9;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm____Delta__V__DSI__ extends edf_parameter_base;
		const string name = "$$\Delta$$V__DSI__";
		const string unit = "V";
		const real min = 1.75;
		const real typ = 2;
		const real max = 2.25;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_R__DSI_M__ extends edf_parameter_base;
		const string name = "R__DSI,M__";
		const string unit = "$$\Omega$$";
		const real max = 6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI_BIT_8__ extends edf_parameter_base;
		const string name = "t__DSI,BIT,8__";
		const string unit = "µs";
		const real min = 7.97;
		const real typ = 8.00;
		const real max = 8.03;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI_BIT_16__ extends edf_parameter_base;
		const string name = "t__DSI,BIT,16__";
		const string unit = "µs";
		const real min = 15.94;
		const real typ = 16;
		const real max = 16.06;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI_BIT_32__ extends edf_parameter_base;
		const string name = "t__DSI,BIT,32__";
		const string unit = "µs";
		const real min = 31.88;
		const real typ = 32;
		const real max = 32.12;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI_BIT_TOL__ extends edf_parameter_base;
		const string name = "t__DSI,BIT,TOL__";
		const string unit = "%";
		const real min = -0.3;
		const real max = 0.3;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_SR__EMC_HL__ extends edf_parameter_base;
		const string name = "SR__EMC,HL__";
		const string unit = "µs";
		const real min = 2;
		const real typ = 2.5;
		const real max = 3;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_SR__EMC_LH__ extends edf_parameter_base;
		const string name = "SR__EMC,LH__";
		const string unit = "µs";
		const real min = 2;
		const real typ = 2.5;
		const real max = 3;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_SR__STP_HL__ extends edf_parameter_base;
		const string name = "SR__STP,HL__";
		const string unit = "ns";
		const real min = 10;
		const real max = 1000;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_SR__STP_LH__ extends edf_parameter_base;
		const string name = "SR__STP,LH__";
		const string unit = "ns";
		const real min = 10;
		const real max = 1000;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DSI_CL_HI__ extends edf_parameter_base;
		const string name = "I__DSI,CL,HI__";
		const string unit = "mA";
		const real min = -135;
		const real max = -30;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DSI_CL_LO__ extends edf_parameter_base;
		const string name = "I__DSI,CL,LO__";
		const string unit = "mA";
		const real min = 40;
		const real max = 110;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSImon_TO__ extends edf_parameter_base;
		const string name = "t__DSImon,TO__";
		const string unit = "ms";
		const real min = 2;
		const real typ = 5;
		const real max = 7;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ms;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DSI_RESP_1__ extends edf_parameter_base;
		const string name = "I__DSI,RESP,1__";
		const string unit = "mA";
		const real min = -7.0;
		const real typ = -6.0;
		const real max = -5.0;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DSI_RESP_1_hys__ extends edf_parameter_base;
		const string name = "I__DSI,RESP,1,hys__";
		const string unit = "mA";
		const real min = 0.10;
		const real typ = 0.4;
		const real max = 0.61;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DSI_RESP_2__ extends edf_parameter_base;
		const string name = "I__DSI,RESP,2__";
		const string unit = "mA";
		const real min = -19.0;
		const real typ = -18.0;
		const real max = -17.0;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DSI_RESP_2_hys__ extends edf_parameter_base;
		const string name = "I__DSI,RESP,2,hys__";
		const string unit = "mA";
		const real min = 0.10;
		const real typ = 0.4;
		const real max = 0.61;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_dI__DSI_RESP_LSB__ extends edf_parameter_base;
		const string name = "dI__DSI,RESP_LSB__";
		const string unit = "mA / LSB";
		const real min = 0.3;
		const real typ = 0.4;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DAC_00001__ extends edf_parameter_base;
		const string name = "I__DAC,00001__";
		const string unit = "uA";
		const real min = 1.4;
		const real typ = 2;
		const real max = 2.6;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DAC_00010__ extends edf_parameter_base;
		const string name = "I__DAC,00010__";
		const string unit = "uA";
		const real min = 3;
		const real typ = 4;
		const real max = 5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DAC_00100__ extends edf_parameter_base;
		const string name = "I__DAC,00100__";
		const string unit = "uA";
		const real min = 6.5;
		const real typ = 8;
		const real max = 10.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DAC_01000__ extends edf_parameter_base;
		const string name = "I__DAC,01000__";
		const string unit = "uA";
		const real min = 13.5;
		const real typ = 16;
		const real max = 19.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_I__DAC_11111__ extends edf_parameter_base;
		const string name = "I__DAC,11111__";
		const string unit = "uA";
		const real min = 54;
		const real typ = 63;
		const real max = 73;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_IDAC__value_opt__ extends edf_parameter_base;
		const string name = "IDAC__value_opt__";
		const string unit = "LSB/mA";
		const real typ = 5;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class epm_t__d_DSI_RESP_01__ extends edf_parameter_base;
		const string name = "t__d,DSI,RESP,01__";
		const string unit = "µs";
		const real min = 0.2;
		const real typ = 0.5;
		const real max = 1.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_RESP_10__ extends edf_parameter_base;
		const string name = "t__d,DSI,RESP,10__";
		const string unit = "µs";
		const real min = 0.2;
		const real typ = 0.5;
		const real max = 1.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_RESP_12__ extends edf_parameter_base;
		const string name = "t__d,DSI,RESP,12__";
		const string unit = "µs";
		const real min = 0.2;
		const real typ = 0.5;
		const real max = 1.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_RESP_21__ extends edf_parameter_base;
		const string name = "t__d,DSI,RESP,21__";
		const string unit = "µs";
		const real min = 0.2;
		const real typ = 0.5;
		const real max = 1.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_RESP_02__ extends edf_parameter_base;
		const string name = "t__d,DSI,RESP,02__";
		const string unit = "µs";
		const real min = 0.2;
		const real typ = 0.8;
		const real max = 1.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_RESP_20__ extends edf_parameter_base;
		const string name = "t__d,DSI,RESP,20__";
		const string unit = "µs";
		const real min = 0.2;
		const real typ = 0.8;
		const real max = 1.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__P_DSI_RX_min__ extends edf_parameter_base;
		const string name = "t__P,DSI,RX,min__";
		const string unit = "µs";
		const real min = 0.2;
		const real max = 0.6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_01_10__ extends edf_parameter_base;
		const string name = "t__d,DSI,01,10__";
		const string unit = "µs";
		const real min = -0.75;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_01_12__ extends edf_parameter_base;
		const string name = "t__d,DSI,01,12__";
		const string unit = "µs";
		const real min = -0.75;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_01_21__ extends edf_parameter_base;
		const string name = "t__d,DSI,01,21__";
		const string unit = "µs";
		const real min = -0.75;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_01_02__ extends edf_parameter_base;
		const string name = "t__d,DSI,01,02__";
		const string unit = "µs";
		const real min = -1.0;
		const real max = 0.6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_02_20__ extends edf_parameter_base;
		const string name = "t__d,DSI,02,20__";
		const string unit = "µs";
		const real min = -0.9;
		const real max = 0.9;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_02_21__ extends edf_parameter_base;
		const string name = "t__d,DSI,02,21__";
		const string unit = "µs";
		const real min = -0.5;
		const real max = 1.25;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_10_01__ extends edf_parameter_base;
		const string name = "t__d,DSI,10,01__";
		const string unit = "µs";
		const real min = -0.75;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_10_02__ extends edf_parameter_base;
		const string name = "t__d,DSI,10,02__";
		const string unit = "µs";
		const real min = -1.25;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_12_20__ extends edf_parameter_base;
		const string name = "t__d,DSI,12,20__";
		const string unit = "µs";
		const real min = -1.00;
		const real max = 0.6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_12_21__ extends edf_parameter_base;
		const string name = "t__d,DSI,12,21__";
		const string unit = "µs";
		const real min = -0.9;
		const real max = 0.9;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_20_01__ extends edf_parameter_base;
		const string name = "t__d,DSI,20,01__";
		const string unit = "µs";
		const real min = -0.5;
		const real max = 1.25;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_20_02__ extends edf_parameter_base;
		const string name = "t__d,DSI,20,02__";
		const string unit = "µs";
		const real min = -0.9;
		const real max = 0.9;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_21_10__ extends edf_parameter_base;
		const string name = "t__d,DSI,21,10__";
		const string unit = "µs";
		const real min = -0.75;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_21_12__ extends edf_parameter_base;
		const string name = "t__d,DSI,21,12__";
		const string unit = "µs";
		const real min = -0.9;
		const real max = 0.9;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_21_01__ extends edf_parameter_base;
		const string name = "t__d,DSI,21,01__";
		const string unit = "µs";
		const real min = -0.75;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_21_20__ extends edf_parameter_base;
		const string name = "t__d,DSI,21,20__";
		const string unit = "µs";
		const real min = -1.0;
		const real max = 0.6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__d_DSI_diff_max__ extends edf_parameter_base;
		const string name = "t__d,DSI,diff,max__";
		const string unit = "µs";
		const real min = 0.0;
		const real typ = 0.25;
		const real max = 0.75;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_ratio__td_DSI_fast_normal__ extends edf_parameter_base;
		const string name = "ratio__td,DSI,fast-normal__";
		const real min = 0.3;
		const real typ = 0.6;
		const real max = 0.95;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_answer_low_8__ extends edf_parameter_base;
		const string name = "t__CRM,answer,low,8__";
		const string unit = "µs";
		const real min = 265;
		const real max = 280;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_answer_high_8__ extends edf_parameter_base;
		const string name = "t__CRM,answer,high,8__";
		const string unit = "µs";
		const real min = 310;
		const real max = 320;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_answer_low_16__ extends edf_parameter_base;
		const string name = "t__CRM,answer,low,16__";
		const string unit = "µs";
		const real min = 530;
		const real max = 560;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_answer_high_16__ extends edf_parameter_base;
		const string name = "t__CRM,answer,high,16__";
		const string unit = "µs";
		const real min = 620;
		const real max = 640;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_answer_low_32__ extends edf_parameter_base;
		const string name = "t__CRM,answer,low,32__";
		const string unit = "µs";
		const real min = 1060;
		const real max = 1120;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_answer_high_32__ extends edf_parameter_base;
		const string name = "t__CRM,answer,high,32__";
		const string unit = "µs";
		const real min = 1240;
		const real max = 1280;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_start__ extends edf_parameter_base;
		const string name = "t__CRM,start__";
		const string unit = "µs";
		const real min = 0;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CRM_davail__ extends edf_parameter_base;
		const string name = "t__CRM,davail__";
		const string unit = "µs";
		const real min = 0;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__PDCM_davail__ extends edf_parameter_base;
		const string name = "t__PDCM,davail__";
		const string unit = "us";
		const real min = -15;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class epm_t__Disc_pulse_8__ extends edf_parameter_base;
		const string name = "t__Disc_pulse,8__";
		const string unit = "µs";
		const real min = 15.98;
		const real typ = 16;
		const real max = 16.02;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_pulse_16__ extends edf_parameter_base;
		const string name = "t__Disc_pulse,16__";
		const string unit = "µs";
		const real min = 31.96;
		const real typ = 32;
		const real max = 32.04;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_pulse_32__ extends edf_parameter_base;
		const string name = "t__Disc_pulse,32__";
		const string unit = "µs";
		const real min = 63.92;
		const real typ = 64;
		const real max = 64.08;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_per_8__ extends edf_parameter_base;
		const string name = "t__Disc_per,8__";
		const string unit = "µs";
		const real min = 124;
		const real typ = 125;
		const real max = 126.25;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_per_16__ extends edf_parameter_base;
		const string name = "t__Disc_per,16__";
		const string unit = "µs";
		const real min = 188;
		const real typ = 189;
		const real max = 190;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_per_32__ extends edf_parameter_base;
		const string name = "t__Disc_per,32__";
		const string unit = "µs";
		const real min = 316;
		const real typ = 317;
		const real max = 318;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_Accept__ extends edf_parameter_base;
		const string name = "t__Disc,Accept__";
		const string unit = "µs";
		const real min = 10;
		const real typ = 16;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class epm_t__Disc_dly_valid_8__ extends edf_parameter_base;
		const string name = "t__Disc_dly_valid,8__";
		const string unit = "µs";
		const real min = 50;
		const real max = 80;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_dly_valid_16__ extends edf_parameter_base;
		const string name = "t__Disc_dly_valid,16__";
		const string unit = "µs";
		const real min = 100;
		const real max = 160;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__Disc_dly_valid_32__ extends edf_parameter_base;
		const string name = "t__Disc_dly_valid,32__";
		const string unit = "µs";
		const real min = 200;
		const real max = 320;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__smdv__ extends edf_parameter_base;
		const string name = "t__smdv__";
		const string unit = "ns";
		const real min = 0;
		const real max = 15;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__smdv_1V8__ extends edf_parameter_base;
		const string name = "t__smdv,1V8__";
		const string unit = "ns";
		const real min = 0;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__cmdisla__ extends edf_parameter_base;
		const string name = "t__cmdisla__";
		const string unit = "ns";
		const real min = 0;
		const real max = 100;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__cmdv__ extends edf_parameter_base;
		const string name = "t__cmdv__";
		const string unit = "ns";
		const real min = 0;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__DSI_UV_act___V__DSI__ extends edf_parameter_base;
		const string name = "V__DSI,UV,act__/V__DSI__";
		const real min = 0.5;
		const real max = 0.67;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_V__DSI_OV_act___V__CLDO__ extends edf_parameter_base;
		const string name = "V__DSI,OV,act__/V__CLDO__";
		const real min = 0.88;
		const real typ = 0.91;
		const real max = 0.98;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI3_sync__ extends edf_parameter_base;
		const string name = "t__DSI3,sync__";
		const string unit = "µs";
		const real min = 0;
		const real max = 2;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__DSI3_master_sync__ extends edf_parameter_base;
		const string name = "t__DSI3,master_sync__";
		const string unit = "µs";
		const real min = 7;
		const real typ = 10;
		const real max = 14;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_f__CLK_PLL__ extends edf_parameter_base;
		const string name = "f__CLK,PLL__";
		const string unit = "MHz";
		const real min = 17.982;
		const real typ = 18.0;
		const real max = 18.018;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_f__OSC_RC__ extends edf_parameter_base;
		const string name = "f__OSC,RC__";
		const string unit = "MHz";
		const real min = 17.46;
		const real typ = 18;
		const real max = 18.54;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_r__CLKREF_err_ul__ extends edf_parameter_base;
		const string name = "r__CLKREF,err,ul__";
		const real min = 1.04;
		const real max = 1.17;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_r__CLKREF_err_ll__ extends edf_parameter_base;
		const string name = "r__CLKREF,err,ll__";
		const real min = 0.86;
		const real max = 0.96;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CLKREF_filt__ extends edf_parameter_base;
		const string name = "t__CLKREF,filt__";
		const string unit = "ns";
		const real min = 40;
		const real typ = 80;
		const real max = 120;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__CLKREF_sync__ extends edf_parameter_base;
		const string name = "t__CLKREF,sync__";
		const string unit = "ms";
		const real min = 0.1;
		const real max = 2;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ms;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_f__OSC_OSC20M__ extends edf_parameter_base;
		const string name = "f__OSC,OSC20M__";
		const string unit = "MHz";
		const real min = 10;
		const real typ = 20;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__OTP_prog_pulse__ extends edf_parameter_base;
		const string name = "t__OTP,prog_pulse__";
		const string unit = "µs";
		const real min = 100;
		const real max = 105;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Sense_Amplifier_Mode_P extends edf_parameter_base;
		const string name = "Sense Amplifier Mode P";
		const real min = 4094.5;
		const real typ = 4095;
		const real max = 4095.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Sense_Amplifier_Mode_N extends edf_parameter_base;
		const string name = "Sense Amplifier Mode N";
		const real min = -0.5;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Wordline_Continuity extends edf_parameter_base;
		const string name = "Wordline Continuity";
		const real min = -0.5;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Bitline_Continuity extends edf_parameter_base;
		const string name = "Bitline Continuity";
		const real min = -0.5;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Read_Cell_Stress extends edf_parameter_base;
		const string name = "Read Cell Stress";
		const real min = -0.5;
		const real typ = 0;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Array_Clean extends edf_parameter_base;
		const string name = "Array Clean";
		const real min = -0.5;
		const real typ = 0;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Program_and_Verify extends edf_parameter_base;
		const string name = "Program and Verify";
		const real min = 1.9;
		const real typ = 2.0;
		const real max = 2.1;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Program_Soak_Pulses extends edf_parameter_base;
		const string name = "Program/Soak Pulses";
		const real max = 11;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_Mission_Mode extends edf_parameter_base;
		const string name = "Mission Mode";
		const real min = -0.5;
		const real typ = 0;
		const real max = 0.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class epm_t__SRAM_BIST__ extends edf_parameter_base;
		const string name = "t__SRAM_BIST__";
		const string unit = "ms";
		const real min = 3;
		const real max = 5;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ms;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_T__J__ extends edf_parameter_base;
		const string name = "T__J__";
		const string unit = "°C";
		const real min = -40;
		const real max = 150;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_T__STG__ extends edf_parameter_base;
		const string name = "T__STG__";
		const string unit = "°C";
		const real min = -55;
		const real max = 150;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__CLDO__ extends edf_parameter_base;
		const string name = "V__CLDO__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 20;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__DIO__ extends edf_parameter_base;
		const string name = "V__DIO__";
		const string unit = "V";
		const real min = -0.3;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class max_I__DIO__ extends edf_parameter_base;
		const string name = "I__DIO__";
		const string unit = "mA";
		const real min = -10;
		const real max = 10;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__VIO__ extends edf_parameter_base;
		const string name = "V__VIO__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 5.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__VSUP__ extends edf_parameter_base;
		const string name = "V__VSUP__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__VSUP_TRAN__ extends edf_parameter_base;
		const string name = "V__VSUP,TRAN__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 40;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__VCC__ extends edf_parameter_base;
		const string name = "V__VCC__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 5.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__VDD__ extends edf_parameter_base;
		const string name = "V__VDD__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 1.98;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__DSIn__ extends edf_parameter_base;
		const string name = "V__DSIn__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 30;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class max_V__DSIn_TRAN__ extends edf_parameter_base;
		const string name = "V__DSIn,TRAN__";
		const string unit = "V";
		const real min = -0.3;
		const real max = 40;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_C__DIO_LOAD__ extends edf_parameter_base;
		const string name = "C__DIO,LOAD__";
		const string unit = "pF";
		const real max = 20;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__irf__ extends edf_parameter_base;
		const string name = "t__irf__";
		const string unit = "ns";
		const real max = 6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__RESB__ extends edf_parameter_base;
		const string name = "t__RESB__";
		const string unit = "µs";
		const real min = 20;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_V__VSUP__ extends edf_parameter_base;
		const string name = "V__VSUP__";
		const string unit = "V";
		const real min = 6;
		const real max = 18;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_dV__VSUP___dt extends edf_parameter_base;
		const string name = "dV__VSUP__/dt";
		const string unit = "V/µs";
		const real max = 1;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_V__VIO__ extends edf_parameter_base;
		const string name = "V__VIO__";
		const string unit = "V";
		const real min = 1.65;
		const real typ = 5.0;
		const real max = 5.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_T__AMB__ extends edf_parameter_base;
		const string name = "T__AMB__";
		const string unit = "°C";
		const real min = -40;
		const real max = 105;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_C__VSUP__ extends edf_parameter_base;
		const string name = "C__VSUP__";
		const string unit = "$$\mu$$F";
	
		virtual function string get_name();
			return name;
		endfunction
	endclass
		
	class rec_C__VCC__ extends edf_parameter_base;
		const string name = "C__VCC__";
		const string unit = "nF";
		const real typ = 100;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class rec_C__VDD__ extends edf_parameter_base;
		const string name = "C__VDD__";
		const string unit = "nF";
		const real typ = 330;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class rec_C__CLDO_e__ extends edf_parameter_base;
		const string name = "C__CLDO,e__";
		const string unit = "µF";
		const real typ = 22;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class rec_C__CLDO_c__ extends edf_parameter_base;
		const string name = "C__CLDO,c__";
		const string unit = "µF";
		const real typ = 1;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class rec_I__DSI_Q__ extends edf_parameter_base;
		const string name = "I__DSI,Q__";
		const string unit = "mA";
		const real min = -4.5;
		const real max = 0;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_C__DSI_sum__ extends edf_parameter_base;
		const string name = "C__DSI,sum__";
		const string unit = "nF";
		const real min = 15;
		const real typ = 30;
		const real max = 50;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__DSI_CHIP__ extends edf_parameter_base;
		const string name = "t__DSI,CHIP__";
		const string unit = "µs";
		const real min = 2;
		const real typ = 3;
		const real max = 5;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__DSI_SYMBOL__ extends edf_parameter_base;
		const string name = "t__DSI,SYMBOL__";
		const string unit = "t__DSI,CHIP__";
		const real typ = 3;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_typ();
			return typ;
		endfunction	
	endclass
		
	class rec_t__DSI_CHIP_TOL__ extends edf_parameter_base;
		const string name = "t__DSI,CHIP,TOL__";
		const string unit = "%";
		const real min = -5;
		const real max = 5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_I__DSI_REC_1__ extends edf_parameter_base;
		const string name = "I__DSI,REC,1__";
		const string unit = "mA";
		const real min = 10.5;
		const real typ = 12;
		const real max = 13.5;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_I__DSI_REC_2__ extends edf_parameter_base;
		const string name = "I__DSI,REC,2__";
		const string unit = "mA";
		const real min = 21;
		const real typ = 24;
		const real max = 27;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__CRM_answer__ extends edf_parameter_base;
		const string name = "t__CRM,answer__";
		const string unit = "µs";
		const real min = 280;
		const real typ = 295;
		const real max = 310;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__PDCM_PER__ extends edf_parameter_base;
		const string name = "t__PDCM,PER__";
		const string unit = "ms";
		const real min = 0.1;
		const real max = 65;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ms;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__PDCM_START__ extends edf_parameter_base;
		const string name = "t__PDCM,START__";
	
		virtual function string get_name();
			return name;
		endfunction
	endclass
		
	class rec_t__PDCM_END__ extends edf_parameter_base;
		const string name = "t__PDCM,END__";
		const string unit = "µs";
		const real min = 15;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__response_IPS__ extends edf_parameter_base;
		const string name = "t__response,IPS__";
		const string unit = "t__CHIP__";
		const real min = 6;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__Disc_dly_8__ extends edf_parameter_base;
		const string name = "t__Disc_dly,8__";
		const string unit = "µs";
		const real min = 58;
		const real typ = 64;
		const real max = 70;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__Disc_dly_16__ extends edf_parameter_base;
		const string name = "t__Disc_dly,16__";
		const string unit = "µs";
		const real min = 116;
		const real typ = 128;
		const real max = 140;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__Disc_dly_32__ extends edf_parameter_base;
		const string name = "t__Disc_dly,32__";
		const string unit = "µs";
		const real min = 232;
		const real typ = 256;
		const real max = 280;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__Disc_ramp__ extends edf_parameter_base;
		const string name = "t__Disc_ramp__";
		const string unit = "µs";
		const real min = 16;
		const real max = 20;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__Disc_width__ extends edf_parameter_base;
		const string name = "t__Disc_width__";
		const string unit = "µs";
		const real min = 24;
		const real max = 32;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_f__SPI__ extends edf_parameter_base;
		const string name = "f__SPI__";
		const string unit = "MHz";
		const real max = 16.8;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_f__SPI_LV__ extends edf_parameter_base;
		const string name = "f__SPI,LV__";
		const string unit = "MHz";
		const real max = 12.6;
	
		virtual function string get_name();
			return name;
		endfunction
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_t__csdisle__ extends edf_parameter_base;
		const string name = "t__csdisle__";
		const string unit = "ns";
		const real min = 100;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__csdisla__ extends edf_parameter_base;
		const string name = "t__csdisla__";
		const string unit = "ns";
		const real min = 100;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__csenle__ extends edf_parameter_base;
		const string name = "t__csenle__";
		const string unit = "ns";
		const real min = 10;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__csenla__ extends edf_parameter_base;
		const string name = "t__csenla__";
		const string unit = "ns";
		const real min = 10;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__shi__ extends edf_parameter_base;
		const string name = "t__shi__";
		const string unit = "ns";
		const real min = 20;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__slo__ extends edf_parameter_base;
		const string name = "t__slo__";
		const string unit = "ns";
		const real min = 20;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__smds__ extends edf_parameter_base;
		const string name = "t__smds__";
		const string unit = "ns";
		const real min = 10;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__smdh__ extends edf_parameter_base;
		const string name = "t__smdh__";
		const string unit = "ns";
		const real min = 10;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__cwof__ extends edf_parameter_base;
		const string name = "t__cwof__";
		const string unit = "ns";
		const real min = 20;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__iwg__ extends edf_parameter_base;
		const string name = "t__iwg__";
		const string unit = "ns";
		const real min = 250;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1ns;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_t__SYNCB_pw__ extends edf_parameter_base;
		const string name = "t__SYNCB,pw__";
		const string unit = "µs";
		const real min = 1;
	
		virtual function string get_name();
			return name;
		endfunction
	
		function time get_time_scale();
			return 1us;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	endclass
		
	class rec_f__CLKREF__ extends edf_parameter_base;
		const string name = "f__CLKREF__";
		const string unit = "kHz";
		const real min = 480;
		const real typ = 500;
		const real max = 520;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_f__CLK_REF_ROC__ extends edf_parameter_base;
		const string name = "f__CLK_REF_ROC__";
		const string unit = "MHz";
		const real min = 0.5;
		const real max = 4;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		
	class rec_D__CLKREF__ extends edf_parameter_base;
		const string name = "D__CLKREF__";
		const string unit = "%";
		const real min = 40;
		const real typ = 50;
		const real max = 60;
	
		virtual function string get_name();
			return name;
		endfunction
		
		virtual function real get_min();
			return min;
		endfunction	
	
		virtual function real get_typ();
			return typ;
		endfunction	
	
		virtual function real get_max();
			return max;
		endfunction	
	endclass
		

 	class edf_epms;
 		epm_IC_REV IC_REV = new();	
 		epm_V__DIO_OL__ V__DIO_OL__ = new();	
 		epm_V__DIO_OH__ V__DIO_OH__ = new();	
 		epm_I__DIO_LEAK__ I__DIO_LEAK__ = new();	
 		epm_R__DIO_PU__ R__DIO_PU__ = new();	
 		epm_R__DIO_PD__ R__DIO_PD__ = new();	
 		epm_t__orf__ t__orf__ = new();	
 		epm_V__DIO_TH__ V__DIO_TH__ = new();	
 		epm_V__DIO_TH_18__ V__DIO_TH_18__ = new();	
 		epm_C__DIO_IO__ C__DIO_IO__ = new();	
 		epm_t__RESB_deb__ t__RESB_deb__ = new();	
 		epm_I__VSUP__ I__VSUP__ = new();	
 		epm_I__VIO_idle__ I__VIO_idle__ = new();	
 		epm_V__VCC__ V__VCC__ = new();	
 		epm_I__VCC_SHORT__ I__VCC_SHORT__ = new();	
 		epm_V__VCC_UV_fall__ V__VCC_UV_fall__ = new();	
 		epm_V__VCC_UV_rise__ V__VCC_UV_rise__ = new();	
 		epm_V__VCC_UV_hyst__ V__VCC_UV_hyst__ = new();	
 		epm_t__VCC_UV_deb__ t__VCC_UV_deb__ = new();	
 		epm_V__VDD__ V__VDD__ = new();	
 		epm_I__VDD_SHORT__ I__VDD_SHORT__ = new();	
 		epm_V__VDD_POR_Fall__ V__VDD_POR_Fall__ = new();	
 		epm_V__VDD_POR_Rise__ V__VDD_POR_Rise__ = new();	
 		epm_V__VDD_POR_HYST__ V__VDD_POR_HYST__ = new();	
 		epm_V__CLDO__ V__CLDO__ = new();	
 		epm_I__CLDO_SHORT__ I__CLDO_SHORT__ = new();	
 		epm_r__CLDO_UV_rise__ r__CLDO_UV_rise__ = new();	
 		epm_r__CLDO_UV_fall__ r__CLDO_UV_fall__ = new();	
 		epm_t__CLDO_UV__ t__CLDO_UV__ = new();	
 		epm_t__startup__ t__startup__ = new();	
 		epm_t__DSI_restart__ t__DSI_restart__ = new();	
 		epm_T__J_OT_warn_on__ T__J_OT_warn_on__ = new();	
 		epm_T__J_OT_warn_off__ T__J_OT_warn_off__ = new();	
 		epm____Delta__T__J_we__ ___Delta__T__J_we__ = new();	
 		epm_T__J_OT_err__ T__J_OT_err__ = new();	
 		epm_T__J_OT_err_off__ T__J_OT_err_off__ = new();	
 		epm_V__temp__ V__temp__ = new();	
 		epm_tk__Vtemp__ tk__Vtemp__ = new();	
 		epm_t__OT_deb__ t__OT_deb__ = new();	
 		epm_V__temp_OT_err__ V__temp_OT_err__ = new();	
 		epm_V__temp_OT_err_off__ V__temp_OT_err_off__ = new();	
 		epm_V__temp_OT_warn__ V__temp_OT_warn__ = new();	
 		epm_V__temp_OT_warn_off__ V__temp_OT_warn_off__ = new();	
 		epm_V__VBG__ V__VBG__ = new();	
 		epm_I__5u_untrimmed__ I__5u_untrimmed__ = new();	
 		epm_I__5u_trimmed__ I__5u_trimmed__ = new();	
 		epm_I__BP10U__ I__BP10U__ = new();	
 		epm_V__VRR_UV__ V__VRR_UV__ = new();	
 		epm_V__VRR_OV__ V__VRR_OV__ = new();	
 		epm_t__VBGerr_deb__ t__VBGerr_deb__ = new();	
 		epm_V__DSI_HIGH__ V__DSI_HIGH__ = new();	
 		epm____Delta__V__DSI__ ___Delta__V__DSI__ = new();	
 		epm_R__DSI_M__ R__DSI_M__ = new();	
 		epm_t__DSI_BIT_8__ t__DSI_BIT_8__ = new();	
 		epm_t__DSI_BIT_16__ t__DSI_BIT_16__ = new();	
 		epm_t__DSI_BIT_32__ t__DSI_BIT_32__ = new();	
 		epm_t__DSI_BIT_TOL__ t__DSI_BIT_TOL__ = new();	
 		epm_SR__EMC_HL__ SR__EMC_HL__ = new();	
 		epm_SR__EMC_LH__ SR__EMC_LH__ = new();	
 		epm_SR__STP_HL__ SR__STP_HL__ = new();	
 		epm_SR__STP_LH__ SR__STP_LH__ = new();	
 		epm_I__DSI_CL_HI__ I__DSI_CL_HI__ = new();	
 		epm_I__DSI_CL_LO__ I__DSI_CL_LO__ = new();	
 		epm_t__DSImon_TO__ t__DSImon_TO__ = new();	
 		epm_I__DSI_RESP_1__ I__DSI_RESP_1__ = new();	
 		epm_I__DSI_RESP_1_hys__ I__DSI_RESP_1_hys__ = new();	
 		epm_I__DSI_RESP_2__ I__DSI_RESP_2__ = new();	
 		epm_I__DSI_RESP_2_hys__ I__DSI_RESP_2_hys__ = new();	
 		epm_dI__DSI_RESP_LSB__ dI__DSI_RESP_LSB__ = new();	
 		epm_I__DAC_00001__ I__DAC_00001__ = new();	
 		epm_I__DAC_00010__ I__DAC_00010__ = new();	
 		epm_I__DAC_00100__ I__DAC_00100__ = new();	
 		epm_I__DAC_01000__ I__DAC_01000__ = new();	
 		epm_I__DAC_11111__ I__DAC_11111__ = new();	
 		epm_IDAC__value_opt__ IDAC__value_opt__ = new();	
 		epm_t__d_DSI_RESP_01__ t__d_DSI_RESP_01__ = new();	
 		epm_t__d_DSI_RESP_10__ t__d_DSI_RESP_10__ = new();	
 		epm_t__d_DSI_RESP_12__ t__d_DSI_RESP_12__ = new();	
 		epm_t__d_DSI_RESP_21__ t__d_DSI_RESP_21__ = new();	
 		epm_t__d_DSI_RESP_02__ t__d_DSI_RESP_02__ = new();	
 		epm_t__d_DSI_RESP_20__ t__d_DSI_RESP_20__ = new();	
 		epm_t__P_DSI_RX_min__ t__P_DSI_RX_min__ = new();	
 		epm_t__d_DSI_01_10__ t__d_DSI_01_10__ = new();	
 		epm_t__d_DSI_01_12__ t__d_DSI_01_12__ = new();	
 		epm_t__d_DSI_01_21__ t__d_DSI_01_21__ = new();	
 		epm_t__d_DSI_01_02__ t__d_DSI_01_02__ = new();	
 		epm_t__d_DSI_02_20__ t__d_DSI_02_20__ = new();	
 		epm_t__d_DSI_02_21__ t__d_DSI_02_21__ = new();	
 		epm_t__d_DSI_10_01__ t__d_DSI_10_01__ = new();	
 		epm_t__d_DSI_10_02__ t__d_DSI_10_02__ = new();	
 		epm_t__d_DSI_12_20__ t__d_DSI_12_20__ = new();	
 		epm_t__d_DSI_12_21__ t__d_DSI_12_21__ = new();	
 		epm_t__d_DSI_20_01__ t__d_DSI_20_01__ = new();	
 		epm_t__d_DSI_20_02__ t__d_DSI_20_02__ = new();	
 		epm_t__d_DSI_21_10__ t__d_DSI_21_10__ = new();	
 		epm_t__d_DSI_21_12__ t__d_DSI_21_12__ = new();	
 		epm_t__d_DSI_21_01__ t__d_DSI_21_01__ = new();	
 		epm_t__d_DSI_21_20__ t__d_DSI_21_20__ = new();	
 		epm_t__d_DSI_diff_max__ t__d_DSI_diff_max__ = new();	
 		epm_ratio__td_DSI_fast_normal__ ratio__td_DSI_fast_normal__ = new();	
 		epm_t__CRM_answer_low_8__ t__CRM_answer_low_8__ = new();	
 		epm_t__CRM_answer_high_8__ t__CRM_answer_high_8__ = new();	
 		epm_t__CRM_answer_low_16__ t__CRM_answer_low_16__ = new();	
 		epm_t__CRM_answer_high_16__ t__CRM_answer_high_16__ = new();	
 		epm_t__CRM_answer_low_32__ t__CRM_answer_low_32__ = new();	
 		epm_t__CRM_answer_high_32__ t__CRM_answer_high_32__ = new();	
 		epm_t__CRM_start__ t__CRM_start__ = new();	
 		epm_t__CRM_davail__ t__CRM_davail__ = new();	
 		epm_t__PDCM_davail__ t__PDCM_davail__ = new();	
 		epm_t__Disc_pulse_8__ t__Disc_pulse_8__ = new();	
 		epm_t__Disc_pulse_16__ t__Disc_pulse_16__ = new();	
 		epm_t__Disc_pulse_32__ t__Disc_pulse_32__ = new();	
 		epm_t__Disc_per_8__ t__Disc_per_8__ = new();	
 		epm_t__Disc_per_16__ t__Disc_per_16__ = new();	
 		epm_t__Disc_per_32__ t__Disc_per_32__ = new();	
 		epm_t__Disc_Accept__ t__Disc_Accept__ = new();	
 		epm_t__Disc_dly_valid_8__ t__Disc_dly_valid_8__ = new();	
 		epm_t__Disc_dly_valid_16__ t__Disc_dly_valid_16__ = new();	
 		epm_t__Disc_dly_valid_32__ t__Disc_dly_valid_32__ = new();	
 		epm_t__smdv__ t__smdv__ = new();	
 		epm_t__smdv_1V8__ t__smdv_1V8__ = new();	
 		epm_t__cmdisla__ t__cmdisla__ = new();	
 		epm_t__cmdv__ t__cmdv__ = new();	
 		epm_V__DSI_UV_act___V__DSI__ V__DSI_UV_act___V__DSI__ = new();	
 		epm_V__DSI_OV_act___V__CLDO__ V__DSI_OV_act___V__CLDO__ = new();	
 		epm_t__DSI3_sync__ t__DSI3_sync__ = new();	
 		epm_t__DSI3_master_sync__ t__DSI3_master_sync__ = new();	
 		epm_f__CLK_PLL__ f__CLK_PLL__ = new();	
 		epm_f__OSC_RC__ f__OSC_RC__ = new();	
 		epm_r__CLKREF_err_ul__ r__CLKREF_err_ul__ = new();	
 		epm_r__CLKREF_err_ll__ r__CLKREF_err_ll__ = new();	
 		epm_t__CLKREF_filt__ t__CLKREF_filt__ = new();	
 		epm_t__CLKREF_sync__ t__CLKREF_sync__ = new();	
 		epm_f__OSC_OSC20M__ f__OSC_OSC20M__ = new();	
 		epm_t__OTP_prog_pulse__ t__OTP_prog_pulse__ = new();	
 		epm_Sense_Amplifier_Mode_P Sense_Amplifier_Mode_P = new();	
 		epm_Sense_Amplifier_Mode_N Sense_Amplifier_Mode_N = new();	
 		epm_Wordline_Continuity Wordline_Continuity = new();	
 		epm_Bitline_Continuity Bitline_Continuity = new();	
 		epm_Read_Cell_Stress Read_Cell_Stress = new();	
 		epm_Array_Clean Array_Clean = new();	
 		epm_Program_and_Verify Program_and_Verify = new();	
 		epm_Program_Soak_Pulses Program_Soak_Pulses = new();	
 		epm_Mission_Mode Mission_Mode = new();	
 		epm_t__SRAM_BIST__ t__SRAM_BIST__ = new();	
 	
		function new();
			// nothing to do here
		endfunction
 	endclass
 	
 	class edf_max_ratings;
 		max_T__J__ T__J__ = new();	
 		max_T__STG__ T__STG__ = new();	
 		max_V__CLDO__ V__CLDO__ = new();	
 		max_V__DIO__ V__DIO__ = new();	
 		max_I__DIO__ I__DIO__ = new();	
 		max_V__VIO__ V__VIO__ = new();	
 		max_V__VSUP__ V__VSUP__ = new();	
 		max_V__VSUP_TRAN__ V__VSUP_TRAN__ = new();	
 		max_V__VCC__ V__VCC__ = new();	
 		max_V__VDD__ V__VDD__ = new();	
 		max_V__DSIn__ V__DSIn__ = new();	
 		max_V__DSIn_TRAN__ V__DSIn_TRAN__ = new();	
 	
		function new();
			// nothing to do here
		endfunction
 	endclass
 	
 	class edf_recommended_parameters;
 		rec_C__DIO_LOAD__ C__DIO_LOAD__ = new();	
 		rec_t__irf__ t__irf__ = new();	
 		rec_t__RESB__ t__RESB__ = new();	
 		rec_V__VSUP__ V__VSUP__ = new();	
 		rec_dV__VSUP___dt dV__VSUP___dt = new();	
 		rec_V__VIO__ V__VIO__ = new();	
 		rec_T__AMB__ T__AMB__ = new();	
 		rec_C__VSUP__ C__VSUP__ = new();	
 		rec_C__VCC__ C__VCC__ = new();	
 		rec_C__VDD__ C__VDD__ = new();	
 		rec_C__CLDO_e__ C__CLDO_e__ = new();	
 		rec_C__CLDO_c__ C__CLDO_c__ = new();	
 		rec_I__DSI_Q__ I__DSI_Q__ = new();	
 		rec_C__DSI_sum__ C__DSI_sum__ = new();	
 		rec_t__DSI_CHIP__ t__DSI_CHIP__ = new();	
 		rec_t__DSI_SYMBOL__ t__DSI_SYMBOL__ = new();	
 		rec_t__DSI_CHIP_TOL__ t__DSI_CHIP_TOL__ = new();	
 		rec_I__DSI_REC_1__ I__DSI_REC_1__ = new();	
 		rec_I__DSI_REC_2__ I__DSI_REC_2__ = new();	
 		rec_t__CRM_answer__ t__CRM_answer__ = new();	
 		rec_t__PDCM_PER__ t__PDCM_PER__ = new();	
 		rec_t__PDCM_START__ t__PDCM_START__ = new();	
 		rec_t__PDCM_END__ t__PDCM_END__ = new();	
 		rec_t__response_IPS__ t__response_IPS__ = new();	
 		rec_t__Disc_dly_8__ t__Disc_dly_8__ = new();	
 		rec_t__Disc_dly_16__ t__Disc_dly_16__ = new();	
 		rec_t__Disc_dly_32__ t__Disc_dly_32__ = new();	
 		rec_t__Disc_ramp__ t__Disc_ramp__ = new();	
 		rec_t__Disc_width__ t__Disc_width__ = new();	
 		rec_f__SPI__ f__SPI__ = new();	
 		rec_f__SPI_LV__ f__SPI_LV__ = new();	
 		rec_t__csdisle__ t__csdisle__ = new();	
 		rec_t__csdisla__ t__csdisla__ = new();	
 		rec_t__csenle__ t__csenle__ = new();	
 		rec_t__csenla__ t__csenla__ = new();	
 		rec_t__shi__ t__shi__ = new();	
 		rec_t__slo__ t__slo__ = new();	
 		rec_t__smds__ t__smds__ = new();	
 		rec_t__smdh__ t__smdh__ = new();	
 		rec_t__cwof__ t__cwof__ = new();	
 		rec_t__iwg__ t__iwg__ = new();	
 		rec_t__SYNCB_pw__ t__SYNCB_pw__ = new();	
 		rec_f__CLKREF__ f__CLKREF__ = new();	
 		rec_f__CLK_REF_ROC__ f__CLK_REF_ROC__ = new();	
 		rec_D__CLKREF__ D__CLKREF__ = new();	
 	
		function new();
			// nothing to do here
		endfunction
 	endclass 	
 	
 	class edf_parameter_model;
 		edf_epms epms;
 		edf_max_ratings max_ratings;
 		edf_recommended_parameters recommended;
 		
		function new();
			epms = new();
			max_ratings = new();
			recommended = new();
		endfunction
 	endclass

endpackage	

`endif // EDF_EPM_MODEL_PKG_SV