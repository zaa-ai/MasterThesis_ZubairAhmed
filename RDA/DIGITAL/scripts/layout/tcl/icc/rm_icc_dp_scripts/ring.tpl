template : ring_m2v_m3h(wv,wh,s,ov,oh) {
  side : horizontal {
    layer : MET3
    width : @wh
    spacing : @s
    offset : @oh
  }
  side : vertical {
    layer : MET2
    width : @wv
    spacing : @s
    offset : @ov
  }
}

template : ring_m4v_m5h(wv,wh,s,ov,oh) {
  side : horizontal {
    layer : MET5
    width : @wh
    spacing : @s
    offset : @oh
  }
  side : vertical {
    layer : MET4
    width : @wv
    spacing : @s
    offset : @ov
  }
}

template : ring_m5h_m5v(osh, osv) {
side : horizontal {
	layer : MET5
	width : 5.000000
	spacing : 2
	offset : @osh
	}
side : vertical {
	layer : MET5
	width : 5.000000
	spacing : 2
	offset : @osv
	}
}

template : ring_m5h_m4v(osh, osv, wh, wv) {
side : horizontal {
	layer : MET5
	width : @wh
	spacing : 2
	offset : @osh
	}
side : vertical {
	layer : MET4
	width : @wv
	spacing : 0.8
	offset : @osv
	}
}

#not used
template : ring_m3m4_vertical(wv,wh,s) {
  side : vertical {
    layer : MET3
    width : @wh
    spacing : @s
    offset : -4.0
  }
  side : horizontal {
    layer : MET4
    width : @wv
    spacing : @s
    offset : -20.0
  }
}
# VSUB ring
template : vsub_ring_horizontal {
 side : horizontal {
	layer : MET3
	width : 2
	spacing : minimum
	offset : -3
 }
 side : vertical {
	layer : MET4
	width : 2
	spacing : minimum
	offset : -3
 }
}
template : vsub_ring_vertical {
 side : vertical {
	layer : MET3
	width : 2
	spacing : minimum
	offset : -3
 }
 side : horizontal {
	layer : MET4
	width : 2
	spacing : minimum
	offset : -3
 }
}
# Block ring
template : block_ring_horizontal {
 side : horizontal {
	layer : MET3
	width : 2.4
	spacing : 0.64
	offset : 2.4
 }
 side : vertical {
	layer : MET2
	width : 2.4
	spacing : 0.64
	offset : 2.4
 }
}
template : block_ring_vertical {
 side : vertical {
	layer : MET3
	width : 2.4
	spacing : 0.64
	offset : 2.4
 }
 side : horizontal {
	layer : MET2
	width : 2.4
	spacing : 0.64
	offset : 2.4
 }
}
# Template for VCC from OTP Layout Guide
template : ip_vcc_ring {
	side : vertical {
		layer : MET4
		width : 15
		spacing : 0.64
		offset : 5
	}
 	side : horizontal {
		layer : MET5
		width : 15
		spacing : 0.64
		offset : 5
	}
}
