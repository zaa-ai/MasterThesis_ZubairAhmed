`define PAD_INST(_name_, _oe_, _out_, _pd_, _pu_, _ie_) assign  _name_.oe = _oe_ ; \
assign  _name_.out = _out_ ; \
assign  _name_.pd  = _pd_ ; \
assign  _name_.pu  = _pu_ ; \
assign  _name_.ie  = _ie_ ;
