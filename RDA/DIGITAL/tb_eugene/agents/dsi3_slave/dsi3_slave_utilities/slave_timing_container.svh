typedef enum {RANDOM_VALUE, NEXT_VALUE, CYCLIC_VALUE} slave_timing_iterator_mode;
typedef struct {int kramp; int data_set;} slave_timing_selector;

/**
 * Class: timing_iterator
 *
 * Class used to walk through all timings located in a timing container
 */
virtual class timing_iterator;
	protected slave_timing_iterator_mode mode;
	
	/**
	 * Function: has_next
	 * 
	 * Returns true, if there exists a next timing object
	 * It is always true if in RANDOM_VALUE mode or in CYCLIC_VALUE mode
	 * 
	 * Returns:
	 *   bit
	 */
	pure virtual function bit has_next();
	/**
	 * Function: next
	 * 
	 * Returns the next timing object
	 * 
	 * Returns:
	 *   slave_rxd_timing
	 */
	pure virtual function slave_rxd_timing next();
	/**
	 * Function: current
	 * 
	 * Returns the current timing object
	 * 
	 * Returns:
	 *   slave_rxd_timing
	 */
	pure virtual function slave_rxd_timing current();
	/**
	 * Function: current_selector
	 * 
	 * Returns the current selector
	 * 
	 * Returns:
	 *   slave_rxd_timing
	 */
	pure virtual function slave_timing_selector current_selector();
	/**
	 * Function: restart
	 * 
	 * Restarts iterator
	 * 
	 * Returns:
	 *   void
	 */
	pure virtual function void restart();
	/**
	 * Function: set_mode
	 * 
	 * Sets the mode of the iterator (e.g. RANDOM_VALUE, NEXT_VALUE or CYCLIC_VALUE)
	 * 
	 * Parameters:
	 * - slave_timing_iterator_mode mode 
	 * 
	 * Returns:
	 *   void
	 */
	pure virtual function void set_mode(slave_timing_iterator_mode mode);
	/**
	 * Function: get_table_string
	 * 
	 * Returns a String containing all values of the current selection for usage in a table

	 * Returns:
	 *   string
	 */
	pure virtual function string get_table_string();
	/**
	 * Function: get_table_header
	 * 
	 * Returns a *string* for a table header. Use get_table_string() to get the row information
	 * 
	 * Returns:
	 *   string
	 */
	pure virtual function string get_table_header();
endclass

typedef timing_iterator_impl;
/**
 * Class: timing_container
 *
 * Interface for a container containing timing information 
 */
virtual class timing_container;
	protected timing_iterator iterator;
	/**
	 * Function: get_iterator
	 * 
	 * Returns a iterator for walking through the timing objects
	 * 
	 * Parameters:
	 * 
	 * Returns:
	 *   timing_iterator
	 */
	pure virtual function timing_iterator get_iterator();
	
endclass

/**
 * Class: slave_timing_container
 * 
 * contains all DSI3 timings of the receiver (rxd1, rxd2) when changing the chip value
 */
class slave_timing_container #(parameter int kramp=1, parameter int data_sets=1) extends timing_container;
	
	slave_rxd_timing slave_timing[kramp][data_sets];
	
	function new();
		foreach (slave_timing[i,j])
			slave_timing[i][j] = new();
	endfunction
	
	/**
	 * Function: get_iterator
	 * 
	 * Returns an iterator for the timing objects
	 * 
	 * Returns:
	 *   timing_iterator
	 */	
	virtual function timing_iterator get_iterator();
		if (iterator == null) begin
			timing_iterator_impl#(.kramp(kramp), .data_sets(data_sets)) temp_iterator;
			temp_iterator = new(this);
			iterator = temp_iterator;
		end
		return iterator;
	endfunction
	
endclass


/**
 * Class: default_slave_timing_container
 *
 * Default timing container containing one single timing (default_slave_rxd_timing)
 */
class default_slave_timing_container extends slave_timing_container#(1,1);
	
	function new();
		default_slave_rxd_timing temp = new();
		slave_timing[0][0] = temp;
	endfunction
	
endclass

/**
 * Class: default_slave_timing_container
 *
 * Timing container containing one single timing (no_slave_rxd_timing)
 */
class no_slave_timing_container extends slave_timing_container#(1,1);
	
	function new();
		no_slave_timing temp = new();
		slave_timing[0][0] = temp;
	endfunction
	
endclass

/**
 * Class: timing_iterator_impl
 *
 * Implementation for the timing_iterator 'interface'
 */
class timing_iterator_impl#(parameter int kramp=1, parameter int data_sets=1) extends timing_iterator;
	
	protected slave_timing_container#(kramp, data_sets) timings;
	protected slave_timing_selector select_timing;
	
	function new(slave_timing_container#(kramp, data_sets) slave_timings);
		this.timings = slave_timings;
		initialize();
	endfunction
	
	/**
	 * Function: has_next
	 * 
	 * Returns true, if there exists a next timing object
	 * 
	 * Returns:
	 *   bit
	 */
	virtual function bit has_next();
		case (mode)
			NEXT_VALUE: begin
				slave_timing_selector next_select = next_selector();
				return is_selector_valid(next_select);
			end
			RANDOM_VALUE, CYCLIC_VALUE : return 1;
		endcase
	endfunction
	
	protected function is_selector_valid(slave_timing_selector selector);
		if (selector.kramp < kramp) begin
			return 1;
		end 
		else begin
			return 0;
		end		
	endfunction
	
	/**
	 * Function: next
	 * 
	 * Returns the next timing object
	 * 
	 * Returns:
	 *   slave_rxd_timing
	 */
	virtual function slave_rxd_timing next();
		case (mode)
			NEXT_VALUE, CYCLIC_VALUE: begin
				slave_timing_selector next_select = next_selector();
				select_timing = next_select;
			end
			RANDOM_VALUE: begin
				int kramp_value = $urandom_range($high(timings.slave_timing, 1), $low(timings.slave_timing, 1));
				int data_set_value = $urandom_range($high(timings.slave_timing, 2), $low(timings.slave_timing, 2));
				select_timing.kramp = kramp_value;
				select_timing.data_set = data_set_value;
			end
			CYCLIC_VALUE: begin
				slave_timing_selector next_select = next_selector();
				if (is_selector_valid(next_select)) begin
					select_timing = next_select;
				end
				else begin
					initialize();
					select_timing.data_set++;
				end
			end
		endcase
		return get_current();
	endfunction
	
	/**
	 * Function: current
	 * 
	 * Returns the current timing object
	 * 
	 * Returns:
	 *   slave_rxd_timing
	 */
	virtual function slave_rxd_timing current();
		return get_current();
	endfunction
	
	/**
	 * Function: current_selector
	 * 
	 * Returns the current timing selector structure
	 * 
	 * Returns:
	 *   slave_timing_selector
	 */
	virtual function slave_timing_selector current_selector();
		return select_timing;
	endfunction
		
	/**
	 * Function: restart
	 * 
	 * Restarts the iterator
	 */
	virtual function void restart();
		initialize();
	endfunction
	
	protected virtual function slave_timing_selector next_selector();
		slave_timing_selector temp = select_timing;
		if (temp.data_set < (data_sets-1)) begin
			temp.data_set++;
		end
		else begin
			temp.data_set = 0;
			temp.kramp++;
		end
		return temp;
	endfunction
	
	protected virtual function initialize();
		select_timing.kramp = 0;
		select_timing.data_set = -1;
	endfunction
	
	/**
	 * Function: set_mode
	 * 
	 * Sets the mode of the iterator (e.g. RANDOM_VALUE, NEXT_VALUE or CYCLIC_VALUE)
	 * 
	 * Parameters:
	 * - slave_timing_iterator_mode mode 
	 * 
	 * Returns:
	 *   void
	 */
	virtual function void set_mode(slave_timing_iterator_mode mode);
		this.mode = mode;
	endfunction
	/**
	 * Function: get_table_header
	 * 
	 * Returns a *string* for a table header. Use get_table_string() to get the row information
	 * 
	 * Returns:
	 *   string
	 */	
	virtual function string get_table_header();
		return $sformatf("kramp | data_set | %s", timings.slave_timing[0][0].get_table_header());
	endfunction
	/**
	 * Function: get_table_string
	 * 
	 * Returns a String containing all values of the current selection for usage in a table

	 * Returns:
	 *   string
	 */	
	virtual function string get_table_string();
		string s = $sformatf("   %2d |     %3d  | %s", select_timing.kramp, select_timing.data_set, get_current().get_table_string());
		return s;
	endfunction
	
	protected function slave_rxd_timing get_current();
		return timings.slave_timing[select_timing.kramp][select_timing.data_set];
	endfunction
endclass