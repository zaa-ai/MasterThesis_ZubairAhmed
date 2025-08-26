/*------------------------------------------------------------------------------
 * Copyright (c) 2023 Elmos SE
 * File          : in_order_buffer_comparator.sv
 * Author        : jvoi
 * Creation date : 2023-06-01
 * Description   : Compares two buffer transactions
 *------------------------------------------------------------------------------*/
class in_order_buffer_comparator extends uvm_component;
    `uvm_component_utils(in_order_buffer_comparator)
    
    // Port: before_export
    //
    // The export to which one stream of data is written. The port must be
    // connected to an analysis port that will provide such data. 
    
    uvm_analysis_export #(buffer_writer_tr) before_export;
    
    
    // Port: after_export
    //
    // The export to which the other stream of data is written. The port must be
    // connected to an analysis port that will provide such data. 
    
    uvm_analysis_export #(buffer_writer_tr) after_export;
    
    
    // Port: pair_ap
    //
    // The comparator sends out pairs of transactions across this analysis port.
    // Both matched and unmatched pairs are published via a pair_type objects.
    // Any connected analysis export(s) will receive these transaction pairs.
    
    uvm_analysis_port   #(uvm_class_pair #( buffer_writer_tr, buffer_writer_tr )) pair_ap;
    
    protected   uvm_tlm_analysis_fifo #(buffer_writer_tr) m_before_fifo;
    protected   uvm_tlm_analysis_fifo #(buffer_writer_tr) m_after_fifo;
    
    int m_matches, m_mismatches;
    
    function new(string name, uvm_component parent);
        
        super.new(name, parent);
        
        before_export = new("before_export", this);
        after_export  = new("after_export", this);
        pair_ap       = new("pair_ap", this);
        
        m_before_fifo = new("before", this);
        m_after_fifo  = new("after", this);
        m_matches = 0;
        m_mismatches = 0;
        
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        before_export.connect(m_before_fifo.analysis_export);
        after_export.connect(m_after_fifo.analysis_export);
    endfunction
    
    // Task- run_phase
    //
    // Internal method.
    //
    // Takes pairs of before and after transactions and compares them. 
    // Status information is updated according to the results of the comparison.
    // Each pair is published to the pair_ap analysis port.
    
    virtual task run_phase(uvm_phase phase);
        
        uvm_class_pair #( buffer_writer_tr, buffer_writer_tr ) pair;
        buffer_writer_tr b;
        buffer_writer_tr a;
        
        string s;
        super.run_phase(phase); 
        forever begin
            
            m_before_fifo.get(b);
            m_after_fifo.get(a);
            
            if(!uvm_class_comp #( buffer_writer_tr )::comp(b, a)) begin
                
                $sformat(s, "%s differs from %s", uvm_class_converter #( buffer_writer_tr )::convert2string(a),
                        uvm_class_converter #( buffer_writer_tr )::convert2string(b));
                
                uvm_report_warning("Comparator Mismatch", s);
                
                m_mismatches++;
                
            end
            else begin
                s = uvm_class_converter #( buffer_writer_tr )::convert2string(b);
                uvm_report_info("Comparator Match", s);
                m_matches++;
            end
            
            // we make the assumption here that a transaction "sent for
            // analysis" is safe from being edited by another process.
            // Hence, it is safe not to clone a and b.
            
            pair = new("after/before");
            pair.first = a;
            pair.second = b;
            pair_ap.write(pair);
        end
        
    endtask
    
    
    // Function: flush
    //
    // This method sets m_matches and m_mismatches back to zero. The
    // <uvm_tlm_fifo#(T)::flush> takes care of flushing the FIFOs.
    
    virtual function void flush();
        m_matches = 0;
        m_mismatches = 0;
        m_before_fifo.flush();
        m_after_fifo.flush();
    endfunction
    
    virtual function bit is_empty();
        if (m_after_fifo.is_empty() == 1'b0) return 1'b0;
        if (m_before_fifo.is_empty() == 1'b0) return 1'b0;
        return 1'b1;
    endfunction
    
    virtual function int check_for_empty();
        if(is_empty == 1'b0) begin
            `uvm_error(this.get_type_name(), $sformatf("fifos of comparator are not empty. expected input :%1d , from buffer agent:%1d", m_before_fifo.used(), m_after_fifo.used()))
            return 1'b0;
        end
        return 1'b1;
    endfunction
    
endclass