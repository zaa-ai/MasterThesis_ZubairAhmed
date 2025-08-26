
  //==========================================================================
  // calculates bitwidth of a given number
  // special case: number 0 returns 1 !
  //==========================================================================

  function automatic integer num2width;
    // 0, 1       => 1
    // 2, 3       => 2
    // 4, 5, 6, 7 => 3
    // 8, ..., 15 => 4
    // and so on ...
    input integer num;
    integer number;
    integer result;
  begin
    result = 1;
    number = num >> 1;
    while (number) begin
      result = result + 1;
      number = number >> 1;
    end
    num2width = result;
  end
  endfunction

  //==========================================================================
  // calculates address offset of a given data width
  //==========================================================================

  function automatic integer addr_offset;
    input integer data_width;
    integer bytes;
    // bytes 0, 1       => offset = 0
    // bytes 2, 3       => offset = 1
    // bytes 4, 5, 6, 7 => offset = 2
    // bytes 8, ..., 15 => offset = 3
    // and so on ...
  begin
    bytes  = data_width / 8;
    addr_offset = num2width(bytes) - 1;
  end
  endfunction

  //==========================================================================
  // calculates address width of a given memory depth and data width
  // addr_width = address_bits(depth) + address_offset(data_width)
  //==========================================================================

  function automatic integer addr_width;
    input integer depth;
    input integer data_width;
  begin
    addr_width = num2width(depth - 1) + addr_offset(data_width);
  end
  endfunction

  //==========================================================================
  // returns minimum value
  //==========================================================================

  function automatic integer min;
    input integer a;
    input integer b;
  begin
    if (a < b) min = a;
    else       min = b;
  end
  endfunction

  //==========================================================================
  // returns maximum value
  //==========================================================================

  function automatic integer max;
    input integer a;
    input integer b;
  begin
    if (a < b) max = b;
    else       max = a;
  end
  endfunction

  //==========================================================================
  // returns number of '1' bits in vector slice [b-1:0]  (returns 0 if b <= 0)
  //==========================================================================

  function automatic [4:0] count_ones_16;
    input  [15:0] a;
    input integer b;
    integer n;
  begin
    count_ones_16 = 5'b0;
    for (n = 0; n < b; n++) begin
      if (a[n]) begin
        count_ones_16 = count_ones_16 + 5'b1;
      end
    end
  end
  endfunction

  //==========================================================================
  // calculates number of needed "Hamming distance 4" ECC bits
  //==========================================================================

  function automatic integer hd4_ecc_width;
    input integer data_width;
    integer n;
    //
    //  /n\          n!
    // |   | = ------------- = n = num of checkbits
    //  \1/     1! * (n-1)!
    //
    //  i <= n
    //  ------
    //  \      /n\
    //   >    |   | = (2^n)/2 = 2^(n-1) = (num of databits + num of checkbits)
    //  /      \i/
    //  ------
    //  i = 1
    //  i = odd
    //
    //  =>  max num of databits[num of checkbits] =
    //         (num of databits + num of checkbits) - num of checkbits = 2^(n-1) - n
    //
    // data_width  =   1 => ecc_width = 3 ... else:
    // data_width <=   4 => ecc_width = 4 ... else:
    // data_width <=  11 => ecc_width = 5 ... else:
    // data_width <=  26 => ecc_width = 6 ... else:
    // data_width <=  57 => ecc_width = 7 ... else:
    // data_width <= 120 => ecc_width = 8 ... else:
    // and so on ...
  begin
    n = 3;
    while ((2**(n-1))-n < data_width) begin
      n++;
    end
    hd4_ecc_width = n;
  end
  endfunction

