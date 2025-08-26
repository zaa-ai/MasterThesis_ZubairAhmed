
==========================================================================
polynomial reversal
==========================================================================

starting point: Koopman notation polynomial without bit 0 term, which is always 1
reversed polynomial is needed for the "bitwise right-shift CRC algorithm" variant

example:
polynomial 0xA6 => 1010.0110.1 (including bit 0 which is 1) => 1.0100.1101 = 0x14D
=> reversed 1.0110.0101 = 0x165 => 1011.0010.1 => 0xB2 (LSB skipped)

8 bit poly 0xA6 => 0xB2 (HD3 for up to 247 bit, HD2 for 2048+ bits)
8 bit poly 0x97 => 0xF4 (HD4 for up to 119 bit, HD2 for 2048+ bits)
6 bit poly 0x2C => 0x26 (HD4 for up to  25 bit)
5 bit poly 0x12 => 0x14 (HD3 for up to  26 bit)

==========================================================================
bitwise right-shift CRC algorithm (variant)
==========================================================================

crc_sum = input_CRC_sum

for (i = 0; i < num_bits(data); i++) {
  if (lsb(data) ^ lsb(crc_sum)) {
    crc_sum = (crc_sum >> 1) ^ (revpoly);
  } else {
    crc_sum = (crc_sum >> 1);
  }
  data >>= 1;
}

output_CRC_sum = crc_sum

==========================================================================
bitwise left-shift CRC algorithm (variant)
==========================================================================

poly = Koopman notation polynomial WITH bit 0 term appended, which is always 1
polynomial from table 0x5B => 101.1011.1 (including bit 0 which is 1) = 1011.0111 = 0xB7

Koopman table poly 0x5B => 0xB7 (HD4 for 32 bit (up to 56 bit) data using 7 bit ECC)


shiftreg = (data << num_bits(crc_sum)) + input_CRC_sum;

for (i = 0; i < num_bits(data); i++) {
  if (msb(shiftreg)) {
    shiftreg = (shiftreg << 1) ^ (poly << num_bits(data));
  } else {
    shiftreg = (shiftreg << 1);
  }
}

output_CRC_sum = (shiftreg >> num_bits(data));

--------------------------------------------
which is equivalent to the code used in HDL:
--------------------------------------------

shiftreg = (data << num_bits(crc_sum)) + input_CRC_sum;

for (i = 0; i < num_bits(data); i++) {
  if (msb(shiftreg)) {
    shiftreg = shiftreg ^ (poly << (num_bits(data) - 1));
  }
  shiftreg = shiftreg << 1;
}

output_CRC_sum = (shiftreg >> num_bits(data));

==========================================================================

Both (right- and left-shift) variants result in the same Min Hamming Distance (MHD) !

