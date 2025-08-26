#!/usr/bin/perl -w

use Math::Trig ':pi';
use POSIX;

my $position = 0; # current position within otp.dat file

my $wave_count = 72;
my $max = pow(2, 5) - 1; # maximum waveshape value

#####   ID   #####
print_address_and_data(0x0001 , random_data()); # ID LOW
print_address_and_data(0x0002 , random_data()); # ID HIGH

#####   IREF   #####
print_address_and_data(0x0003 , 0x0002); # TRIM_IREF

#####   OSC   #####
print_address_and_data(0x0006 , 0x004B); # TRIM_OSC
print_address_and_data(0x0007 , 0x0003); # TRIM_OSC_TCF

#####   DSI0   #####
#print_address_and_data(0x8204 , 0x00A1); # TRIM_DSI0_REC_FALL
#print_address_and_data(0x8208 , 0x00A2); # TRIM_DSI0_REC_RISE
#print_address_and_data(0x8210 , 0x00A3); # TRIM_DSI0_TR

#####   DSI1   #####
#print_address_and_data(0x8244 , 0x00B1); # TRIM_DSI1_REC_FALL
#print_address_and_data(0x8248 , 0x00B2); # TRIM_DSI1_REC_RISE
#print_address_and_data(0x8250 , 0x00B3); # TRIM_DSI1_TR
 
#####   DSI2   #####
#print_address_and_data(0x8284 , 0x00C1); # TRIM_DSI2_REC_FALL
#print_address_and_data(0x8288 , 0x00C2); # TRIM_DSI2_REC_RISE
#print_address_and_data(0x8290 , 0x00C3); # TRIM_DSI2_TR
 
#print_word(0x0000);

#####   DSI3   #####
#print_address_and_data(0x82C4 , 0x00D1); # TRIM_DSI3_REC_FALL
#print_address_and_data(0x82C8 , 0x00D2); # TRIM_DSI3_REC_RISE
#print_address_and_data(0x82D0 , 0x00D3); # TRIM_DSI3_TR
 
#####   OT   #####
#print_address_and_data(0x8080 , 0x0003); # TRIM_OT

#####   CLDO   #####
#print_address_and_data(0x8020 , 0x0005); # CLDO_TRIM

print_address_and_data(0x0000 , random_data()); # END

#print_hex(0xA5);  # Cookie for usage of wave shapes for 1st stored in OTP
#insert_wave_fall(0x400);
#insert_wave_rise(0x448);
#
#insert_zero_up_to(0x200);
#
#print_hex(0xA5);  # Cookie for TDMA scheme
#for(my $channel = 0; $channel < 2; $channel++) {
#	
#	print_msb_lsb_hex(1000); 	# PDCM period
#	print_hex(0);				# BP flag
#	print_hex(16);				# packet count
#	
#	for(my $k = 0; $k < 16; $k++) {
#		print_msb_lsb_hex($k*10);		# earliest start time
#		print_msb_lsb_hex($k*10+10);	# latest start time
#		print_hex(2 << 6);				# source ID
#		print_hex(8);					# symbol count
#	}
#}

 insert_zero_up_to(4096);
# fill_file_full(4096);
# --------------------------------------------

sub random_data {
	my $value = rand(65535);
	return ($value & 0xFFFF)
}

sub insert_random {
	my ($count) = @_;
    my $index;
   	for($index = 0; $index < $count; $index++) {
   		print_hex(rand(4096));
   	}
}

# inserts 0x00 until given target position within otp.dat file is reached
sub insert_zero_up_to {
	my ($target_position) = @_;
    my $index;
   	for($index = $position; $index < $target_position; $index++) {
   		print_hex(0);
   	}
}

sub insert_wave_fall {
	my ($start_address) = @_;
	my $data;
	
   	for(my $index = 0; $index < $wave_count; $index++) {
   		
   		print_word($start_address);
        $start_address++;
        
   		if($index > $wave_count/2) {
   			$data = 0;
   		} else {
   			$data = $max * cos(pi/$wave_count * $index);
   		}
   		print_word($data);
   	}
}

sub insert_wave_rise {
	my ($start_address) = @_;
    my $data;
    
   	for(my $index = 0; $index < $wave_count; $index++) { 
   		       
        print_word($start_address);
        $start_address++;
        
   		if($index > $wave_count/2) {
   			$data = 0;
   		} else {
   			$data = $max - ($max * cos(pi/$wave_count * $index));
   		}
   		print_word($data);
   	}
}

sub fill_file_full {
	my ($target_position) = @_;
    my $data;
    
    while($position < $target_position){
        print_word(0x0011);
        $data = random_data();
        print_word($data);
    }
}

sub print_msb_lsb_hex{
	my ($value) = @_;
	$value = $value & 0xFFFF;
	
	my $msb = ($value >> 8) & 0xFF;
	my $lsb = $value & 0xFF;
	
	print_hex($msb);
	print_hex($lsb);
	#print "-> MSB $msb, LSB $lsb \n";
}

sub print_hex{
	my ($value) = @_;
	$value = $value & 0xFF;
	
	my @bits = get_bits($value, 8);
	
	my $parity = 0;
	$parity += 8 * ($bits[4] ^ $bits[5] ^ $bits[6] ^ $bits[7]);
	$parity += 4 * ($bits[1] ^ $bits[2] ^ $bits[3] ^ $bits[7]);
	$parity += 2 * ($bits[0] ^ $bits[2] ^ $bits[3] ^ $bits[5] ^ $bits[6]);
	$parity += 1 * ($bits[0] ^ $bits[1] ^ $bits[3] ^ $bits[4] ^ $bits[6]);
	$value = 256 * $parity + $value;
	
	printf "%03x\n", int($value);
	$position++;
}

#usage print_data(0x0011 , 0x0815)
sub print_address_and_data{
	my ($address, $value) = @_;
	
#	printf "address=%08x\n" ,int($address);
#	printf "  data=%08x\n", int($value);
	
	print_word($address);
	print_word($value);
}

sub print_word{
	my ($value) = @_;
	my $otp_address_value = (($position & 0x0000FFFF) << 16) + ($value & 0x0000FFFF); 
	my @bits = get_bits($otp_address_value, 28);
	my $ecc_high = 0;
	my $ecc_low = 0;
	$ecc_low  +=   1 * (     $bits[ 1] ^ $bits[ 2] ^ $bits[ 3] ^ $bits[ 5] ^ $bits[ 8] ^ $bits[ 9] ^ $bits[11] ^ $bits[14] ^ $bits[17] ^ $bits[18] ^ $bits[19] ^ $bits[21] ^ $bits[24] ^ $bits[25] ^ $bits[27]); 
	$ecc_low  +=   2 * (     $bits[ 0] ^ $bits[ 1] ^ $bits[ 2] ^ $bits[ 4] ^ $bits[ 6] ^ $bits[ 8] ^ $bits[10] ^ $bits[12] ^ $bits[16] ^ $bits[17] ^ $bits[18] ^ $bits[20] ^ $bits[22] ^ $bits[24] ^ $bits[26]); 
	$ecc_low  +=   4 * ( 1 ^ $bits[ 0] ^ $bits[ 3] ^ $bits[ 4] ^ $bits[ 7] ^ $bits[ 9] ^ $bits[10] ^ $bits[13] ^ $bits[15] ^ $bits[16] ^ $bits[19] ^ $bits[20] ^ $bits[23] ^ $bits[25] ^ $bits[26]); 
	$ecc_low  +=   8 * ( 1 ^ $bits[ 0] ^ $bits[ 1] ^ $bits[ 5] ^ $bits[ 6] ^ $bits[ 7] ^ $bits[11] ^ $bits[12] ^ $bits[13] ^ $bits[16] ^ $bits[17] ^ $bits[21] ^ $bits[22] ^ $bits[23] ^ $bits[27]); 
	$ecc_high +=   1 * (     $bits[ 2] ^ $bits[ 3] ^ $bits[ 4] ^ $bits[ 5] ^ $bits[ 6] ^ $bits[ 7] ^ $bits[14] ^ $bits[15] ^ $bits[18] ^ $bits[19] ^ $bits[20] ^ $bits[21] ^ $bits[22] ^ $bits[23]); 
	$ecc_high +=   2 * (     $bits[ 8] ^ $bits[ 9] ^ $bits[10] ^ $bits[11] ^ $bits[12] ^ $bits[13] ^ $bits[14] ^ $bits[15] ^ $bits[24] ^ $bits[25] ^ $bits[26] ^ $bits[27]); 
	$ecc_high +=   4 * (     $bits[ 0] ^ $bits[ 1] ^ $bits[ 2] ^ $bits[ 3] ^ $bits[ 4] ^ $bits[ 5] ^ $bits[ 6] ^ $bits[ 7] ^ $bits[24] ^ $bits[25] ^ $bits[26] ^ $bits[27]); 
	$ecc_high +=   8 * (     $bits[ 0] ^ $bits[ 1] ^ $bits[ 2] ^ $bits[ 3] ^ $bits[ 4] ^ $bits[ 5] ^ $bits[ 6] ^ $bits[ 7] ^ $bits[24] ^ $bits[25] ^ $bits[26] ^ $bits[27]);
	
#	printf "otp_address_value=%12x\n" ,int($otp_address_value);
#	printf "ecc_high=%08x\n", int($ecc_high);
#	printf "ecc_low=%08x\n", int($ecc_low);
	
	my $value_low  = ($value & 0x00FF); 
	my $value_high = ($value & 0xFFFF) >> 8;
	
	my $otp_word_low  = ($ecc_low  << 8) + $value_low; 
	my $otp_word_high = ($ecc_high << 8) + $value_high; 
	
	printf "%03x\n", int($otp_word_high);
	$position++;
	printf "%03x\n", int($otp_word_low);
	$position++;
	
}


sub get_bits {
  my ($value, $size) = @_;
  my @bits = ();
  for (my $bit_count = 0; $bit_count < $size; $bit_count++) {
    push @bits, ($value & 1) ? 1 : 0;
    $value /= 2;
  }
  return @bits;
}

exit 0;
