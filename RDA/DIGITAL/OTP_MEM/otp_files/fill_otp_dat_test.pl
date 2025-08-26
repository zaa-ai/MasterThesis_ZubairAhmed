#!/usr/bin/perl -w

use Math::Trig ':pi';
use POSIX;

my $position = 0; # current position within otp.dat file

my $wave_count = 72;
my $max = pow(2, 5) - 1; # maximum waveshape value

print_hex(0x00);
print_hex(0x11);
insert_random(2);
print_hex(0x00);
print_hex(0x12);
insert_random(2);

### check data 0
print_hex(0xAF);
print_hex(0xFE);
print_hex(0x00);
print_hex(0x00);

### check data address high and data previous word 0
print_hex(0x00);
print_hex(0xBE);
print_hex(0xEF);
print_hex(0x00);

### check data address low and data high 0
print_hex(0xD0);
print_hex(0x00);
print_hex(0x00);
print_hex(0x0F);

### check data address low and data high 0
print_hex(0xD0);
print_hex(0x00);
print_hex(0x00);
print_hex(0x0F);

insert_random(4*100);


insert_zero_up_to(4096);

# --------------------------------------------

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
   	for(my $index = 0; $index < $wave_count; $index++) {
   		if($index > $wave_count/2) {
   			print_hex(0);
   		} else {
   			print_hex($max * cos(pi/$wave_count * $index));
   		}
   	}
}

sub insert_wave_rise {
   	for(my $index = 0; $index < $wave_count; $index++) {
   		if($index > $wave_count/2) {
   			print_hex($max);
   		} else {
   			print_hex($max - ($max * cos(pi/$wave_count * $index)));
   		}
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
