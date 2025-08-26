
// ELMOS 523.99A FLASH CRC : 2 x (16 + 6) = 44

#include <stdio.h>
#include <string.h>


// |43|42|41|40|39|38|37|36|35|34|33|32|31|30|29|..|18|17|16|15|14|13|..| 2| 1| 0|
// +-----------------+-----------------+--------------------+--------------------+
// |                 |                 |                    |                    |
// |  H CRC (6 bit)  |  L CRC (6 bit)  |  H DATA  (16 bit)  |  L DATA  (16 bit)  |
// |                 |                 |                    |                    |
// +-----------------+-----------------+--------------------+--------------------+


typedef  unsigned long  data_crc_t;  // type size: min 16 + 6 bit -> 32 bit

data_crc_t calc_flash_crc(data_crc_t n) { 

	data_crc_t crc;
    data_crc_t shiftreg, i;

    shiftreg = (~n) & 0xFFFF;
    for (i = 0; i < 16; i++) {
        if (shiftreg & (((data_crc_t)1) << (16 - 1))) {
            shiftreg ^= (((data_crc_t)0x5F) << (16 - (6 + 1)));
        }
        shiftreg <<= 1;
    }
    crc = (shiftreg >> (16 - 6));
	return (~crc) & 0x3F;
}


typedef  unsigned short      data16_t;
typedef  unsigned long long  data44_t;


int main(int argc, char *argv[]) {

	int n, k, words44;
	data16_t data16[256];
	data44_t data44[128];

	data16_t cal_data     = 0x4433;  // calibration data word
	data16_t sys_osc_freq = 24000;   // calibrated system osc frequency value [kHz]

	memset(data16, 0xFF, sizeof(data16));
	memset(data44, 0xFF, sizeof(data44));

	n = 0;
	/* content >>>> */
	data16[n++] = cal_data;
	data16[n++] = sys_osc_freq;
	data16[n++] = 0x354d;
	data16[n++] = 0x3332;
	data16[n++] = 0x3939;
	data16[n++] = 0x0041;
	data16[n++] = 0xffff;
	data16[n++] = 0xffff;
	data16[n++] = 0x4031;
	data16[n++] = 0x2000;
	data16[n++] = 0x4034;
	data16[n++] = 0xff80;
	data16[n++] = 0x44b2;
	data16[n++] = 0x018e;
	data16[n++] = 0x4034;
	data16[n++] = 0xff84;
	data16[n++] = 0x44b2;
	data16[n++] = 0x0190;
	data16[n++] = 0x44b2;
	data16[n++] = 0x0192;
	data16[n++] = 0x44b2;
	data16[n++] = 0x0194;
	data16[n++] = 0x44b2;
	data16[n++] = 0x0196;
	data16[n++] = 0x4034;
	data16[n++] = 0xff8c;
	data16[n++] = 0x44b2;
	data16[n++] = 0x0198;
	data16[n++] = 0x4392;
	data16[n++] = 0x018c;
	data16[n++] = 0x9392;
	data16[n++] = 0x018a;
	data16[n++] = 0x2009;
	data16[n++] = 0x4035;
	data16[n++] = 0xfffc;
	data16[n++] = 0x1290;
	data16[n++] = 0x001e;
	data16[n++] = 0xd0b2;
	data16[n++] = 0x0100;
	data16[n++] = 0x0188;
	data16[n++] = 0x43a2;
	data16[n++] = 0x018a;
	data16[n++] = 0x4035;
	data16[n++] = 0xfffa;
	data16[n++] = 0x1290;
	data16[n++] = 0x000c;
	data16[n++] = 0x4304;
	data16[n++] = 0x4305;
	data16[n++] = 0x4031;
	data16[n++] = 0x003e;
	data16[n++] = 0x4130;
	data16[n++] = 0x4524;
	data16[n++] = 0xc034;
	data16[n++] = 0x03fe;
	data16[n++] = 0x9034;
	data16[n++] = 0xfc00;
	data16[n++] = 0x2001;
	data16[n++] = 0x12a5;
	data16[n++] = 0x4130;
	data16[n++] = 0xffff;
	data16[n++] = 0xffff;
	data16[n++] = 0xffff;
	data16[n++] = 0xffff;
	data16[n++] = 0xff90;
	/* <<<< content */

	words44 = (n+1)/2;

	n = 0;
	for (k = 0; k < words44; k++) {
		data44[k] = 
			(((data44_t)calc_flash_crc(data16[n+1])) << 38) +
			(((data44_t)calc_flash_crc(data16[n  ])) << 32) +
			(((data44_t)               data16[n+1] ) << 16) +
			(((data44_t)               data16[n  ] )      ) ;
		n += 2;
	}

	// NOW: write words44 "words" of data44 to FLASH and verify (dyn)
	for (k = 0; k < words44; k++) {
		printf("0x%011llx\n", data44[k]);
	}

	return 1;
}


