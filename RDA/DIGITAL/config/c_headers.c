#ifndef __m52144a_BF_H__
#define __m52144a_BF_H__


// Instance base addresses

#ifndef BASE_ADDR_Info 
#define BASE_ADDR_Info 0x0000U
#define SIZE_Info 0x0020U
#endif

// Register bit field definitions
	 
/* Info_IC_REVISION */

#define MSK_INFO_IC_REVISION_REVISION                                (0xffff)
#define SFT_INFO_IC_REVISION_REVISION                                (0)
#define LSB_INFO_IC_REVISION_REVISION                                (0)
#define MSB_INFO_IC_REVISION_REVISION                                (15)

typedef struct {
  unsigned short revision : 16;
} info_ic_revision_bf;
		
typedef union {
  unsigned short val;
  info_ic_revision_bf bf;
} info_ic_revision_t;


/* Info_CHIP_ID_LOW */

#define MSK_INFO_CHIP_ID_LOW_CHIP_ID_LOW                             (0xffff)
#define SFT_INFO_CHIP_ID_LOW_CHIP_ID_LOW                             (0)
#define LSB_INFO_CHIP_ID_LOW_CHIP_ID_LOW                             (0)
#define MSB_INFO_CHIP_ID_LOW_CHIP_ID_LOW                             (15)

typedef struct {
  unsigned short chip_id_low : 16;
} info_chip_id_low_bf;
		
typedef union {
  unsigned short val;
  info_chip_id_low_bf bf;
} info_chip_id_low_t;


/* Info_CHIP_ID_HIGH */

#define MSK_INFO_CHIP_ID_HIGH_CHIP_ID_HIGH                           (0xffff)
#define SFT_INFO_CHIP_ID_HIGH_CHIP_ID_HIGH                           (0)
#define LSB_INFO_CHIP_ID_HIGH_CHIP_ID_HIGH                           (0)
#define MSB_INFO_CHIP_ID_HIGH_CHIP_ID_HIGH                           (15)

typedef struct {
  unsigned short chip_id_high : 16;
} info_chip_id_high_bf;
		
typedef union {
  unsigned short val;
  info_chip_id_high_bf bf;
} info_chip_id_high_t;



typedef struct {
  info_ic_revision_t                                                 ic_revision;
  info_chip_id_low_t                                                 chip_id_low;
  info_chip_id_high_t                                                chip_id_high;
} info_t;

typedef union {
  unsigned short a[sizeof(info_t)/sizeof(unsigned short)];
  info_t s;
} info_u_t;


#define ADDR_INFO_IC_REVISION                                        (0x1FU)
#define A_INFO_IC_REVISION(ba)                                       ((ba) + ADDR_INFO_IC_REVISION)
#define R_INFO_IC_REVISION(ba)                                       (*(volatile unsigned short *)((unsigned int)A_INFO_IC_REVISION(ba)))
#define RES_INFO_IC_REVISION                                         (0x0001U)
#define MSB_INFO_IC_REVISION                                         (15)
#define LSB_INFO_IC_REVISION                                         (0)
#define VBMASK_INFO_IC_REVISION                                      (0xffffU)
#define ROMASK_INFO_IC_REVISION                                      (0xffffU)
#define AADDR_INFO_IC_REVISION                                       (BASE_ADDR_INFO + ADDR_INFO_IC_REVISION)
#define REG_INFO_IC_REVISION                                         (*(volatile unsigned short *)((unsigned int)AADDR_INFO_IC_REVISION))

#define ADDR_INFO_CHIP_ID_LOW                                        (0x1U)
#define A_INFO_CHIP_ID_LOW(ba)                                       ((ba) + ADDR_INFO_CHIP_ID_LOW)
#define R_INFO_CHIP_ID_LOW(ba)                                       (*(volatile unsigned short *)((unsigned int)A_INFO_CHIP_ID_LOW(ba)))
#define RES_INFO_CHIP_ID_LOW                                         (0x0000U)
#define MSB_INFO_CHIP_ID_LOW                                         (15)
#define LSB_INFO_CHIP_ID_LOW                                         (0)
#define VBMASK_INFO_CHIP_ID_LOW                                      (0xffffU)
#define ROMASK_INFO_CHIP_ID_LOW                                      (0xffffU)
#define AADDR_INFO_CHIP_ID_LOW                                       (BASE_ADDR_INFO + ADDR_INFO_CHIP_ID_LOW)
#define REG_INFO_CHIP_ID_LOW                                         (*(volatile unsigned short *)((unsigned int)AADDR_INFO_CHIP_ID_LOW))

#define ADDR_INFO_CHIP_ID_HIGH                                       (0x2U)
#define A_INFO_CHIP_ID_HIGH(ba)                                      ((ba) + ADDR_INFO_CHIP_ID_HIGH)
#define R_INFO_CHIP_ID_HIGH(ba)                                      (*(volatile unsigned short *)((unsigned int)A_INFO_CHIP_ID_HIGH(ba)))
#define RES_INFO_CHIP_ID_HIGH                                        (0x0000U)
#define MSB_INFO_CHIP_ID_HIGH                                        (15)
#define LSB_INFO_CHIP_ID_HIGH                                        (0)
#define VBMASK_INFO_CHIP_ID_HIGH                                     (0xffffU)
#define ROMASK_INFO_CHIP_ID_HIGH                                     (0xffffU)
#define AADDR_INFO_CHIP_ID_HIGH                                      (BASE_ADDR_INFO + ADDR_INFO_CHIP_ID_HIGH)
#define REG_INFO_CHIP_ID_HIGH                                        (*(volatile unsigned short *)((unsigned int)AADDR_INFO_CHIP_ID_HIGH))

 


// Instance base addresses

#ifndef BASE_ADDR_Supply 
#define BASE_ADDR_Supply 0x0000U
#define SIZE_Supply 0x0040U
#endif

// Register bit field definitions
	 
/* Supply_TRIM_IREF */

#define MSK_SUPPLY_TRIM_IREF_IREF                                    (0xf)
#define SFT_SUPPLY_TRIM_IREF_IREF                                    (0)
#define LSB_SUPPLY_TRIM_IREF_IREF                                    (0)
#define MSB_SUPPLY_TRIM_IREF_IREF                                    (3)

typedef struct {
  unsigned short iref : 4;
  unsigned short reserved : 12;
} supply_trim_iref_bf;
		
typedef union {
  unsigned short val;
  supply_trim_iref_bf bf;
} supply_trim_iref_t;


/* Supply_TRIM_OT */

#define MSK_SUPPLY_TRIM_OT_TRIM_OT                                   (0x3)
#define SFT_SUPPLY_TRIM_OT_TRIM_OT                                   (0)
#define LSB_SUPPLY_TRIM_OT_TRIM_OT                                   (0)
#define MSB_SUPPLY_TRIM_OT_TRIM_OT                                   (1)

typedef struct {
  unsigned short trim_ot : 2;
  unsigned short reserved : 14;
} supply_trim_ot_bf;
		
typedef union {
  unsigned short val;
  supply_trim_ot_bf bf;
} supply_trim_ot_t;


/* Supply_SUP_HW_CTRL */

#define BIT_SUPPLY_SUP_HW_CTRL_IGNORE_UV                             (0)#define MSK_SUPPLY_SUP_HW_CTRL_IGNORE_UV                             (0x1)
#define SFT_SUPPLY_SUP_HW_CTRL_IGNORE_UV                             (0)
#define LSB_SUPPLY_SUP_HW_CTRL_IGNORE_UV                             (0)
#define MSB_SUPPLY_SUP_HW_CTRL_IGNORE_UV                             (0)

#define BIT_SUPPLY_SUP_HW_CTRL_IGNORE_HWF                            (0)#define MSK_SUPPLY_SUP_HW_CTRL_IGNORE_HWF                            (0x1)
#define SFT_SUPPLY_SUP_HW_CTRL_IGNORE_HWF                            (0)
#define LSB_SUPPLY_SUP_HW_CTRL_IGNORE_HWF                            (1)
#define MSB_SUPPLY_SUP_HW_CTRL_IGNORE_HWF                            (1)

typedef struct {
  unsigned short ignore_uv : 1;
  unsigned short ignore_hwf : 1;
  unsigned short reserved : 14;
} supply_sup_hw_ctrl_bf;
		
typedef union {
  unsigned short val;
  supply_sup_hw_ctrl_bf bf;
} supply_sup_hw_ctrl_t;


/* Supply_SUP_IRQ_STAT */

#define BIT_SUPPLY_SUP_IRQ_STAT_REF_FAIL                             (0)#define MSK_SUPPLY_SUP_IRQ_STAT_REF_FAIL                             (0x1)
#define SFT_SUPPLY_SUP_IRQ_STAT_REF_FAIL                             (0)
#define LSB_SUPPLY_SUP_IRQ_STAT_REF_FAIL                             (0)
#define MSB_SUPPLY_SUP_IRQ_STAT_REF_FAIL                             (0)

#define BIT_SUPPLY_SUP_IRQ_STAT_VCCUV                                (0)#define MSK_SUPPLY_SUP_IRQ_STAT_VCCUV                                (0x1)
#define SFT_SUPPLY_SUP_IRQ_STAT_VCCUV                                (0)
#define LSB_SUPPLY_SUP_IRQ_STAT_VCCUV                                (1)
#define MSB_SUPPLY_SUP_IRQ_STAT_VCCUV                                (1)

#define BIT_SUPPLY_SUP_IRQ_STAT_LDOUV                                (0)#define MSK_SUPPLY_SUP_IRQ_STAT_LDOUV                                (0x1)
#define SFT_SUPPLY_SUP_IRQ_STAT_LDOUV                                (0)
#define LSB_SUPPLY_SUP_IRQ_STAT_LDOUV                                (2)
#define MSB_SUPPLY_SUP_IRQ_STAT_LDOUV                                (2)

#define BIT_SUPPLY_SUP_IRQ_STAT_OTE                                  (0)#define MSK_SUPPLY_SUP_IRQ_STAT_OTE                                  (0x1)
#define SFT_SUPPLY_SUP_IRQ_STAT_OTE                                  (0)
#define LSB_SUPPLY_SUP_IRQ_STAT_OTE                                  (3)
#define MSB_SUPPLY_SUP_IRQ_STAT_OTE                                  (3)

#define BIT_SUPPLY_SUP_IRQ_STAT_OTW                                  (0)#define MSK_SUPPLY_SUP_IRQ_STAT_OTW                                  (0x1)
#define SFT_SUPPLY_SUP_IRQ_STAT_OTW                                  (0)
#define LSB_SUPPLY_SUP_IRQ_STAT_OTW                                  (4)
#define MSB_SUPPLY_SUP_IRQ_STAT_OTW                                  (4)

typedef struct {
  unsigned short ref_fail : 1;
  unsigned short vccuv : 1;
  unsigned short ldouv : 1;
  unsigned short ote : 1;
  unsigned short otw : 1;
} supply_sup_irq_stat_bf;
		
typedef union {
  unsigned short val;
  supply_sup_irq_stat_bf bf;
} supply_sup_irq_stat_t;


/* Supply_SUP_IRQ_MASK */

#define BIT_SUPPLY_SUP_IRQ_MASK_REF_FAIL                             (0)#define MSK_SUPPLY_SUP_IRQ_MASK_REF_FAIL                             (0x1)
#define SFT_SUPPLY_SUP_IRQ_MASK_REF_FAIL                             (0)
#define LSB_SUPPLY_SUP_IRQ_MASK_REF_FAIL                             (0)
#define MSB_SUPPLY_SUP_IRQ_MASK_REF_FAIL                             (0)

#define BIT_SUPPLY_SUP_IRQ_MASK_VCCUV                                (0)#define MSK_SUPPLY_SUP_IRQ_MASK_VCCUV                                (0x1)
#define SFT_SUPPLY_SUP_IRQ_MASK_VCCUV                                (0)
#define LSB_SUPPLY_SUP_IRQ_MASK_VCCUV                                (1)
#define MSB_SUPPLY_SUP_IRQ_MASK_VCCUV                                (1)

#define BIT_SUPPLY_SUP_IRQ_MASK_LDOUV                                (0)#define MSK_SUPPLY_SUP_IRQ_MASK_LDOUV                                (0x1)
#define SFT_SUPPLY_SUP_IRQ_MASK_LDOUV                                (0)
#define LSB_SUPPLY_SUP_IRQ_MASK_LDOUV                                (2)
#define MSB_SUPPLY_SUP_IRQ_MASK_LDOUV                                (2)

#define BIT_SUPPLY_SUP_IRQ_MASK_OTE                                  (0)#define MSK_SUPPLY_SUP_IRQ_MASK_OTE                                  (0x1)
#define SFT_SUPPLY_SUP_IRQ_MASK_OTE                                  (0)
#define LSB_SUPPLY_SUP_IRQ_MASK_OTE                                  (3)
#define MSB_SUPPLY_SUP_IRQ_MASK_OTE                                  (3)

#define BIT_SUPPLY_SUP_IRQ_MASK_OTW                                  (0)#define MSK_SUPPLY_SUP_IRQ_MASK_OTW                                  (0x1)
#define SFT_SUPPLY_SUP_IRQ_MASK_OTW                                  (0)
#define LSB_SUPPLY_SUP_IRQ_MASK_OTW                                  (4)
#define MSB_SUPPLY_SUP_IRQ_MASK_OTW                                  (4)

typedef struct {
  unsigned short ref_fail : 1;
  unsigned short vccuv : 1;
  unsigned short ldouv : 1;
  unsigned short ote : 1;
  unsigned short otw : 1;
} supply_sup_irq_mask_bf;
		
typedef union {
  unsigned short val;
  supply_sup_irq_mask_bf bf;
} supply_sup_irq_mask_t;


/* Supply_SUP_STAT */

#define BIT_SUPPLY_SUP_STAT_REF_FAIL                                 (0)#define MSK_SUPPLY_SUP_STAT_REF_FAIL                                 (0x1)
#define SFT_SUPPLY_SUP_STAT_REF_FAIL                                 (0)
#define LSB_SUPPLY_SUP_STAT_REF_FAIL                                 (0)
#define MSB_SUPPLY_SUP_STAT_REF_FAIL                                 (0)

#define BIT_SUPPLY_SUP_STAT_VCCUV                                    (0)#define MSK_SUPPLY_SUP_STAT_VCCUV                                    (0x1)
#define SFT_SUPPLY_SUP_STAT_VCCUV                                    (0)
#define LSB_SUPPLY_SUP_STAT_VCCUV                                    (1)
#define MSB_SUPPLY_SUP_STAT_VCCUV                                    (1)

#define BIT_SUPPLY_SUP_STAT_LDOUV                                    (0)#define MSK_SUPPLY_SUP_STAT_LDOUV                                    (0x1)
#define SFT_SUPPLY_SUP_STAT_LDOUV                                    (0)
#define LSB_SUPPLY_SUP_STAT_LDOUV                                    (2)
#define MSB_SUPPLY_SUP_STAT_LDOUV                                    (2)

#define BIT_SUPPLY_SUP_STAT_OTE                                      (0)#define MSK_SUPPLY_SUP_STAT_OTE                                      (0x1)
#define SFT_SUPPLY_SUP_STAT_OTE                                      (0)
#define LSB_SUPPLY_SUP_STAT_OTE                                      (3)
#define MSB_SUPPLY_SUP_STAT_OTE                                      (3)

#define BIT_SUPPLY_SUP_STAT_OTW                                      (0)#define MSK_SUPPLY_SUP_STAT_OTW                                      (0x1)
#define SFT_SUPPLY_SUP_STAT_OTW                                      (0)
#define LSB_SUPPLY_SUP_STAT_OTW                                      (4)
#define MSB_SUPPLY_SUP_STAT_OTW                                      (4)

typedef struct {
  unsigned short ref_fail : 1;
  unsigned short vccuv : 1;
  unsigned short ldouv : 1;
  unsigned short ote : 1;
  unsigned short otw : 1;
} supply_sup_stat_bf;
		
typedef union {
  unsigned short val;
  supply_sup_stat_bf bf;
} supply_sup_stat_t;


/* Supply_SUP_CTRL */

#define BIT_SUPPLY_SUP_CTRL_EN_LDO                                   (0)#define MSK_SUPPLY_SUP_CTRL_EN_LDO                                   (0x1)
#define SFT_SUPPLY_SUP_CTRL_EN_LDO                                   (0)
#define LSB_SUPPLY_SUP_CTRL_EN_LDO                                   (0)
#define MSB_SUPPLY_SUP_CTRL_EN_LDO                                   (0)

typedef struct {
  unsigned short en_ldo : 1;
} supply_sup_ctrl_bf;
		
typedef union {
  unsigned short val;
  supply_sup_ctrl_bf bf;
} supply_sup_ctrl_t;


/* Supply_IO_CTRL */

#define BIT_SUPPLY_IO_CTRL_HICUR                                     (0)#define MSK_SUPPLY_IO_CTRL_HICUR                                     (0x1)
#define SFT_SUPPLY_IO_CTRL_HICUR                                     (0)
#define LSB_SUPPLY_IO_CTRL_HICUR                                     (0)
#define MSB_SUPPLY_IO_CTRL_HICUR                                     (0)

typedef struct {
  unsigned short hicur : 1;
} supply_io_ctrl_bf;
		
typedef union {
  unsigned short val;
  supply_io_ctrl_bf bf;
} supply_io_ctrl_t;



typedef struct {
  supply_trim_iref_t                                                 trim_iref;
  supply_trim_ot_t                                                   trim_ot;
  supply_sup_hw_ctrl_t                                               sup_hw_ctrl;
  supply_sup_irq_stat_t                                              sup_irq_stat;
  supply_sup_irq_mask_t                                              sup_irq_mask;
  supply_sup_stat_t                                                  sup_stat;
  supply_sup_ctrl_t                                                  sup_ctrl;
  supply_io_ctrl_t                                                   io_ctrl;
} supply_t;

typedef union {
  unsigned short a[sizeof(supply_t)/sizeof(unsigned short)];
  supply_t s;
} supply_u_t;


#define ADDR_SUPPLY_TRIM_IREF                                        (0x3U)
#define A_SUPPLY_TRIM_IREF(ba)                                       ((ba) + ADDR_SUPPLY_TRIM_IREF)
#define R_SUPPLY_TRIM_IREF(ba)                                       (*(volatile unsigned short *)((unsigned int)A_SUPPLY_TRIM_IREF(ba)))
#define RES_SUPPLY_TRIM_IREF                                         (0x0000U)
#define MSB_SUPPLY_TRIM_IREF                                         (15)
#define LSB_SUPPLY_TRIM_IREF                                         (0)
#define VBMASK_SUPPLY_TRIM_IREF                                      (0x000fU)
#define ROMASK_SUPPLY_TRIM_IREF                                      (0xffffU)
#define AADDR_SUPPLY_TRIM_IREF                                       (BASE_ADDR_SUPPLY + ADDR_SUPPLY_TRIM_IREF)
#define REG_SUPPLY_TRIM_IREF                                         (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_TRIM_IREF))

#define ADDR_SUPPLY_TRIM_OT                                          (0x4U)
#define A_SUPPLY_TRIM_OT(ba)                                         ((ba) + ADDR_SUPPLY_TRIM_OT)
#define R_SUPPLY_TRIM_OT(ba)                                         (*(volatile unsigned short *)((unsigned int)A_SUPPLY_TRIM_OT(ba)))
#define RES_SUPPLY_TRIM_OT                                           (0x0000U)
#define MSB_SUPPLY_TRIM_OT                                           (15)
#define LSB_SUPPLY_TRIM_OT                                           (0)
#define VBMASK_SUPPLY_TRIM_OT                                        (0x0003U)
#define ROMASK_SUPPLY_TRIM_OT                                        (0xffffU)
#define AADDR_SUPPLY_TRIM_OT                                         (BASE_ADDR_SUPPLY + ADDR_SUPPLY_TRIM_OT)
#define REG_SUPPLY_TRIM_OT                                           (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_TRIM_OT))

#define ADDR_SUPPLY_SUP_HW_CTRL                                      (0x3CU)
#define A_SUPPLY_SUP_HW_CTRL(ba)                                     ((ba) + ADDR_SUPPLY_SUP_HW_CTRL)
#define R_SUPPLY_SUP_HW_CTRL(ba)                                     (*(volatile unsigned short *)((unsigned int)A_SUPPLY_SUP_HW_CTRL(ba)))
#define RES_SUPPLY_SUP_HW_CTRL                                       (0x0000U)
#define MSB_SUPPLY_SUP_HW_CTRL                                       (15)
#define LSB_SUPPLY_SUP_HW_CTRL                                       (0)
#define VBMASK_SUPPLY_SUP_HW_CTRL                                    (0x0003U)
#define ROMASK_SUPPLY_SUP_HW_CTRL                                    (0xfffcU)
#define AADDR_SUPPLY_SUP_HW_CTRL                                     (BASE_ADDR_SUPPLY + ADDR_SUPPLY_SUP_HW_CTRL)
#define REG_SUPPLY_SUP_HW_CTRL                                       (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_SUP_HW_CTRL))

#define ADDR_SUPPLY_SUP_IRQ_STAT                                     (0x3AU)
#define A_SUPPLY_SUP_IRQ_STAT(ba)                                    ((ba) + ADDR_SUPPLY_SUP_IRQ_STAT)
#define R_SUPPLY_SUP_IRQ_STAT(ba)                                    (*(volatile unsigned short *)((unsigned int)A_SUPPLY_SUP_IRQ_STAT(ba)))
#define RES_SUPPLY_SUP_IRQ_STAT                                      (0x0000U)
#define MSB_SUPPLY_SUP_IRQ_STAT                                      (4)
#define LSB_SUPPLY_SUP_IRQ_STAT                                      (0)
#define VBMASK_SUPPLY_SUP_IRQ_STAT                                   (0x001fU)
#define ROMASK_SUPPLY_SUP_IRQ_STAT                                   (0x0000U)
#define AADDR_SUPPLY_SUP_IRQ_STAT                                    (BASE_ADDR_SUPPLY + ADDR_SUPPLY_SUP_IRQ_STAT)
#define REG_SUPPLY_SUP_IRQ_STAT                                      (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_SUP_IRQ_STAT))

#define ADDR_SUPPLY_SUP_IRQ_MASK                                     (0x3BU)
#define A_SUPPLY_SUP_IRQ_MASK(ba)                                    ((ba) + ADDR_SUPPLY_SUP_IRQ_MASK)
#define R_SUPPLY_SUP_IRQ_MASK(ba)                                    (*(volatile unsigned short *)((unsigned int)A_SUPPLY_SUP_IRQ_MASK(ba)))
#define RES_SUPPLY_SUP_IRQ_MASK                                      (0x001fU)
#define MSB_SUPPLY_SUP_IRQ_MASK                                      (4)
#define LSB_SUPPLY_SUP_IRQ_MASK                                      (0)
#define VBMASK_SUPPLY_SUP_IRQ_MASK                                   (0x001fU)
#define ROMASK_SUPPLY_SUP_IRQ_MASK                                   (0x0000U)
#define AADDR_SUPPLY_SUP_IRQ_MASK                                    (BASE_ADDR_SUPPLY + ADDR_SUPPLY_SUP_IRQ_MASK)
#define REG_SUPPLY_SUP_IRQ_MASK                                      (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_SUP_IRQ_MASK))

#define ADDR_SUPPLY_SUP_STAT                                         (0x3DU)
#define A_SUPPLY_SUP_STAT(ba)                                        ((ba) + ADDR_SUPPLY_SUP_STAT)
#define R_SUPPLY_SUP_STAT(ba)                                        (*(volatile unsigned short *)((unsigned int)A_SUPPLY_SUP_STAT(ba)))
#define RES_SUPPLY_SUP_STAT                                          (0x0000U)
#define MSB_SUPPLY_SUP_STAT                                          (4)
#define LSB_SUPPLY_SUP_STAT                                          (0)
#define VBMASK_SUPPLY_SUP_STAT                                       (0x001fU)
#define ROMASK_SUPPLY_SUP_STAT                                       (0x001fU)
#define AADDR_SUPPLY_SUP_STAT                                        (BASE_ADDR_SUPPLY + ADDR_SUPPLY_SUP_STAT)
#define REG_SUPPLY_SUP_STAT                                          (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_SUP_STAT))

#define ADDR_SUPPLY_SUP_CTRL                                         (0x3EU)
#define A_SUPPLY_SUP_CTRL(ba)                                        ((ba) + ADDR_SUPPLY_SUP_CTRL)
#define R_SUPPLY_SUP_CTRL(ba)                                        (*(volatile unsigned short *)((unsigned int)A_SUPPLY_SUP_CTRL(ba)))
#define RES_SUPPLY_SUP_CTRL                                          (0x0001U)
#define MSB_SUPPLY_SUP_CTRL                                          (0)
#define LSB_SUPPLY_SUP_CTRL                                          (0)
#define VBMASK_SUPPLY_SUP_CTRL                                       (0x0001U)
#define ROMASK_SUPPLY_SUP_CTRL                                       (0x0000U)
#define AADDR_SUPPLY_SUP_CTRL                                        (BASE_ADDR_SUPPLY + ADDR_SUPPLY_SUP_CTRL)
#define REG_SUPPLY_SUP_CTRL                                          (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_SUP_CTRL))

#define ADDR_SUPPLY_IO_CTRL                                          (0x3FU)
#define A_SUPPLY_IO_CTRL(ba)                                         ((ba) + ADDR_SUPPLY_IO_CTRL)
#define R_SUPPLY_IO_CTRL(ba)                                         (*(volatile unsigned short *)((unsigned int)A_SUPPLY_IO_CTRL(ba)))
#define RES_SUPPLY_IO_CTRL                                           (0x0001U)
#define MSB_SUPPLY_IO_CTRL                                           (0)
#define LSB_SUPPLY_IO_CTRL                                           (0)
#define VBMASK_SUPPLY_IO_CTRL                                        (0x0001U)
#define ROMASK_SUPPLY_IO_CTRL                                        (0x0000U)
#define AADDR_SUPPLY_IO_CTRL                                         (BASE_ADDR_SUPPLY + ADDR_SUPPLY_IO_CTRL)
#define REG_SUPPLY_IO_CTRL                                           (*(volatile unsigned short *)((unsigned int)AADDR_SUPPLY_IO_CTRL))

 


// Instance base addresses

#ifndef BASE_ADDR_Timebase 
#define BASE_ADDR_Timebase 0x0000U
#define SIZE_Timebase 0x0050U
#endif

// Register bit field definitions
	 
/* Timebase_CLKREF_CONF */

#define MSK_TIMEBASE_CLKREF_CONF_CLKREF_FREQ                         (0x3)
#define SFT_TIMEBASE_CLKREF_CONF_CLKREF_FREQ                         (0)
#define LSB_TIMEBASE_CLKREF_CONF_CLKREF_FREQ                         (0)
#define MSB_TIMEBASE_CLKREF_CONF_CLKREF_FREQ                         (1)

typedef struct {
  unsigned short clkref_freq : 2;
} timebase_clkref_conf_bf;
		
typedef union {
  unsigned short val;
  timebase_clkref_conf_bf bf;
} timebase_clkref_conf_t;


/* Timebase_TB_CNT */

#define MSK_TIMEBASE_TB_CNT_CNT                                      (0xffff)
#define SFT_TIMEBASE_TB_CNT_CNT                                      (0)
#define LSB_TIMEBASE_TB_CNT_CNT                                      (0)
#define MSB_TIMEBASE_TB_CNT_CNT                                      (15)

typedef struct {
  unsigned short cnt : 16;
} timebase_tb_cnt_bf;
		
typedef union {
  unsigned short val;
  timebase_tb_cnt_bf bf;
} timebase_tb_cnt_t;


/* Timebase_TRIM_OSC */

#define MSK_TIMEBASE_TRIM_OSC_TRIM_OSC                               (0x7f)
#define SFT_TIMEBASE_TRIM_OSC_TRIM_OSC                               (0)
#define LSB_TIMEBASE_TRIM_OSC_TRIM_OSC                               (0)
#define MSB_TIMEBASE_TRIM_OSC_TRIM_OSC                               (6)

typedef struct {
  unsigned short trim_osc : 7;
} timebase_trim_osc_bf;
		
typedef union {
  unsigned short val;
  timebase_trim_osc_bf bf;
} timebase_trim_osc_t;


/* Timebase_TRIM_OSC_TCF */

#define MSK_TIMEBASE_TRIM_OSC_TCF_TCF                                (0x7)
#define SFT_TIMEBASE_TRIM_OSC_TCF_TCF                                (0)
#define LSB_TIMEBASE_TRIM_OSC_TCF_TCF                                (0)
#define MSB_TIMEBASE_TRIM_OSC_TCF_TCF                                (2)

typedef struct {
  unsigned short tcf : 3;
} timebase_trim_osc_tcf_bf;
		
typedef union {
  unsigned short val;
  timebase_trim_osc_tcf_bf bf;
} timebase_trim_osc_tcf_t;



typedef struct {
  timebase_clkref_conf_t                                             clkref_conf;
  timebase_tb_cnt_t                                                  tb_cnt;
  timebase_trim_osc_t                                                trim_osc;
  timebase_trim_osc_tcf_t                                            trim_osc_tcf;
} timebase_t;

typedef union {
  unsigned short a[sizeof(timebase_t)/sizeof(unsigned short)];
  timebase_t s;
} timebase_u_t;


#define ADDR_TIMEBASE_CLKREF_CONF                                    (0x40U)
#define A_TIMEBASE_CLKREF_CONF(ba)                                   ((ba) + ADDR_TIMEBASE_CLKREF_CONF)
#define R_TIMEBASE_CLKREF_CONF(ba)                                   (*(volatile unsigned short *)((unsigned int)A_TIMEBASE_CLKREF_CONF(ba)))
#define RES_TIMEBASE_CLKREF_CONF                                     (0x0000U)
#define MSB_TIMEBASE_CLKREF_CONF                                     (1)
#define LSB_TIMEBASE_CLKREF_CONF                                     (0)
#define VBMASK_TIMEBASE_CLKREF_CONF                                  (0x0003U)
#define ROMASK_TIMEBASE_CLKREF_CONF                                  (0x0000U)
#define AADDR_TIMEBASE_CLKREF_CONF                                   (BASE_ADDR_TIMEBASE + ADDR_TIMEBASE_CLKREF_CONF)
#define REG_TIMEBASE_CLKREF_CONF                                     (*(volatile unsigned short *)((unsigned int)AADDR_TIMEBASE_CLKREF_CONF))

#define ADDR_TIMEBASE_TB_CNT                                         (0x41U)
#define A_TIMEBASE_TB_CNT(ba)                                        ((ba) + ADDR_TIMEBASE_TB_CNT)
#define R_TIMEBASE_TB_CNT(ba)                                        (*(volatile unsigned short *)((unsigned int)A_TIMEBASE_TB_CNT(ba)))
#define RES_TIMEBASE_TB_CNT                                          (0x0000U)
#define MSB_TIMEBASE_TB_CNT                                          (15)
#define LSB_TIMEBASE_TB_CNT                                          (0)
#define VBMASK_TIMEBASE_TB_CNT                                       (0xffffU)
#define ROMASK_TIMEBASE_TB_CNT                                       (0xffffU)
#define AADDR_TIMEBASE_TB_CNT                                        (BASE_ADDR_TIMEBASE + ADDR_TIMEBASE_TB_CNT)
#define REG_TIMEBASE_TB_CNT                                          (*(volatile unsigned short *)((unsigned int)AADDR_TIMEBASE_TB_CNT))

#define ADDR_TIMEBASE_TRIM_OSC                                       (0x6U)
#define A_TIMEBASE_TRIM_OSC(ba)                                      ((ba) + ADDR_TIMEBASE_TRIM_OSC)
#define R_TIMEBASE_TRIM_OSC(ba)                                      (*(volatile unsigned short *)((unsigned int)A_TIMEBASE_TRIM_OSC(ba)))
#define RES_TIMEBASE_TRIM_OSC                                        (0x0020U)
#define MSB_TIMEBASE_TRIM_OSC                                        (6)
#define LSB_TIMEBASE_TRIM_OSC                                        (0)
#define VBMASK_TIMEBASE_TRIM_OSC                                     (0x007fU)
#define ROMASK_TIMEBASE_TRIM_OSC                                     (0x007fU)
#define AADDR_TIMEBASE_TRIM_OSC                                      (BASE_ADDR_TIMEBASE + ADDR_TIMEBASE_TRIM_OSC)
#define REG_TIMEBASE_TRIM_OSC                                        (*(volatile unsigned short *)((unsigned int)AADDR_TIMEBASE_TRIM_OSC))

#define ADDR_TIMEBASE_TRIM_OSC_TCF                                   (0x7U)
#define A_TIMEBASE_TRIM_OSC_TCF(ba)                                  ((ba) + ADDR_TIMEBASE_TRIM_OSC_TCF)
#define R_TIMEBASE_TRIM_OSC_TCF(ba)                                  (*(volatile unsigned short *)((unsigned int)A_TIMEBASE_TRIM_OSC_TCF(ba)))
#define RES_TIMEBASE_TRIM_OSC_TCF                                    (0x0003U)
#define MSB_TIMEBASE_TRIM_OSC_TCF                                    (2)
#define LSB_TIMEBASE_TRIM_OSC_TCF                                    (0)
#define VBMASK_TIMEBASE_TRIM_OSC_TCF                                 (0x0007U)
#define ROMASK_TIMEBASE_TRIM_OSC_TCF                                 (0x0007U)
#define AADDR_TIMEBASE_TRIM_OSC_TCF                                  (BASE_ADDR_TIMEBASE + ADDR_TIMEBASE_TRIM_OSC_TCF)
#define REG_TIMEBASE_TRIM_OSC_TCF                                    (*(volatile unsigned short *)((unsigned int)AADDR_TIMEBASE_TRIM_OSC_TCF))

 


// Instance base addresses

#ifndef BASE_ADDR_Interrupt 
#define BASE_ADDR_Interrupt 0x0000U
#define SIZE_Interrupt 0x0060U
#endif

// Register bit field definitions
	 
/* Interrupt_IRQ_STAT */

#define BIT_INTERRUPT_IRQ_STAT_OTPFAIL                               (0)#define MSK_INTERRUPT_IRQ_STAT_OTPFAIL                               (0x1)
#define SFT_INTERRUPT_IRQ_STAT_OTPFAIL                               (0)
#define LSB_INTERRUPT_IRQ_STAT_OTPFAIL                               (0)
#define MSB_INTERRUPT_IRQ_STAT_OTPFAIL                               (0)

#define BIT_INTERRUPT_IRQ_STAT_CLKREF                                (0)#define MSK_INTERRUPT_IRQ_STAT_CLKREF                                (0x1)
#define SFT_INTERRUPT_IRQ_STAT_CLKREF                                (0)
#define LSB_INTERRUPT_IRQ_STAT_CLKREF                                (1)
#define MSB_INTERRUPT_IRQ_STAT_CLKREF                                (1)

#define BIT_INTERRUPT_IRQ_STAT_RESET                                 (0)#define MSK_INTERRUPT_IRQ_STAT_RESET                                 (0x1)
#define SFT_INTERRUPT_IRQ_STAT_RESET                                 (0)
#define LSB_INTERRUPT_IRQ_STAT_RESET                                 (2)
#define MSB_INTERRUPT_IRQ_STAT_RESET                                 (2)

#define BIT_INTERRUPT_IRQ_STAT_SPI                                   (0)#define MSK_INTERRUPT_IRQ_STAT_SPI                                   (0x1)
#define SFT_INTERRUPT_IRQ_STAT_SPI                                   (0)
#define LSB_INTERRUPT_IRQ_STAT_SPI                                   (3)
#define MSB_INTERRUPT_IRQ_STAT_SPI                                   (3)

#define BIT_INTERRUPT_IRQ_STAT_BUF                                   (0)#define MSK_INTERRUPT_IRQ_STAT_BUF                                   (0x1)
#define SFT_INTERRUPT_IRQ_STAT_BUF                                   (0)
#define LSB_INTERRUPT_IRQ_STAT_BUF                                   (4)
#define MSB_INTERRUPT_IRQ_STAT_BUF                                   (4)

#define MSK_INTERRUPT_IRQ_STAT_DSI                                   (0x3)
#define SFT_INTERRUPT_IRQ_STAT_DSI                                   (0)
#define LSB_INTERRUPT_IRQ_STAT_DSI                                   (5)
#define MSB_INTERRUPT_IRQ_STAT_DSI                                   (6)

#define BIT_INTERRUPT_IRQ_STAT_SUPPLY                                (0)#define MSK_INTERRUPT_IRQ_STAT_SUPPLY                                (0x1)
#define SFT_INTERRUPT_IRQ_STAT_SUPPLY                                (0)
#define LSB_INTERRUPT_IRQ_STAT_SUPPLY                                (9)
#define MSB_INTERRUPT_IRQ_STAT_SUPPLY                                (9)

#define BIT_INTERRUPT_IRQ_STAT_ECC_FAIL                              (0)#define MSK_INTERRUPT_IRQ_STAT_ECC_FAIL                              (0x1)
#define SFT_INTERRUPT_IRQ_STAT_ECC_FAIL                              (0)
#define LSB_INTERRUPT_IRQ_STAT_ECC_FAIL                              (10)
#define MSB_INTERRUPT_IRQ_STAT_ECC_FAIL                              (10)

#define BIT_INTERRUPT_IRQ_STAT_RESERVED                              (0)#define MSK_INTERRUPT_IRQ_STAT_RESERVED                              (0x1)
#define SFT_INTERRUPT_IRQ_STAT_RESERVED                              (0)
#define LSB_INTERRUPT_IRQ_STAT_RESERVED                              (11)
#define MSB_INTERRUPT_IRQ_STAT_RESERVED                              (11)

#define BIT_INTERRUPT_IRQ_STAT_HW_FAIL                               (0)#define MSK_INTERRUPT_IRQ_STAT_HW_FAIL                               (0x1)
#define SFT_INTERRUPT_IRQ_STAT_HW_FAIL                               (0)
#define LSB_INTERRUPT_IRQ_STAT_HW_FAIL                               (12)
#define MSB_INTERRUPT_IRQ_STAT_HW_FAIL                               (12)

typedef struct {
  unsigned short otpfail : 1;
  unsigned short clkref : 1;
  unsigned short reset : 1;
  unsigned short spi : 1;
  unsigned short buf : 1;
  unsigned short dsi : 2;
  unsigned short reserved : 2;
  unsigned short supply : 1;
  unsigned short ecc_fail : 1;
  unsigned short reserved : 1;
  unsigned short hw_fail : 1;
  unsigned short reserved : 3;
} interrupt_irq_stat_bf;
		
typedef union {
  unsigned short val;
  interrupt_irq_stat_bf bf;
} interrupt_irq_stat_t;


/* Interrupt_IRQ_MASK */

#define BIT_INTERRUPT_IRQ_MASK_OTPFAIL                               (0)#define MSK_INTERRUPT_IRQ_MASK_OTPFAIL                               (0x1)
#define SFT_INTERRUPT_IRQ_MASK_OTPFAIL                               (0)
#define LSB_INTERRUPT_IRQ_MASK_OTPFAIL                               (0)
#define MSB_INTERRUPT_IRQ_MASK_OTPFAIL                               (0)

#define BIT_INTERRUPT_IRQ_MASK_CLKREF                                (0)#define MSK_INTERRUPT_IRQ_MASK_CLKREF                                (0x1)
#define SFT_INTERRUPT_IRQ_MASK_CLKREF                                (0)
#define LSB_INTERRUPT_IRQ_MASK_CLKREF                                (1)
#define MSB_INTERRUPT_IRQ_MASK_CLKREF                                (1)

#define BIT_INTERRUPT_IRQ_MASK_RESET                                 (0)#define MSK_INTERRUPT_IRQ_MASK_RESET                                 (0x1)
#define SFT_INTERRUPT_IRQ_MASK_RESET                                 (0)
#define LSB_INTERRUPT_IRQ_MASK_RESET                                 (2)
#define MSB_INTERRUPT_IRQ_MASK_RESET                                 (2)

#define BIT_INTERRUPT_IRQ_MASK_SPI                                   (0)#define MSK_INTERRUPT_IRQ_MASK_SPI                                   (0x1)
#define SFT_INTERRUPT_IRQ_MASK_SPI                                   (0)
#define LSB_INTERRUPT_IRQ_MASK_SPI                                   (3)
#define MSB_INTERRUPT_IRQ_MASK_SPI                                   (3)

#define BIT_INTERRUPT_IRQ_MASK_BUF                                   (0)#define MSK_INTERRUPT_IRQ_MASK_BUF                                   (0x1)
#define SFT_INTERRUPT_IRQ_MASK_BUF                                   (0)
#define LSB_INTERRUPT_IRQ_MASK_BUF                                   (4)
#define MSB_INTERRUPT_IRQ_MASK_BUF                                   (4)

#define MSK_INTERRUPT_IRQ_MASK_DSI                                   (0x3)
#define SFT_INTERRUPT_IRQ_MASK_DSI                                   (0)
#define LSB_INTERRUPT_IRQ_MASK_DSI                                   (5)
#define MSB_INTERRUPT_IRQ_MASK_DSI                                   (6)

#define BIT_INTERRUPT_IRQ_MASK_SUPPLY                                (0)#define MSK_INTERRUPT_IRQ_MASK_SUPPLY                                (0x1)
#define SFT_INTERRUPT_IRQ_MASK_SUPPLY                                (0)
#define LSB_INTERRUPT_IRQ_MASK_SUPPLY                                (9)
#define MSB_INTERRUPT_IRQ_MASK_SUPPLY                                (9)

#define BIT_INTERRUPT_IRQ_MASK_ECC_FAIL                              (0)#define MSK_INTERRUPT_IRQ_MASK_ECC_FAIL                              (0x1)
#define SFT_INTERRUPT_IRQ_MASK_ECC_FAIL                              (0)
#define LSB_INTERRUPT_IRQ_MASK_ECC_FAIL                              (10)
#define MSB_INTERRUPT_IRQ_MASK_ECC_FAIL                              (10)

#define BIT_INTERRUPT_IRQ_MASK_RESERVED                              (0)#define MSK_INTERRUPT_IRQ_MASK_RESERVED                              (0x1)
#define SFT_INTERRUPT_IRQ_MASK_RESERVED                              (0)
#define LSB_INTERRUPT_IRQ_MASK_RESERVED                              (11)
#define MSB_INTERRUPT_IRQ_MASK_RESERVED                              (11)

#define BIT_INTERRUPT_IRQ_MASK_HW_FAIL                               (0)#define MSK_INTERRUPT_IRQ_MASK_HW_FAIL                               (0x1)
#define SFT_INTERRUPT_IRQ_MASK_HW_FAIL                               (0)
#define LSB_INTERRUPT_IRQ_MASK_HW_FAIL                               (12)
#define MSB_INTERRUPT_IRQ_MASK_HW_FAIL                               (12)

typedef struct {
  unsigned short otpfail : 1;
  unsigned short clkref : 1;
  unsigned short reset : 1;
  unsigned short spi : 1;
  unsigned short buf : 1;
  unsigned short dsi : 2;
  unsigned short reserved : 2;
  unsigned short supply : 1;
  unsigned short ecc_fail : 1;
  unsigned short reserved : 1;
  unsigned short hw_fail : 1;
} interrupt_irq_mask_bf;
		
typedef union {
  unsigned short val;
  interrupt_irq_mask_bf bf;
} interrupt_irq_mask_t;


/* Interrupt_ECC_IRQ_STAT */

#define MSK_INTERRUPT_ECC_IRQ_STAT_DSI_CRM_DATA_BUF                  (0x3)
#define SFT_INTERRUPT_ECC_IRQ_STAT_DSI_CRM_DATA_BUF                  (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_DSI_CRM_DATA_BUF                  (0)
#define MSB_INTERRUPT_ECC_IRQ_STAT_DSI_CRM_DATA_BUF                  (1)

#define MSK_INTERRUPT_ECC_IRQ_STAT_DSI_PDCM_DATA_BUF                 (0x3)
#define SFT_INTERRUPT_ECC_IRQ_STAT_DSI_PDCM_DATA_BUF                 (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_DSI_PDCM_DATA_BUF                 (2)
#define MSB_INTERRUPT_ECC_IRQ_STAT_DSI_PDCM_DATA_BUF                 (3)

#define MSK_INTERRUPT_ECC_IRQ_STAT_DSI_CMD_BUF                       (0x3)
#define SFT_INTERRUPT_ECC_IRQ_STAT_DSI_CMD_BUF                       (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_DSI_CMD_BUF                       (4)
#define MSB_INTERRUPT_ECC_IRQ_STAT_DSI_CMD_BUF                       (5)

#define MSK_INTERRUPT_ECC_IRQ_STAT_DSI_TDMA                          (0x3)
#define SFT_INTERRUPT_ECC_IRQ_STAT_DSI_TDMA                          (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_DSI_TDMA                          (6)
#define MSB_INTERRUPT_ECC_IRQ_STAT_DSI_TDMA                          (7)

#define MSK_INTERRUPT_ECC_IRQ_STAT_DSI_CMD                           (0x3)
#define SFT_INTERRUPT_ECC_IRQ_STAT_DSI_CMD                           (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_DSI_CMD                           (8)
#define MSB_INTERRUPT_ECC_IRQ_STAT_DSI_CMD                           (9)

#define BIT_INTERRUPT_ECC_IRQ_STAT_SPI_CMD_BUF                       (0)#define MSK_INTERRUPT_ECC_IRQ_STAT_SPI_CMD_BUF                       (0x1)
#define SFT_INTERRUPT_ECC_IRQ_STAT_SPI_CMD_BUF                       (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_SPI_CMD_BUF                       (12)
#define MSB_INTERRUPT_ECC_IRQ_STAT_SPI_CMD_BUF                       (12)

#define BIT_INTERRUPT_ECC_IRQ_STAT_SPI_CMD                           (0)#define MSK_INTERRUPT_ECC_IRQ_STAT_SPI_CMD                           (0x1)
#define SFT_INTERRUPT_ECC_IRQ_STAT_SPI_CMD                           (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_SPI_CMD                           (13)
#define MSB_INTERRUPT_ECC_IRQ_STAT_SPI_CMD                           (13)

#define BIT_INTERRUPT_ECC_IRQ_STAT_SPI_DATA                          (0)#define MSK_INTERRUPT_ECC_IRQ_STAT_SPI_DATA                          (0x1)
#define SFT_INTERRUPT_ECC_IRQ_STAT_SPI_DATA                          (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_SPI_DATA                          (14)
#define MSB_INTERRUPT_ECC_IRQ_STAT_SPI_DATA                          (14)

#define BIT_INTERRUPT_ECC_IRQ_STAT_RAM                               (0)#define MSK_INTERRUPT_ECC_IRQ_STAT_RAM                               (0x1)
#define SFT_INTERRUPT_ECC_IRQ_STAT_RAM                               (0)
#define LSB_INTERRUPT_ECC_IRQ_STAT_RAM                               (15)
#define MSB_INTERRUPT_ECC_IRQ_STAT_RAM                               (15)

typedef struct {
  unsigned short dsi_crm_data_buf : 2;
  unsigned short dsi_pdcm_data_buf : 2;
  unsigned short dsi_cmd_buf : 2;
  unsigned short dsi_tdma : 2;
  unsigned short dsi_cmd : 2;
  unsigned short reserved : 2;
  unsigned short spi_cmd_buf : 1;
  unsigned short spi_cmd : 1;
  unsigned short spi_data : 1;
  unsigned short ram : 1;
} interrupt_ecc_irq_stat_bf;
		
typedef union {
  unsigned short val;
  interrupt_ecc_irq_stat_bf bf;
} interrupt_ecc_irq_stat_t;


/* Interrupt_ECC_IRQ_MASK */

#define MSK_INTERRUPT_ECC_IRQ_MASK_DSI_CRM_DATA_BUF                  (0x3)
#define SFT_INTERRUPT_ECC_IRQ_MASK_DSI_CRM_DATA_BUF                  (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_DSI_CRM_DATA_BUF                  (0)
#define MSB_INTERRUPT_ECC_IRQ_MASK_DSI_CRM_DATA_BUF                  (1)

#define MSK_INTERRUPT_ECC_IRQ_MASK_DSI_PDCM_DATA_BUF                 (0x3)
#define SFT_INTERRUPT_ECC_IRQ_MASK_DSI_PDCM_DATA_BUF                 (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_DSI_PDCM_DATA_BUF                 (2)
#define MSB_INTERRUPT_ECC_IRQ_MASK_DSI_PDCM_DATA_BUF                 (3)

#define MSK_INTERRUPT_ECC_IRQ_MASK_DSI_CMD_BUF                       (0x3)
#define SFT_INTERRUPT_ECC_IRQ_MASK_DSI_CMD_BUF                       (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_DSI_CMD_BUF                       (4)
#define MSB_INTERRUPT_ECC_IRQ_MASK_DSI_CMD_BUF                       (5)

#define MSK_INTERRUPT_ECC_IRQ_MASK_DSI_TDMA                          (0x3)
#define SFT_INTERRUPT_ECC_IRQ_MASK_DSI_TDMA                          (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_DSI_TDMA                          (6)
#define MSB_INTERRUPT_ECC_IRQ_MASK_DSI_TDMA                          (7)

#define MSK_INTERRUPT_ECC_IRQ_MASK_DSI_CMD                           (0x3)
#define SFT_INTERRUPT_ECC_IRQ_MASK_DSI_CMD                           (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_DSI_CMD                           (8)
#define MSB_INTERRUPT_ECC_IRQ_MASK_DSI_CMD                           (9)

#define BIT_INTERRUPT_ECC_IRQ_MASK_SPI_CMD_BUF                       (0)#define MSK_INTERRUPT_ECC_IRQ_MASK_SPI_CMD_BUF                       (0x1)
#define SFT_INTERRUPT_ECC_IRQ_MASK_SPI_CMD_BUF                       (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_SPI_CMD_BUF                       (12)
#define MSB_INTERRUPT_ECC_IRQ_MASK_SPI_CMD_BUF                       (12)

#define BIT_INTERRUPT_ECC_IRQ_MASK_SPI_CMD                           (0)#define MSK_INTERRUPT_ECC_IRQ_MASK_SPI_CMD                           (0x1)
#define SFT_INTERRUPT_ECC_IRQ_MASK_SPI_CMD                           (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_SPI_CMD                           (13)
#define MSB_INTERRUPT_ECC_IRQ_MASK_SPI_CMD                           (13)

#define BIT_INTERRUPT_ECC_IRQ_MASK_SPI_DATA                          (0)#define MSK_INTERRUPT_ECC_IRQ_MASK_SPI_DATA                          (0x1)
#define SFT_INTERRUPT_ECC_IRQ_MASK_SPI_DATA                          (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_SPI_DATA                          (14)
#define MSB_INTERRUPT_ECC_IRQ_MASK_SPI_DATA                          (14)

#define BIT_INTERRUPT_ECC_IRQ_MASK_RAM                               (0)#define MSK_INTERRUPT_ECC_IRQ_MASK_RAM                               (0x1)
#define SFT_INTERRUPT_ECC_IRQ_MASK_RAM                               (0)
#define LSB_INTERRUPT_ECC_IRQ_MASK_RAM                               (15)
#define MSB_INTERRUPT_ECC_IRQ_MASK_RAM                               (15)

typedef struct {
  unsigned short dsi_crm_data_buf : 2;
  unsigned short dsi_pdcm_data_buf : 2;
  unsigned short dsi_cmd_buf : 2;
  unsigned short dsi_tdma : 2;
  unsigned short dsi_cmd : 2;
  unsigned short reserved : 2;
  unsigned short spi_cmd_buf : 1;
  unsigned short spi_cmd : 1;
  unsigned short spi_data : 1;
  unsigned short ram : 1;
} interrupt_ecc_irq_mask_bf;
		
typedef union {
  unsigned short val;
  interrupt_ecc_irq_mask_bf bf;
} interrupt_ecc_irq_mask_t;


/* Interrupt_ECC_CORR_IRQ_STAT */

#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CRM_DATA_BUF             (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CRM_DATA_BUF             (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CRM_DATA_BUF             (0)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CRM_DATA_BUF             (1)

#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_PDCM_DATA_BUF            (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_PDCM_DATA_BUF            (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_PDCM_DATA_BUF            (2)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_PDCM_DATA_BUF            (3)

#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD_BUF                  (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD_BUF                  (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD_BUF                  (4)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD_BUF                  (5)

#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_TDMA                     (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_TDMA                     (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_TDMA                     (6)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_TDMA                     (7)

#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD                      (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD                      (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD                      (8)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_DSI_CMD                      (9)

#define BIT_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD_BUF                  (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD_BUF                  (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD_BUF                  (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD_BUF                  (12)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD_BUF                  (12)

#define BIT_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD                      (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD                      (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD                      (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD                      (13)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_CMD                      (13)

#define BIT_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_DATA                     (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_DATA                     (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_DATA                     (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_DATA                     (14)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_SPI_DATA                     (14)

#define BIT_INTERRUPT_ECC_CORR_IRQ_STAT_RAM                          (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_STAT_RAM                          (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_STAT_RAM                          (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT_RAM                          (15)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT_RAM                          (15)

typedef struct {
  unsigned short dsi_crm_data_buf : 2;
  unsigned short dsi_pdcm_data_buf : 2;
  unsigned short dsi_cmd_buf : 2;
  unsigned short dsi_tdma : 2;
  unsigned short dsi_cmd : 2;
  unsigned short reserved : 2;
  unsigned short spi_cmd_buf : 1;
  unsigned short spi_cmd : 1;
  unsigned short spi_data : 1;
  unsigned short ram : 1;
} interrupt_ecc_corr_irq_stat_bf;
		
typedef union {
  unsigned short val;
  interrupt_ecc_corr_irq_stat_bf bf;
} interrupt_ecc_corr_irq_stat_t;


/* Interrupt_ECC_CORR_IRQ_MASK */

#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CRM_DATA_BUF             (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CRM_DATA_BUF             (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CRM_DATA_BUF             (0)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CRM_DATA_BUF             (1)

#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_PDCM_DATA_BUF            (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_PDCM_DATA_BUF            (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_PDCM_DATA_BUF            (2)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_PDCM_DATA_BUF            (3)

#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD_BUF                  (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD_BUF                  (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD_BUF                  (4)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD_BUF                  (5)

#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_TDMA                     (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_TDMA                     (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_TDMA                     (6)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_TDMA                     (7)

#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD                      (0x3)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD                      (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD                      (8)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_DSI_CMD                      (9)

#define BIT_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD_BUF                  (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD_BUF                  (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD_BUF                  (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD_BUF                  (12)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD_BUF                  (12)

#define BIT_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD                      (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD                      (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD                      (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD                      (13)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_CMD                      (13)

#define BIT_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_DATA                     (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_DATA                     (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_DATA                     (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_DATA                     (14)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_SPI_DATA                     (14)

#define BIT_INTERRUPT_ECC_CORR_IRQ_MASK_RAM                          (0)#define MSK_INTERRUPT_ECC_CORR_IRQ_MASK_RAM                          (0x1)
#define SFT_INTERRUPT_ECC_CORR_IRQ_MASK_RAM                          (0)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK_RAM                          (15)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK_RAM                          (15)

typedef struct {
  unsigned short dsi_crm_data_buf : 2;
  unsigned short dsi_pdcm_data_buf : 2;
  unsigned short dsi_cmd_buf : 2;
  unsigned short dsi_tdma : 2;
  unsigned short dsi_cmd : 2;
  unsigned short reserved : 2;
  unsigned short spi_cmd_buf : 1;
  unsigned short spi_cmd : 1;
  unsigned short spi_data : 1;
  unsigned short ram : 1;
} interrupt_ecc_corr_irq_mask_bf;
		
typedef union {
  unsigned short val;
  interrupt_ecc_corr_irq_mask_bf bf;
} interrupt_ecc_corr_irq_mask_t;



typedef struct {
  interrupt_irq_stat_t                                               irq_stat;
  interrupt_irq_mask_t                                               irq_mask;
  interrupt_ecc_irq_stat_t                                           ecc_irq_stat;
  interrupt_ecc_irq_mask_t                                           ecc_irq_mask;
  interrupt_ecc_corr_irq_stat_t                                      ecc_corr_irq_stat;
  interrupt_ecc_corr_irq_mask_t                                      ecc_corr_irq_mask;
} interrupt_t;

typedef union {
  unsigned short a[sizeof(interrupt_t)/sizeof(unsigned short)];
  interrupt_t s;
} interrupt_u_t;


#define ADDR_INTERRUPT_IRQ_STAT                                      (0x50U)
#define A_INTERRUPT_IRQ_STAT(ba)                                     ((ba) + ADDR_INTERRUPT_IRQ_STAT)
#define R_INTERRUPT_IRQ_STAT(ba)                                     (*(volatile unsigned short *)((unsigned int)A_INTERRUPT_IRQ_STAT(ba)))
#define RES_INTERRUPT_IRQ_STAT                                       (0x0004U)
#define MSB_INTERRUPT_IRQ_STAT                                       (15)
#define LSB_INTERRUPT_IRQ_STAT                                       (0)
#define VBMASK_INTERRUPT_IRQ_STAT                                    (0x1e7fU)
#define ROMASK_INTERRUPT_IRQ_STAT                                    (0xeff8U)
#define AADDR_INTERRUPT_IRQ_STAT                                     (BASE_ADDR_INTERRUPT + ADDR_INTERRUPT_IRQ_STAT)
#define REG_INTERRUPT_IRQ_STAT                                       (*(volatile unsigned short *)((unsigned int)AADDR_INTERRUPT_IRQ_STAT))

#define ADDR_INTERRUPT_IRQ_MASK                                      (0x51U)
#define A_INTERRUPT_IRQ_MASK(ba)                                     ((ba) + ADDR_INTERRUPT_IRQ_MASK)
#define R_INTERRUPT_IRQ_MASK(ba)                                     (*(volatile unsigned short *)((unsigned int)A_INTERRUPT_IRQ_MASK(ba)))
#define RES_INTERRUPT_IRQ_MASK                                       (0x167fU)
#define MSB_INTERRUPT_IRQ_MASK                                       (12)
#define LSB_INTERRUPT_IRQ_MASK                                       (0)
#define VBMASK_INTERRUPT_IRQ_MASK                                    (0x1e7fU)
#define ROMASK_INTERRUPT_IRQ_MASK                                    (0x0180U)
#define AADDR_INTERRUPT_IRQ_MASK                                     (BASE_ADDR_INTERRUPT + ADDR_INTERRUPT_IRQ_MASK)
#define REG_INTERRUPT_IRQ_MASK                                       (*(volatile unsigned short *)((unsigned int)AADDR_INTERRUPT_IRQ_MASK))

#define ADDR_INTERRUPT_ECC_IRQ_STAT                                  (0x52U)
#define A_INTERRUPT_ECC_IRQ_STAT(ba)                                 ((ba) + ADDR_INTERRUPT_ECC_IRQ_STAT)
#define R_INTERRUPT_ECC_IRQ_STAT(ba)                                 (*(volatile unsigned short *)((unsigned int)A_INTERRUPT_ECC_IRQ_STAT(ba)))
#define RES_INTERRUPT_ECC_IRQ_STAT                                   (0x0000U)
#define MSB_INTERRUPT_ECC_IRQ_STAT                                   (15)
#define LSB_INTERRUPT_ECC_IRQ_STAT                                   (0)
#define VBMASK_INTERRUPT_ECC_IRQ_STAT                                (0xf3ffU)
#define ROMASK_INTERRUPT_ECC_IRQ_STAT                                (0x0c00U)
#define AADDR_INTERRUPT_ECC_IRQ_STAT                                 (BASE_ADDR_INTERRUPT + ADDR_INTERRUPT_ECC_IRQ_STAT)
#define REG_INTERRUPT_ECC_IRQ_STAT                                   (*(volatile unsigned short *)((unsigned int)AADDR_INTERRUPT_ECC_IRQ_STAT))

#define ADDR_INTERRUPT_ECC_IRQ_MASK                                  (0x53U)
#define A_INTERRUPT_ECC_IRQ_MASK(ba)                                 ((ba) + ADDR_INTERRUPT_ECC_IRQ_MASK)
#define R_INTERRUPT_ECC_IRQ_MASK(ba)                                 (*(volatile unsigned short *)((unsigned int)A_INTERRUPT_ECC_IRQ_MASK(ba)))
#define RES_INTERRUPT_ECC_IRQ_MASK                                   (0xf3ffU)
#define MSB_INTERRUPT_ECC_IRQ_MASK                                   (15)
#define LSB_INTERRUPT_ECC_IRQ_MASK                                   (0)
#define VBMASK_INTERRUPT_ECC_IRQ_MASK                                (0xf3ffU)
#define ROMASK_INTERRUPT_ECC_IRQ_MASK                                (0x0c00U)
#define AADDR_INTERRUPT_ECC_IRQ_MASK                                 (BASE_ADDR_INTERRUPT + ADDR_INTERRUPT_ECC_IRQ_MASK)
#define REG_INTERRUPT_ECC_IRQ_MASK                                   (*(volatile unsigned short *)((unsigned int)AADDR_INTERRUPT_ECC_IRQ_MASK))

#define ADDR_INTERRUPT_ECC_CORR_IRQ_STAT                             (0x54U)
#define A_INTERRUPT_ECC_CORR_IRQ_STAT(ba)                            ((ba) + ADDR_INTERRUPT_ECC_CORR_IRQ_STAT)
#define R_INTERRUPT_ECC_CORR_IRQ_STAT(ba)                            (*(volatile unsigned short *)((unsigned int)A_INTERRUPT_ECC_CORR_IRQ_STAT(ba)))
#define RES_INTERRUPT_ECC_CORR_IRQ_STAT                              (0x0000U)
#define MSB_INTERRUPT_ECC_CORR_IRQ_STAT                              (15)
#define LSB_INTERRUPT_ECC_CORR_IRQ_STAT                              (0)
#define VBMASK_INTERRUPT_ECC_CORR_IRQ_STAT                           (0xf3ffU)
#define ROMASK_INTERRUPT_ECC_CORR_IRQ_STAT                           (0x0c00U)
#define AADDR_INTERRUPT_ECC_CORR_IRQ_STAT                            (BASE_ADDR_INTERRUPT + ADDR_INTERRUPT_ECC_CORR_IRQ_STAT)
#define REG_INTERRUPT_ECC_CORR_IRQ_STAT                              (*(volatile unsigned short *)((unsigned int)AADDR_INTERRUPT_ECC_CORR_IRQ_STAT))

#define ADDR_INTERRUPT_ECC_CORR_IRQ_MASK                             (0x55U)
#define A_INTERRUPT_ECC_CORR_IRQ_MASK(ba)                            ((ba) + ADDR_INTERRUPT_ECC_CORR_IRQ_MASK)
#define R_INTERRUPT_ECC_CORR_IRQ_MASK(ba)                            (*(volatile unsigned short *)((unsigned int)A_INTERRUPT_ECC_CORR_IRQ_MASK(ba)))
#define RES_INTERRUPT_ECC_CORR_IRQ_MASK                              (0xf3ffU)
#define MSB_INTERRUPT_ECC_CORR_IRQ_MASK                              (15)
#define LSB_INTERRUPT_ECC_CORR_IRQ_MASK                              (0)
#define VBMASK_INTERRUPT_ECC_CORR_IRQ_MASK                           (0xf3ffU)
#define ROMASK_INTERRUPT_ECC_CORR_IRQ_MASK                           (0x0c00U)
#define AADDR_INTERRUPT_ECC_CORR_IRQ_MASK                            (BASE_ADDR_INTERRUPT + ADDR_INTERRUPT_ECC_CORR_IRQ_MASK)
#define REG_INTERRUPT_ECC_CORR_IRQ_MASK                              (*(volatile unsigned short *)((unsigned int)AADDR_INTERRUPT_ECC_CORR_IRQ_MASK))

 


// Instance base addresses

#ifndef BASE_ADDR_Buffer_IRQs 
#define BASE_ADDR_Buffer_IRQs 0x0000U
#define SIZE_Buffer_IRQs 0x0070U
#endif

// Register bit field definitions
	 
/* Buffer_IRQs_BUF_IRQ_STAT */

#define MSK_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CRM_FE                      (0x3)
#define SFT_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CRM_FE                      (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CRM_FE                      (0)
#define MSB_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CRM_FE                      (1)

#define MSK_BUFFER_IRQS_BUF_IRQ_STAT_DSI_PDCM_FE                     (0x3)
#define SFT_BUFFER_IRQS_BUF_IRQ_STAT_DSI_PDCM_FE                     (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_STAT_DSI_PDCM_FE                     (2)
#define MSB_BUFFER_IRQS_BUF_IRQ_STAT_DSI_PDCM_FE                     (3)

#define MSK_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CMD_FE                      (0x3)
#define SFT_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CMD_FE                      (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CMD_FE                      (4)
#define MSB_BUFFER_IRQS_BUF_IRQ_STAT_DSI_CMD_FE                      (5)

#define BIT_BUFFER_IRQS_BUF_IRQ_STAT_SPI_CMD_FE                      (0)#define MSK_BUFFER_IRQS_BUF_IRQ_STAT_SPI_CMD_FE                      (0x1)
#define SFT_BUFFER_IRQS_BUF_IRQ_STAT_SPI_CMD_FE                      (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_STAT_SPI_CMD_FE                      (6)
#define MSB_BUFFER_IRQS_BUF_IRQ_STAT_SPI_CMD_FE                      (6)

typedef struct {
  unsigned short dsi_crm_fe : 2;
  unsigned short dsi_pdcm_fe : 2;
  unsigned short dsi_cmd_fe : 2;
  unsigned short spi_cmd_fe : 1;
  unsigned short reserved : 9;
} buffer_irqs_buf_irq_stat_bf;
		
typedef union {
  unsigned short val;
  buffer_irqs_buf_irq_stat_bf bf;
} buffer_irqs_buf_irq_stat_t;


/* Buffer_IRQs_BUF_IRQ_MASK */

#define MSK_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CRM_FE                      (0x3)
#define SFT_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CRM_FE                      (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CRM_FE                      (0)
#define MSB_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CRM_FE                      (1)

#define MSK_BUFFER_IRQS_BUF_IRQ_MASK_DSI_PDCM_FE                     (0x3)
#define SFT_BUFFER_IRQS_BUF_IRQ_MASK_DSI_PDCM_FE                     (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_MASK_DSI_PDCM_FE                     (2)
#define MSB_BUFFER_IRQS_BUF_IRQ_MASK_DSI_PDCM_FE                     (3)

#define MSK_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CMD_FE                      (0x3)
#define SFT_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CMD_FE                      (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CMD_FE                      (4)
#define MSB_BUFFER_IRQS_BUF_IRQ_MASK_DSI_CMD_FE                      (5)

#define BIT_BUFFER_IRQS_BUF_IRQ_MASK_SPI_CMD_FE                      (0)#define MSK_BUFFER_IRQS_BUF_IRQ_MASK_SPI_CMD_FE                      (0x1)
#define SFT_BUFFER_IRQS_BUF_IRQ_MASK_SPI_CMD_FE                      (0)
#define LSB_BUFFER_IRQS_BUF_IRQ_MASK_SPI_CMD_FE                      (6)
#define MSB_BUFFER_IRQS_BUF_IRQ_MASK_SPI_CMD_FE                      (6)

typedef struct {
  unsigned short dsi_crm_fe : 2;
  unsigned short dsi_pdcm_fe : 2;
  unsigned short dsi_cmd_fe : 2;
  unsigned short spi_cmd_fe : 1;
  unsigned short reserved : 9;
} buffer_irqs_buf_irq_mask_bf;
		
typedef union {
  unsigned short val;
  buffer_irqs_buf_irq_mask_bf bf;
} buffer_irqs_buf_irq_mask_t;


/* Buffer_IRQs_BUF_FILL_WARN */

#define MSK_BUFFER_IRQS_BUF_FILL_WARN_DSI_CRM_FW                     (0x3)
#define SFT_BUFFER_IRQS_BUF_FILL_WARN_DSI_CRM_FW                     (0)
#define LSB_BUFFER_IRQS_BUF_FILL_WARN_DSI_CRM_FW                     (0)
#define MSB_BUFFER_IRQS_BUF_FILL_WARN_DSI_CRM_FW                     (1)

#define MSK_BUFFER_IRQS_BUF_FILL_WARN_DSI_PDCM_FW                    (0x3)
#define SFT_BUFFER_IRQS_BUF_FILL_WARN_DSI_PDCM_FW                    (0)
#define LSB_BUFFER_IRQS_BUF_FILL_WARN_DSI_PDCM_FW                    (2)
#define MSB_BUFFER_IRQS_BUF_FILL_WARN_DSI_PDCM_FW                    (3)

#define MSK_BUFFER_IRQS_BUF_FILL_WARN_DSI_CMD_FW                     (0x3)
#define SFT_BUFFER_IRQS_BUF_FILL_WARN_DSI_CMD_FW                     (0)
#define LSB_BUFFER_IRQS_BUF_FILL_WARN_DSI_CMD_FW                     (4)
#define MSB_BUFFER_IRQS_BUF_FILL_WARN_DSI_CMD_FW                     (5)

#define BIT_BUFFER_IRQS_BUF_FILL_WARN_SPI_CMD_FW                     (0)#define MSK_BUFFER_IRQS_BUF_FILL_WARN_SPI_CMD_FW                     (0x1)
#define SFT_BUFFER_IRQS_BUF_FILL_WARN_SPI_CMD_FW                     (0)
#define LSB_BUFFER_IRQS_BUF_FILL_WARN_SPI_CMD_FW                     (6)
#define MSB_BUFFER_IRQS_BUF_FILL_WARN_SPI_CMD_FW                     (6)

typedef struct {
  unsigned short dsi_crm_fw : 2;
  unsigned short dsi_pdcm_fw : 2;
  unsigned short dsi_cmd_fw : 2;
  unsigned short spi_cmd_fw : 1;
} buffer_irqs_buf_fill_warn_bf;
		
typedef union {
  unsigned short val;
  buffer_irqs_buf_fill_warn_bf bf;
} buffer_irqs_buf_fill_warn_t;



typedef struct {
  buffer_irqs_buf_irq_stat_t                                         buf_irq_stat;
  buffer_irqs_buf_irq_mask_t                                         buf_irq_mask;
  buffer_irqs_buf_fill_warn_t                                        buf_fill_warn;
} buffer_irqs_t;

typedef union {
  unsigned short a[sizeof(buffer_irqs_t)/sizeof(unsigned short)];
  buffer_irqs_t s;
} buffer_irqs_u_t;


#define ADDR_BUFFER_IRQS_BUF_IRQ_STAT                                (0x61U)
#define A_BUFFER_IRQS_BUF_IRQ_STAT(ba)                               ((ba) + ADDR_BUFFER_IRQS_BUF_IRQ_STAT)
#define R_BUFFER_IRQS_BUF_IRQ_STAT(ba)                               (*(volatile unsigned short *)((unsigned int)A_BUFFER_IRQS_BUF_IRQ_STAT(ba)))
#define RES_BUFFER_IRQS_BUF_IRQ_STAT                                 (0x0000U)
#define MSB_BUFFER_IRQS_BUF_IRQ_STAT                                 (15)
#define LSB_BUFFER_IRQS_BUF_IRQ_STAT                                 (0)
#define VBMASK_BUFFER_IRQS_BUF_IRQ_STAT                              (0x007fU)
#define ROMASK_BUFFER_IRQS_BUF_IRQ_STAT                              (0xff80U)
#define AADDR_BUFFER_IRQS_BUF_IRQ_STAT                               (BASE_ADDR_BUFFER_IRQS + ADDR_BUFFER_IRQS_BUF_IRQ_STAT)
#define REG_BUFFER_IRQS_BUF_IRQ_STAT                                 (*(volatile unsigned short *)((unsigned int)AADDR_BUFFER_IRQS_BUF_IRQ_STAT))

#define ADDR_BUFFER_IRQS_BUF_IRQ_MASK                                (0x62U)
#define A_BUFFER_IRQS_BUF_IRQ_MASK(ba)                               ((ba) + ADDR_BUFFER_IRQS_BUF_IRQ_MASK)
#define R_BUFFER_IRQS_BUF_IRQ_MASK(ba)                               (*(volatile unsigned short *)((unsigned int)A_BUFFER_IRQS_BUF_IRQ_MASK(ba)))
#define RES_BUFFER_IRQS_BUF_IRQ_MASK                                 (0x007fU)
#define MSB_BUFFER_IRQS_BUF_IRQ_MASK                                 (15)
#define LSB_BUFFER_IRQS_BUF_IRQ_MASK                                 (0)
#define VBMASK_BUFFER_IRQS_BUF_IRQ_MASK                              (0x007fU)
#define ROMASK_BUFFER_IRQS_BUF_IRQ_MASK                              (0xff80U)
#define AADDR_BUFFER_IRQS_BUF_IRQ_MASK                               (BASE_ADDR_BUFFER_IRQS + ADDR_BUFFER_IRQS_BUF_IRQ_MASK)
#define REG_BUFFER_IRQS_BUF_IRQ_MASK                                 (*(volatile unsigned short *)((unsigned int)AADDR_BUFFER_IRQS_BUF_IRQ_MASK))

#define ADDR_BUFFER_IRQS_BUF_FILL_WARN                               (0x63U)
#define A_BUFFER_IRQS_BUF_FILL_WARN(ba)                              ((ba) + ADDR_BUFFER_IRQS_BUF_FILL_WARN)
#define R_BUFFER_IRQS_BUF_FILL_WARN(ba)                              (*(volatile unsigned short *)((unsigned int)A_BUFFER_IRQS_BUF_FILL_WARN(ba)))
#define RES_BUFFER_IRQS_BUF_FILL_WARN                                (0x0000U)
#define MSB_BUFFER_IRQS_BUF_FILL_WARN                                (6)
#define LSB_BUFFER_IRQS_BUF_FILL_WARN                                (0)
#define VBMASK_BUFFER_IRQS_BUF_FILL_WARN                             (0x007fU)
#define ROMASK_BUFFER_IRQS_BUF_FILL_WARN                             (0x007fU)
#define AADDR_BUFFER_IRQS_BUF_FILL_WARN                              (BASE_ADDR_BUFFER_IRQS + ADDR_BUFFER_IRQS_BUF_FILL_WARN)
#define REG_BUFFER_IRQS_BUF_FILL_WARN                                (*(volatile unsigned short *)((unsigned int)AADDR_BUFFER_IRQS_BUF_FILL_WARN))

 


// Instance base addresses

#ifndef BASE_ADDR_SPI 
#define BASE_ADDR_SPI 0x0000U
#define SIZE_SPI 0x0090U
#endif

// Register bit field definitions
	 
/* SPI_SPI_IRQ_STAT */

#define BIT_SPI_SPI_IRQ_STAT_CMD_INC                                 (0)#define MSK_SPI_SPI_IRQ_STAT_CMD_INC                                 (0x1)
#define SFT_SPI_SPI_IRQ_STAT_CMD_INC                                 (0)
#define LSB_SPI_SPI_IRQ_STAT_CMD_INC                                 (0)
#define MSB_SPI_SPI_IRQ_STAT_CMD_INC                                 (0)

#define BIT_SPI_SPI_IRQ_STAT_CRC_ERR                                 (0)#define MSK_SPI_SPI_IRQ_STAT_CRC_ERR                                 (0x1)
#define SFT_SPI_SPI_IRQ_STAT_CRC_ERR                                 (0)
#define LSB_SPI_SPI_IRQ_STAT_CRC_ERR                                 (1)
#define MSB_SPI_SPI_IRQ_STAT_CRC_ERR                                 (1)

#define BIT_SPI_SPI_IRQ_STAT_ALI_ERR                                 (0)#define MSK_SPI_SPI_IRQ_STAT_ALI_ERR                                 (0x1)
#define SFT_SPI_SPI_IRQ_STAT_ALI_ERR                                 (0)
#define LSB_SPI_SPI_IRQ_STAT_ALI_ERR                                 (2)
#define MSB_SPI_SPI_IRQ_STAT_ALI_ERR                                 (2)

#define BIT_SPI_SPI_IRQ_STAT_HW_FAIL                                 (0)#define MSK_SPI_SPI_IRQ_STAT_HW_FAIL                                 (0x1)
#define SFT_SPI_SPI_IRQ_STAT_HW_FAIL                                 (0)
#define LSB_SPI_SPI_IRQ_STAT_HW_FAIL                                 (3)
#define MSB_SPI_SPI_IRQ_STAT_HW_FAIL                                 (3)

#define BIT_SPI_SPI_IRQ_STAT_CMD_IGN                                 (0)#define MSK_SPI_SPI_IRQ_STAT_CMD_IGN                                 (0x1)
#define SFT_SPI_SPI_IRQ_STAT_CMD_IGN                                 (0)
#define LSB_SPI_SPI_IRQ_STAT_CMD_IGN                                 (4)
#define MSB_SPI_SPI_IRQ_STAT_CMD_IGN                                 (4)

typedef struct {
  unsigned short cmd_inc : 1;
  unsigned short crc_err : 1;
  unsigned short ali_err : 1;
  unsigned short hw_fail : 1;
  unsigned short cmd_ign : 1;
  unsigned short reserved : 11;
} spi_spi_irq_stat_bf;
		
typedef union {
  unsigned short val;
  spi_spi_irq_stat_bf bf;
} spi_spi_irq_stat_t;


/* SPI_SPI_IRQ_MASK */

#define BIT_SPI_SPI_IRQ_MASK_CMD_INC                                 (0)#define MSK_SPI_SPI_IRQ_MASK_CMD_INC                                 (0x1)
#define SFT_SPI_SPI_IRQ_MASK_CMD_INC                                 (0)
#define LSB_SPI_SPI_IRQ_MASK_CMD_INC                                 (0)
#define MSB_SPI_SPI_IRQ_MASK_CMD_INC                                 (0)

#define BIT_SPI_SPI_IRQ_MASK_CRC_ERR                                 (0)#define MSK_SPI_SPI_IRQ_MASK_CRC_ERR                                 (0x1)
#define SFT_SPI_SPI_IRQ_MASK_CRC_ERR                                 (0)
#define LSB_SPI_SPI_IRQ_MASK_CRC_ERR                                 (1)
#define MSB_SPI_SPI_IRQ_MASK_CRC_ERR                                 (1)

#define BIT_SPI_SPI_IRQ_MASK_ALI_ERR                                 (0)#define MSK_SPI_SPI_IRQ_MASK_ALI_ERR                                 (0x1)
#define SFT_SPI_SPI_IRQ_MASK_ALI_ERR                                 (0)
#define LSB_SPI_SPI_IRQ_MASK_ALI_ERR                                 (2)
#define MSB_SPI_SPI_IRQ_MASK_ALI_ERR                                 (2)

#define BIT_SPI_SPI_IRQ_MASK_HW_FAIL                                 (0)#define MSK_SPI_SPI_IRQ_MASK_HW_FAIL                                 (0x1)
#define SFT_SPI_SPI_IRQ_MASK_HW_FAIL                                 (0)
#define LSB_SPI_SPI_IRQ_MASK_HW_FAIL                                 (3)
#define MSB_SPI_SPI_IRQ_MASK_HW_FAIL                                 (3)

#define BIT_SPI_SPI_IRQ_MASK_CMD_IGN                                 (0)#define MSK_SPI_SPI_IRQ_MASK_CMD_IGN                                 (0x1)
#define SFT_SPI_SPI_IRQ_MASK_CMD_IGN                                 (0)
#define LSB_SPI_SPI_IRQ_MASK_CMD_IGN                                 (4)
#define MSB_SPI_SPI_IRQ_MASK_CMD_IGN                                 (4)

typedef struct {
  unsigned short cmd_inc : 1;
  unsigned short crc_err : 1;
  unsigned short ali_err : 1;
  unsigned short hw_fail : 1;
  unsigned short cmd_ign : 1;
  unsigned short reserved : 11;
} spi_spi_irq_mask_bf;
		
typedef union {
  unsigned short val;
  spi_spi_irq_mask_bf bf;
} spi_spi_irq_mask_t;


/* SPI_STATUS_WORD */

#define MSK_SPI_STATUS_WORD_CR                                       (0x3)
#define SFT_SPI_STATUS_WORD_CR                                       (0)
#define LSB_SPI_STATUS_WORD_CR                                       (0)
#define MSB_SPI_STATUS_WORD_CR                                       (1)

#define MSK_SPI_STATUS_WORD_PD                                       (0x3)
#define SFT_SPI_STATUS_WORD_PD                                       (0)
#define LSB_SPI_STATUS_WORD_PD                                       (2)
#define MSB_SPI_STATUS_WORD_PD                                       (3)

#define MSK_SPI_STATUS_WORD_NT                                       (0x3)
#define SFT_SPI_STATUS_WORD_NT                                       (0)
#define LSB_SPI_STATUS_WORD_NT                                       (10)
#define MSB_SPI_STATUS_WORD_NT                                       (11)

#define BIT_SPI_STATUS_WORD_CRC                                      (0)#define MSK_SPI_STATUS_WORD_CRC                                      (0x1)
#define SFT_SPI_STATUS_WORD_CRC                                      (0)
#define LSB_SPI_STATUS_WORD_CRC                                      (12)
#define MSB_SPI_STATUS_WORD_CRC                                      (12)

#define BIT_SPI_STATUS_WORD_SCE                                      (0)#define MSK_SPI_STATUS_WORD_SCE                                      (0x1)
#define SFT_SPI_STATUS_WORD_SCE                                      (0)
#define LSB_SPI_STATUS_WORD_SCE                                      (13)
#define MSB_SPI_STATUS_WORD_SCE                                      (13)

#define BIT_SPI_STATUS_WORD_BF                                       (0)#define MSK_SPI_STATUS_WORD_BF                                       (0x1)
#define SFT_SPI_STATUS_WORD_BF                                       (0)
#define LSB_SPI_STATUS_WORD_BF                                       (14)
#define MSB_SPI_STATUS_WORD_BF                                       (14)

#define BIT_SPI_STATUS_WORD_HE                                       (0)#define MSK_SPI_STATUS_WORD_HE                                       (0x1)
#define SFT_SPI_STATUS_WORD_HE                                       (0)
#define LSB_SPI_STATUS_WORD_HE                                       (15)
#define MSB_SPI_STATUS_WORD_HE                                       (15)

typedef struct {
  unsigned short cr : 2;
  unsigned short pd : 2;
  unsigned short reserved : 6;
  unsigned short nt : 2;
  unsigned short crc : 1;
  unsigned short sce : 1;
  unsigned short bf : 1;
  unsigned short he : 1;
} spi_status_word_bf;
		
typedef union {
  unsigned short val;
  spi_status_word_bf bf;
} spi_status_word_t;



typedef struct {
  spi_spi_irq_stat_t                                                 spi_irq_stat;
  spi_spi_irq_mask_t                                                 spi_irq_mask;
  spi_status_word_t                                                  status_word;
} spi_t;

typedef union {
  unsigned short a[sizeof(spi_t)/sizeof(unsigned short)];
  spi_t s;
} spi_u_t;


#define ADDR_SPI_SPI_IRQ_STAT                                        (0x80U)
#define A_SPI_SPI_IRQ_STAT(ba)                                       ((ba) + ADDR_SPI_SPI_IRQ_STAT)
#define R_SPI_SPI_IRQ_STAT(ba)                                       (*(volatile unsigned short *)((unsigned int)A_SPI_SPI_IRQ_STAT(ba)))
#define RES_SPI_SPI_IRQ_STAT                                         (0x0000U)
#define MSB_SPI_SPI_IRQ_STAT                                         (15)
#define LSB_SPI_SPI_IRQ_STAT                                         (0)
#define VBMASK_SPI_SPI_IRQ_STAT                                      (0x001fU)
#define ROMASK_SPI_SPI_IRQ_STAT                                      (0xffe0U)
#define AADDR_SPI_SPI_IRQ_STAT                                       (BASE_ADDR_SPI + ADDR_SPI_SPI_IRQ_STAT)
#define REG_SPI_SPI_IRQ_STAT                                         (*(volatile unsigned short *)((unsigned int)AADDR_SPI_SPI_IRQ_STAT))

#define ADDR_SPI_SPI_IRQ_MASK                                        (0x81U)
#define A_SPI_SPI_IRQ_MASK(ba)                                       ((ba) + ADDR_SPI_SPI_IRQ_MASK)
#define R_SPI_SPI_IRQ_MASK(ba)                                       (*(volatile unsigned short *)((unsigned int)A_SPI_SPI_IRQ_MASK(ba)))
#define RES_SPI_SPI_IRQ_MASK                                         (0x001fU)
#define MSB_SPI_SPI_IRQ_MASK                                         (15)
#define LSB_SPI_SPI_IRQ_MASK                                         (0)
#define VBMASK_SPI_SPI_IRQ_MASK                                      (0x001fU)
#define ROMASK_SPI_SPI_IRQ_MASK                                      (0xffe0U)
#define AADDR_SPI_SPI_IRQ_MASK                                       (BASE_ADDR_SPI + ADDR_SPI_SPI_IRQ_MASK)
#define REG_SPI_SPI_IRQ_MASK                                         (*(volatile unsigned short *)((unsigned int)AADDR_SPI_SPI_IRQ_MASK))

#define ADDR_SPI_STATUS_WORD                                         (0x85U)
#define A_SPI_STATUS_WORD(ba)                                        ((ba) + ADDR_SPI_STATUS_WORD)
#define R_SPI_STATUS_WORD(ba)                                        (*(volatile unsigned short *)((unsigned int)A_SPI_STATUS_WORD(ba)))
#define RES_SPI_STATUS_WORD                                          (0x0c00U)
#define MSB_SPI_STATUS_WORD                                          (15)
#define LSB_SPI_STATUS_WORD                                          (0)
#define VBMASK_SPI_STATUS_WORD                                       (0xfc0fU)
#define ROMASK_SPI_STATUS_WORD                                       (0xffffU)
#define AADDR_SPI_STATUS_WORD                                        (BASE_ADDR_SPI + ADDR_SPI_STATUS_WORD)
#define REG_SPI_STATUS_WORD                                          (*(volatile unsigned short *)((unsigned int)AADDR_SPI_STATUS_WORD))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_common 
#define BASE_ADDR_DSI_common 0x0000U
#define SIZE_DSI_common 0x00a0U
#endif

// Register bit field definitions
	 
/* DSI_common_DSI_ENABLE */

#define MSK_DSI_COMMON_DSI_ENABLE_TRE                                (0x3)
#define SFT_DSI_COMMON_DSI_ENABLE_TRE                                (0)
#define LSB_DSI_COMMON_DSI_ENABLE_TRE                                (0)
#define MSB_DSI_COMMON_DSI_ENABLE_TRE                                (1)

typedef struct {
  unsigned short tre : 2;
} dsi_common_dsi_enable_bf;
		
typedef union {
  unsigned short val;
  dsi_common_dsi_enable_bf bf;
} dsi_common_dsi_enable_t;


/* DSI_common_DSI_CFG */

#define MSK_DSI_COMMON_DSI_CFG_CHIPTIME                              (0x3)
#define SFT_DSI_COMMON_DSI_CFG_CHIPTIME                              (0)
#define LSB_DSI_COMMON_DSI_CFG_CHIPTIME                              (0)
#define MSB_DSI_COMMON_DSI_CFG_CHIPTIME                              (1)

#define MSK_DSI_COMMON_DSI_CFG_BITTIME                               (0x3)
#define SFT_DSI_COMMON_DSI_CFG_BITTIME                               (0)
#define LSB_DSI_COMMON_DSI_CFG_BITTIME                               (2)
#define MSB_DSI_COMMON_DSI_CFG_BITTIME                               (3)

#define BIT_DSI_COMMON_DSI_CFG_CRC_EN                                (0)#define MSK_DSI_COMMON_DSI_CFG_CRC_EN                                (0x1)
#define SFT_DSI_COMMON_DSI_CFG_CRC_EN                                (0)
#define LSB_DSI_COMMON_DSI_CFG_CRC_EN                                (4)
#define MSB_DSI_COMMON_DSI_CFG_CRC_EN                                (4)

#define BIT_DSI_COMMON_DSI_CFG_SYNC_PDCM                             (0)#define MSK_DSI_COMMON_DSI_CFG_SYNC_PDCM                             (0x1)
#define SFT_DSI_COMMON_DSI_CFG_SYNC_PDCM                             (0)
#define LSB_DSI_COMMON_DSI_CFG_SYNC_PDCM                             (5)
#define MSB_DSI_COMMON_DSI_CFG_SYNC_PDCM                             (5)

#define BIT_DSI_COMMON_DSI_CFG_SYNC_MASTER                           (0)#define MSK_DSI_COMMON_DSI_CFG_SYNC_MASTER                           (0x1)
#define SFT_DSI_COMMON_DSI_CFG_SYNC_MASTER                           (0)
#define LSB_DSI_COMMON_DSI_CFG_SYNC_MASTER                           (6)
#define MSB_DSI_COMMON_DSI_CFG_SYNC_MASTER                           (6)

typedef struct {
  unsigned short chiptime : 2;
  unsigned short bittime : 2;
  unsigned short crc_en : 1;
  unsigned short sync_pdcm : 1;
  unsigned short sync_master : 1;
} dsi_common_dsi_cfg_bf;
		
typedef union {
  unsigned short val;
  dsi_common_dsi_cfg_bf bf;
} dsi_common_dsi_cfg_t;


/* DSI_common_DSI_TX_SHIFT */

#define MSK_DSI_COMMON_DSI_TX_SHIFT_SHIFT                            (0x7f)
#define SFT_DSI_COMMON_DSI_TX_SHIFT_SHIFT                            (0)
#define LSB_DSI_COMMON_DSI_TX_SHIFT_SHIFT                            (0)
#define MSB_DSI_COMMON_DSI_TX_SHIFT_SHIFT                            (6)

typedef struct {
  unsigned short shift : 7;
} dsi_common_dsi_tx_shift_bf;
		
typedef union {
  unsigned short val;
  dsi_common_dsi_tx_shift_bf bf;
} dsi_common_dsi_tx_shift_t;


/* DSI_common_SYNC_IDLE_REG */

#define MSK_DSI_COMMON_SYNC_IDLE_REG_DSI                             (0x3)
#define SFT_DSI_COMMON_SYNC_IDLE_REG_DSI                             (0)
#define LSB_DSI_COMMON_SYNC_IDLE_REG_DSI                             (0)
#define MSB_DSI_COMMON_SYNC_IDLE_REG_DSI                             (1)

#define BIT_DSI_COMMON_SYNC_IDLE_REG_PIN                             (0)#define MSK_DSI_COMMON_SYNC_IDLE_REG_PIN                             (0x1)
#define SFT_DSI_COMMON_SYNC_IDLE_REG_PIN                             (0)
#define LSB_DSI_COMMON_SYNC_IDLE_REG_PIN                             (15)
#define MSB_DSI_COMMON_SYNC_IDLE_REG_PIN                             (15)

typedef struct {
  unsigned short dsi : 2;
  unsigned short reserved : 13;
  unsigned short pin : 1;
} dsi_common_sync_idle_reg_bf;
		
typedef union {
  unsigned short val;
  dsi_common_sync_idle_reg_bf bf;
} dsi_common_sync_idle_reg_t;


/* DSI_common_CRM_TIME */

#define MSK_DSI_COMMON_CRM_TIME_TIME                                 (0x7ff)
#define SFT_DSI_COMMON_CRM_TIME_TIME                                 (0)
#define LSB_DSI_COMMON_CRM_TIME_TIME                                 (0)
#define MSB_DSI_COMMON_CRM_TIME_TIME                                 (10)

typedef struct {
  unsigned short time : 11;
  unsigned short reserved : 5;
} dsi_common_crm_time_bf;
		
typedef union {
  unsigned short val;
  dsi_common_crm_time_bf bf;
} dsi_common_crm_time_t;


/* DSI_common_CRM_TIME_NR */

#define MSK_DSI_COMMON_CRM_TIME_NR_TIME                              (0x7ff)
#define SFT_DSI_COMMON_CRM_TIME_NR_TIME                              (0)
#define LSB_DSI_COMMON_CRM_TIME_NR_TIME                              (0)
#define MSB_DSI_COMMON_CRM_TIME_NR_TIME                              (10)

typedef struct {
  unsigned short time : 11;
  unsigned short reserved : 5;
} dsi_common_crm_time_nr_bf;
		
typedef union {
  unsigned short val;
  dsi_common_crm_time_nr_bf bf;
} dsi_common_crm_time_nr_t;



typedef struct {
  dsi_common_dsi_enable_t                                            dsi_enable;
  dsi_common_dsi_cfg_t                                               dsi_cfg;
  dsi_common_dsi_tx_shift_t                                          dsi_tx_shift;
  dsi_common_sync_idle_reg_t                                         sync_idle_reg;
  dsi_common_crm_time_t                                              crm_time;
  dsi_common_crm_time_nr_t                                           crm_time_nr;
} dsi_common_t;

typedef union {
  unsigned short a[sizeof(dsi_common_t)/sizeof(unsigned short)];
  dsi_common_t s;
} dsi_common_u_t;


#define ADDR_DSI_COMMON_DSI_ENABLE                                   (0x91U)
#define A_DSI_COMMON_DSI_ENABLE(ba)                                  ((ba) + ADDR_DSI_COMMON_DSI_ENABLE)
#define R_DSI_COMMON_DSI_ENABLE(ba)                                  (*(volatile unsigned short *)((unsigned int)A_DSI_COMMON_DSI_ENABLE(ba)))
#define RES_DSI_COMMON_DSI_ENABLE                                    (0x0003U)
#define MSB_DSI_COMMON_DSI_ENABLE                                    (1)
#define LSB_DSI_COMMON_DSI_ENABLE                                    (0)
#define VBMASK_DSI_COMMON_DSI_ENABLE                                 (0x0003U)
#define ROMASK_DSI_COMMON_DSI_ENABLE                                 (0x0000U)
#define AADDR_DSI_COMMON_DSI_ENABLE                                  (BASE_ADDR_DSI_COMMON + ADDR_DSI_COMMON_DSI_ENABLE)
#define REG_DSI_COMMON_DSI_ENABLE                                    (*(volatile unsigned short *)((unsigned int)AADDR_DSI_COMMON_DSI_ENABLE))

#define ADDR_DSI_COMMON_DSI_CFG                                      (0x92U)
#define A_DSI_COMMON_DSI_CFG(ba)                                     ((ba) + ADDR_DSI_COMMON_DSI_CFG)
#define R_DSI_COMMON_DSI_CFG(ba)                                     (*(volatile unsigned short *)((unsigned int)A_DSI_COMMON_DSI_CFG(ba)))
#define RES_DSI_COMMON_DSI_CFG                                       (0x0031U)
#define MSB_DSI_COMMON_DSI_CFG                                       (6)
#define LSB_DSI_COMMON_DSI_CFG                                       (0)
#define VBMASK_DSI_COMMON_DSI_CFG                                    (0x007fU)
#define ROMASK_DSI_COMMON_DSI_CFG                                    (0x0000U)
#define AADDR_DSI_COMMON_DSI_CFG                                     (BASE_ADDR_DSI_COMMON + ADDR_DSI_COMMON_DSI_CFG)
#define REG_DSI_COMMON_DSI_CFG                                       (*(volatile unsigned short *)((unsigned int)AADDR_DSI_COMMON_DSI_CFG))

#define ADDR_DSI_COMMON_DSI_TX_SHIFT                                 (0x94U)
#define A_DSI_COMMON_DSI_TX_SHIFT(ba)                                ((ba) + ADDR_DSI_COMMON_DSI_TX_SHIFT)
#define R_DSI_COMMON_DSI_TX_SHIFT(ba)                                (*(volatile unsigned short *)((unsigned int)A_DSI_COMMON_DSI_TX_SHIFT(ba)))
#define RES_DSI_COMMON_DSI_TX_SHIFT                                  (0x0024U)
#define MSB_DSI_COMMON_DSI_TX_SHIFT                                  (6)
#define LSB_DSI_COMMON_DSI_TX_SHIFT                                  (0)
#define VBMASK_DSI_COMMON_DSI_TX_SHIFT                               (0x007fU)
#define ROMASK_DSI_COMMON_DSI_TX_SHIFT                               (0x0000U)
#define AADDR_DSI_COMMON_DSI_TX_SHIFT                                (BASE_ADDR_DSI_COMMON + ADDR_DSI_COMMON_DSI_TX_SHIFT)
#define REG_DSI_COMMON_DSI_TX_SHIFT                                  (*(volatile unsigned short *)((unsigned int)AADDR_DSI_COMMON_DSI_TX_SHIFT))

#define ADDR_DSI_COMMON_SYNC_IDLE_REG                                (0x95U)
#define A_DSI_COMMON_SYNC_IDLE_REG(ba)                               ((ba) + ADDR_DSI_COMMON_SYNC_IDLE_REG)
#define R_DSI_COMMON_SYNC_IDLE_REG(ba)                               (*(volatile unsigned short *)((unsigned int)A_DSI_COMMON_SYNC_IDLE_REG(ba)))
#define RES_DSI_COMMON_SYNC_IDLE_REG                                 (0x0000U)
#define MSB_DSI_COMMON_SYNC_IDLE_REG                                 (15)
#define LSB_DSI_COMMON_SYNC_IDLE_REG                                 (0)
#define VBMASK_DSI_COMMON_SYNC_IDLE_REG                              (0x8003U)
#define ROMASK_DSI_COMMON_SYNC_IDLE_REG                              (0xffffU)
#define AADDR_DSI_COMMON_SYNC_IDLE_REG                               (BASE_ADDR_DSI_COMMON + ADDR_DSI_COMMON_SYNC_IDLE_REG)
#define REG_DSI_COMMON_SYNC_IDLE_REG                                 (*(volatile unsigned short *)((unsigned int)AADDR_DSI_COMMON_SYNC_IDLE_REG))

#define ADDR_DSI_COMMON_CRM_TIME                                     (0x98U)
#define A_DSI_COMMON_CRM_TIME(ba)                                    ((ba) + ADDR_DSI_COMMON_CRM_TIME)
#define R_DSI_COMMON_CRM_TIME(ba)                                    (*(volatile unsigned short *)((unsigned int)A_DSI_COMMON_CRM_TIME(ba)))
#define RES_DSI_COMMON_CRM_TIME                                      (0x01c2U)
#define MSB_DSI_COMMON_CRM_TIME                                      (15)
#define LSB_DSI_COMMON_CRM_TIME                                      (0)
#define VBMASK_DSI_COMMON_CRM_TIME                                   (0x07ffU)
#define ROMASK_DSI_COMMON_CRM_TIME                                   (0xf800U)
#define AADDR_DSI_COMMON_CRM_TIME                                    (BASE_ADDR_DSI_COMMON + ADDR_DSI_COMMON_CRM_TIME)
#define REG_DSI_COMMON_CRM_TIME                                      (*(volatile unsigned short *)((unsigned int)AADDR_DSI_COMMON_CRM_TIME))

#define ADDR_DSI_COMMON_CRM_TIME_NR                                  (0x99U)
#define A_DSI_COMMON_CRM_TIME_NR(ba)                                 ((ba) + ADDR_DSI_COMMON_CRM_TIME_NR)
#define R_DSI_COMMON_CRM_TIME_NR(ba)                                 (*(volatile unsigned short *)((unsigned int)A_DSI_COMMON_CRM_TIME_NR(ba)))
#define RES_DSI_COMMON_CRM_TIME_NR                                   (0x012cU)
#define MSB_DSI_COMMON_CRM_TIME_NR                                   (15)
#define LSB_DSI_COMMON_CRM_TIME_NR                                   (0)
#define VBMASK_DSI_COMMON_CRM_TIME_NR                                (0x07ffU)
#define ROMASK_DSI_COMMON_CRM_TIME_NR                                (0xf800U)
#define AADDR_DSI_COMMON_CRM_TIME_NR                                 (BASE_ADDR_DSI_COMMON + ADDR_DSI_COMMON_CRM_TIME_NR)
#define REG_DSI_COMMON_CRM_TIME_NR                                   (*(volatile unsigned short *)((unsigned int)AADDR_DSI_COMMON_CRM_TIME_NR))

 


// Instance base addresses

#ifndef BASE_ADDR_RAM 
#define BASE_ADDR_RAM 0x0400U
#define SIZE_RAM 0x0c00U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_OTP_CTRL 
#define BASE_ADDR_OTP_CTRL 0x0000U
#define SIZE_OTP_CTRL 0x0074U
#endif

// Register bit field definitions
	 
/* OTP_CTRL_OTP_READ_ADDRESS */

#define MSK_OTP_CTRL_OTP_READ_ADDRESS_ADDR                           (0xfff)
#define SFT_OTP_CTRL_OTP_READ_ADDRESS_ADDR                           (0)
#define LSB_OTP_CTRL_OTP_READ_ADDRESS_ADDR                           (0)
#define MSB_OTP_CTRL_OTP_READ_ADDRESS_ADDR                           (11)

typedef struct {
  unsigned short addr : 12;
  unsigned short reserved : 4;
} otp_ctrl_otp_read_address_bf;
		
typedef union {
  unsigned short val;
  otp_ctrl_otp_read_address_bf bf;
} otp_ctrl_otp_read_address_t;


/* OTP_CTRL_OTP_READ_VALUE */

#define MSK_OTP_CTRL_OTP_READ_VALUE_VALUE                            (0xff)
#define SFT_OTP_CTRL_OTP_READ_VALUE_VALUE                            (0)
#define LSB_OTP_CTRL_OTP_READ_VALUE_VALUE                            (0)
#define MSB_OTP_CTRL_OTP_READ_VALUE_VALUE                            (7)

#define MSK_OTP_CTRL_OTP_READ_VALUE_ECC                              (0xf)
#define SFT_OTP_CTRL_OTP_READ_VALUE_ECC                              (0)
#define LSB_OTP_CTRL_OTP_READ_VALUE_ECC                              (8)
#define MSB_OTP_CTRL_OTP_READ_VALUE_ECC                              (11)

typedef struct {
  unsigned short value : 8;
  unsigned short ecc : 4;
  unsigned short reserved : 4;
} otp_ctrl_otp_read_value_bf;
		
typedef union {
  unsigned short val;
  otp_ctrl_otp_read_value_bf bf;
} otp_ctrl_otp_read_value_t;


/* OTP_CTRL_OTP_READ_STATUS */

#define MSK_OTP_CTRL_OTP_READ_STATUS_STATUS                          (0x3)
#define SFT_OTP_CTRL_OTP_READ_STATUS_STATUS                          (0)
#define LSB_OTP_CTRL_OTP_READ_STATUS_STATUS                          (0)
#define MSB_OTP_CTRL_OTP_READ_STATUS_STATUS                          (1)

typedef struct {
  unsigned short status : 2;
  unsigned short reserved : 14;
} otp_ctrl_otp_read_status_bf;
		
typedef union {
  unsigned short val;
  otp_ctrl_otp_read_status_bf bf;
} otp_ctrl_otp_read_status_t;



typedef struct {
  otp_ctrl_otp_read_address_t                                        otp_read_address;
  otp_ctrl_otp_read_value_t                                          otp_read_value;
  otp_ctrl_otp_read_status_t                                         otp_read_status;
} otp_ctrl_t;

typedef union {
  unsigned short a[sizeof(otp_ctrl_t)/sizeof(unsigned short)];
  otp_ctrl_t s;
} otp_ctrl_u_t;


#define ADDR_OTP_CTRL_OTP_READ_ADDRESS                               (0x70U)
#define A_OTP_CTRL_OTP_READ_ADDRESS(ba)                              ((ba) + ADDR_OTP_CTRL_OTP_READ_ADDRESS)
#define R_OTP_CTRL_OTP_READ_ADDRESS(ba)                              (*(volatile unsigned short *)((unsigned int)A_OTP_CTRL_OTP_READ_ADDRESS(ba)))
#define RES_OTP_CTRL_OTP_READ_ADDRESS                                (0x0000U)
#define MSB_OTP_CTRL_OTP_READ_ADDRESS                                (15)
#define LSB_OTP_CTRL_OTP_READ_ADDRESS                                (0)
#define VBMASK_OTP_CTRL_OTP_READ_ADDRESS                             (0x0fffU)
#define ROMASK_OTP_CTRL_OTP_READ_ADDRESS                             (0xf000U)
#define AADDR_OTP_CTRL_OTP_READ_ADDRESS                              (BASE_ADDR_OTP_CTRL + ADDR_OTP_CTRL_OTP_READ_ADDRESS)
#define REG_OTP_CTRL_OTP_READ_ADDRESS                                (*(volatile unsigned short *)((unsigned int)AADDR_OTP_CTRL_OTP_READ_ADDRESS))

#define ADDR_OTP_CTRL_OTP_READ_VALUE                                 (0x71U)
#define A_OTP_CTRL_OTP_READ_VALUE(ba)                                ((ba) + ADDR_OTP_CTRL_OTP_READ_VALUE)
#define R_OTP_CTRL_OTP_READ_VALUE(ba)                                (*(volatile unsigned short *)((unsigned int)A_OTP_CTRL_OTP_READ_VALUE(ba)))
#define RES_OTP_CTRL_OTP_READ_VALUE                                  (0x0000U)
#define MSB_OTP_CTRL_OTP_READ_VALUE                                  (15)
#define LSB_OTP_CTRL_OTP_READ_VALUE                                  (0)
#define VBMASK_OTP_CTRL_OTP_READ_VALUE                               (0x0fffU)
#define ROMASK_OTP_CTRL_OTP_READ_VALUE                               (0xffffU)
#define AADDR_OTP_CTRL_OTP_READ_VALUE                                (BASE_ADDR_OTP_CTRL + ADDR_OTP_CTRL_OTP_READ_VALUE)
#define REG_OTP_CTRL_OTP_READ_VALUE                                  (*(volatile unsigned short *)((unsigned int)AADDR_OTP_CTRL_OTP_READ_VALUE))

#define ADDR_OTP_CTRL_OTP_READ_STATUS                                (0x72U)
#define A_OTP_CTRL_OTP_READ_STATUS(ba)                               ((ba) + ADDR_OTP_CTRL_OTP_READ_STATUS)
#define R_OTP_CTRL_OTP_READ_STATUS(ba)                               (*(volatile unsigned short *)((unsigned int)A_OTP_CTRL_OTP_READ_STATUS(ba)))
#define RES_OTP_CTRL_OTP_READ_STATUS                                 (0x0000U)
#define MSB_OTP_CTRL_OTP_READ_STATUS                                 (15)
#define LSB_OTP_CTRL_OTP_READ_STATUS                                 (0)
#define VBMASK_OTP_CTRL_OTP_READ_STATUS                              (0x0003U)
#define ROMASK_OTP_CTRL_OTP_READ_STATUS                              (0xffffU)
#define AADDR_OTP_CTRL_OTP_READ_STATUS                               (BASE_ADDR_OTP_CTRL + ADDR_OTP_CTRL_OTP_READ_STATUS)
#define REG_OTP_CTRL_OTP_READ_STATUS                                 (*(volatile unsigned short *)((unsigned int)AADDR_OTP_CTRL_OTP_READ_STATUS))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_Trimming_0 
#define BASE_ADDR_DSI_Trimming_0 0x0010U
#define SIZE_DSI_Trimming_0 0x0002U
#endif

// Register bit field definitions
	 
/* DSI_Trimming_0_TRIM_DSI_REC_FALL */

#define MSK_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC1               (0xf)
#define SFT_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC1               (0)
#define LSB_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC1               (0)
#define MSB_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC1               (3)

#define MSK_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC2               (0xf)
#define SFT_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC2               (0)
#define LSB_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC2               (4)
#define MSB_DSI_TRIMMING_0_TRIM_DSI_REC_FALL_TRIM_REC2               (7)

typedef struct {
  unsigned short trim_rec1 : 4;
  unsigned short trim_rec2 : 4;
  unsigned short reserved : 8;
} dsi_trimming_0_trim_dsi_rec_fall_bf;
		
typedef union {
  unsigned short val;
  dsi_trimming_0_trim_dsi_rec_fall_bf bf;
} dsi_trimming_0_trim_dsi_rec_fall_t;


/* DSI_Trimming_0_TRIM_DSI_REC_RISE */

#define MSK_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC1               (0xf)
#define SFT_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC1               (0)
#define LSB_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC1               (0)
#define MSB_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC1               (3)

#define MSK_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC2               (0xf)
#define SFT_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC2               (0)
#define LSB_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC2               (4)
#define MSB_DSI_TRIMMING_0_TRIM_DSI_REC_RISE_TRIM_REC2               (7)

typedef struct {
  unsigned short trim_rec1 : 4;
  unsigned short trim_rec2 : 4;
  unsigned short reserved : 8;
} dsi_trimming_0_trim_dsi_rec_rise_bf;
		
typedef union {
  unsigned short val;
  dsi_trimming_0_trim_dsi_rec_rise_bf bf;
} dsi_trimming_0_trim_dsi_rec_rise_t;



typedef struct {
  dsi_trimming_0_trim_dsi_rec_fall_t                                 trim_dsi_rec_fall;
  dsi_trimming_0_trim_dsi_rec_rise_t                                 trim_dsi_rec_rise;
} dsi_trimming_0_t;

typedef union {
  unsigned short a[sizeof(dsi_trimming_0_t)/sizeof(unsigned short)];
  dsi_trimming_0_t s;
} dsi_trimming_0_u_t;


#define ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                        (0x0U)
#define A_DSI_TRIMMING_0_TRIM_DSI_REC_FALL(ba)                       ((ba) + ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_FALL)
#define R_DSI_TRIMMING_0_TRIM_DSI_REC_FALL(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_TRIMMING_0_TRIM_DSI_REC_FALL(ba)))
#define RES_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                         (0x0000U)
#define MSB_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                         (15)
#define LSB_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                         (0)
#define VBMASK_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                      (0x00ffU)
#define ROMASK_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                      (0xffffU)
#define AADDR_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                       (BASE_ADDR_DSI_TRIMMING_0 + ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_FALL)
#define REG_DSI_TRIMMING_0_TRIM_DSI_REC_FALL                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_TRIMMING_0_TRIM_DSI_REC_FALL))

#define ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                        (0x1U)
#define A_DSI_TRIMMING_0_TRIM_DSI_REC_RISE(ba)                       ((ba) + ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_RISE)
#define R_DSI_TRIMMING_0_TRIM_DSI_REC_RISE(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_TRIMMING_0_TRIM_DSI_REC_RISE(ba)))
#define RES_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                         (0x0000U)
#define MSB_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                         (15)
#define LSB_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                         (0)
#define VBMASK_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                      (0x00ffU)
#define ROMASK_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                      (0xffffU)
#define AADDR_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                       (BASE_ADDR_DSI_TRIMMING_0 + ADDR_DSI_TRIMMING_0_TRIM_DSI_REC_RISE)
#define REG_DSI_TRIMMING_0_TRIM_DSI_REC_RISE                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_TRIMMING_0_TRIM_DSI_REC_RISE))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_Trimming_1 
#define BASE_ADDR_DSI_Trimming_1 0x0012U
#define SIZE_DSI_Trimming_1 0x0002U
#endif

// Register bit field definitions
	 
/* DSI_Trimming_1_TRIM_DSI_REC_FALL */

#define MSK_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC1               (0xf)
#define SFT_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC1               (0)
#define LSB_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC1               (0)
#define MSB_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC1               (3)

#define MSK_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC2               (0xf)
#define SFT_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC2               (0)
#define LSB_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC2               (4)
#define MSB_DSI_TRIMMING_1_TRIM_DSI_REC_FALL_TRIM_REC2               (7)

typedef struct {
  unsigned short trim_rec1 : 4;
  unsigned short trim_rec2 : 4;
  unsigned short reserved : 8;
} dsi_trimming_1_trim_dsi_rec_fall_bf;
		
typedef union {
  unsigned short val;
  dsi_trimming_1_trim_dsi_rec_fall_bf bf;
} dsi_trimming_1_trim_dsi_rec_fall_t;


/* DSI_Trimming_1_TRIM_DSI_REC_RISE */

#define MSK_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC1               (0xf)
#define SFT_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC1               (0)
#define LSB_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC1               (0)
#define MSB_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC1               (3)

#define MSK_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC2               (0xf)
#define SFT_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC2               (0)
#define LSB_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC2               (4)
#define MSB_DSI_TRIMMING_1_TRIM_DSI_REC_RISE_TRIM_REC2               (7)

typedef struct {
  unsigned short trim_rec1 : 4;
  unsigned short trim_rec2 : 4;
  unsigned short reserved : 8;
} dsi_trimming_1_trim_dsi_rec_rise_bf;
		
typedef union {
  unsigned short val;
  dsi_trimming_1_trim_dsi_rec_rise_bf bf;
} dsi_trimming_1_trim_dsi_rec_rise_t;



typedef struct {
  dsi_trimming_1_trim_dsi_rec_fall_t                                 trim_dsi_rec_fall;
  dsi_trimming_1_trim_dsi_rec_rise_t                                 trim_dsi_rec_rise;
} dsi_trimming_1_t;

typedef union {
  unsigned short a[sizeof(dsi_trimming_1_t)/sizeof(unsigned short)];
  dsi_trimming_1_t s;
} dsi_trimming_1_u_t;


#define ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                        (0x0U)
#define A_DSI_TRIMMING_1_TRIM_DSI_REC_FALL(ba)                       ((ba) + ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_FALL)
#define R_DSI_TRIMMING_1_TRIM_DSI_REC_FALL(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_TRIMMING_1_TRIM_DSI_REC_FALL(ba)))
#define RES_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                         (0x0000U)
#define MSB_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                         (15)
#define LSB_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                         (0)
#define VBMASK_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                      (0x00ffU)
#define ROMASK_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                      (0xffffU)
#define AADDR_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                       (BASE_ADDR_DSI_TRIMMING_1 + ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_FALL)
#define REG_DSI_TRIMMING_1_TRIM_DSI_REC_FALL                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_TRIMMING_1_TRIM_DSI_REC_FALL))

#define ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                        (0x1U)
#define A_DSI_TRIMMING_1_TRIM_DSI_REC_RISE(ba)                       ((ba) + ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_RISE)
#define R_DSI_TRIMMING_1_TRIM_DSI_REC_RISE(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_TRIMMING_1_TRIM_DSI_REC_RISE(ba)))
#define RES_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                         (0x0000U)
#define MSB_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                         (15)
#define LSB_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                         (0)
#define VBMASK_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                      (0x00ffU)
#define ROMASK_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                      (0xffffU)
#define AADDR_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                       (BASE_ADDR_DSI_TRIMMING_1 + ADDR_DSI_TRIMMING_1_TRIM_DSI_REC_RISE)
#define REG_DSI_TRIMMING_1_TRIM_DSI_REC_RISE                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_TRIMMING_1_TRIM_DSI_REC_RISE))

 


// Instance base addresses

#ifndef BASE_ADDR_gpio 
#define BASE_ADDR_gpio 0x0000U
#define SIZE_gpio 0x0010U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_0 
#define BASE_ADDR_DSI_0 0x00a0U
#define SIZE_DSI_0 0x0020U
#endif

// Register bit field definitions
	 
/* DSI_0_DSI_STAT */

#define MSK_DSI_0_DSI_STAT_PULSECNT                                  (0xff)
#define SFT_DSI_0_DSI_STAT_PULSECNT                                  (0)
#define LSB_DSI_0_DSI_STAT_PULSECNT                                  (0)
#define MSB_DSI_0_DSI_STAT_PULSECNT                                  (7)

#define BIT_DSI_0_DSI_STAT_DSIOV                                     (0)#define MSK_DSI_0_DSI_STAT_DSIOV                                     (0x1)
#define SFT_DSI_0_DSI_STAT_DSIOV                                     (0)
#define LSB_DSI_0_DSI_STAT_DSIOV                                     (8)
#define MSB_DSI_0_DSI_STAT_DSIOV                                     (8)

#define BIT_DSI_0_DSI_STAT_DSIUV                                     (0)#define MSK_DSI_0_DSI_STAT_DSIUV                                     (0x1)
#define SFT_DSI_0_DSI_STAT_DSIUV                                     (0)
#define LSB_DSI_0_DSI_STAT_DSIUV                                     (9)
#define MSB_DSI_0_DSI_STAT_DSIUV                                     (9)

#define BIT_DSI_0_DSI_STAT_SYNC                                      (0)#define MSK_DSI_0_DSI_STAT_SYNC                                      (0x1)
#define SFT_DSI_0_DSI_STAT_SYNC                                      (0)
#define LSB_DSI_0_DSI_STAT_SYNC                                      (10)
#define MSB_DSI_0_DSI_STAT_SYNC                                      (10)

#define MSK_DSI_0_DSI_STAT_SLAVES                                    (0xf)
#define SFT_DSI_0_DSI_STAT_SLAVES                                    (0)
#define LSB_DSI_0_DSI_STAT_SLAVES                                    (11)
#define MSB_DSI_0_DSI_STAT_SLAVES                                    (14)

typedef struct {
  unsigned short pulsecnt : 8;
  unsigned short dsiov : 1;
  unsigned short dsiuv : 1;
  unsigned short sync : 1;
  unsigned short slaves : 4;
} dsi_0_dsi_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_0_dsi_stat_bf bf;
} dsi_0_dsi_stat_t;


/* DSI_0_PDCM_PERIOD */

#define MSK_DSI_0_PDCM_PERIOD_PDCMPER                                (0xffff)
#define SFT_DSI_0_PDCM_PERIOD_PDCMPER                                (0)
#define LSB_DSI_0_PDCM_PERIOD_PDCMPER                                (0)
#define MSB_DSI_0_PDCM_PERIOD_PDCMPER                                (15)

typedef struct {
  unsigned short pdcmper : 16;
} dsi_0_pdcm_period_bf;
		
typedef union {
  unsigned short val;
  dsi_0_pdcm_period_bf bf;
} dsi_0_pdcm_period_t;


/* DSI_0_DSI_LOAD */

#define MSK_DSI_0_DSI_LOAD_LOAD                                      (0x1f)
#define SFT_DSI_0_DSI_LOAD_LOAD                                      (0)
#define LSB_DSI_0_DSI_LOAD_LOAD                                      (0)
#define MSB_DSI_0_DSI_LOAD_LOAD                                      (4)

#define BIT_DSI_0_DSI_LOAD_IDLE                                      (0)#define MSK_DSI_0_DSI_LOAD_IDLE                                      (0x1)
#define SFT_DSI_0_DSI_LOAD_IDLE                                      (0)
#define LSB_DSI_0_DSI_LOAD_IDLE                                      (14)
#define MSB_DSI_0_DSI_LOAD_IDLE                                      (14)

#define BIT_DSI_0_DSI_LOAD_START_MEASUREMENT                         (0)#define MSK_DSI_0_DSI_LOAD_START_MEASUREMENT                         (0x1)
#define SFT_DSI_0_DSI_LOAD_START_MEASUREMENT                         (0)
#define LSB_DSI_0_DSI_LOAD_START_MEASUREMENT                         (15)
#define MSB_DSI_0_DSI_LOAD_START_MEASUREMENT                         (15)

typedef struct {
  unsigned short load : 5;
  unsigned short reserved : 9;
  unsigned short idle : 1;
  unsigned short start_measurement : 1;
} dsi_0_dsi_load_bf;
		
typedef union {
  unsigned short val;
  dsi_0_dsi_load_bf bf;
} dsi_0_dsi_load_t;


/* DSI_0_DSI_IRQ_STAT */

#define BIT_DSI_0_DSI_IRQ_STAT_DSIOV                                 (0)#define MSK_DSI_0_DSI_IRQ_STAT_DSIOV                                 (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_DSIOV                                 (0)
#define LSB_DSI_0_DSI_IRQ_STAT_DSIOV                                 (0)
#define MSB_DSI_0_DSI_IRQ_STAT_DSIOV                                 (0)

#define BIT_DSI_0_DSI_IRQ_STAT_DSIUV                                 (0)#define MSK_DSI_0_DSI_IRQ_STAT_DSIUV                                 (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_DSIUV                                 (0)
#define LSB_DSI_0_DSI_IRQ_STAT_DSIUV                                 (1)
#define MSB_DSI_0_DSI_IRQ_STAT_DSIUV                                 (1)

#define BIT_DSI_0_DSI_IRQ_STAT_SYNC_ERR                              (0)#define MSK_DSI_0_DSI_IRQ_STAT_SYNC_ERR                              (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_SYNC_ERR                              (0)
#define LSB_DSI_0_DSI_IRQ_STAT_SYNC_ERR                              (2)
#define MSB_DSI_0_DSI_IRQ_STAT_SYNC_ERR                              (2)

#define BIT_DSI_0_DSI_IRQ_STAT_HW_FAIL                               (0)#define MSK_DSI_0_DSI_IRQ_STAT_HW_FAIL                               (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_HW_FAIL                               (0)
#define LSB_DSI_0_DSI_IRQ_STAT_HW_FAIL                               (3)
#define MSB_DSI_0_DSI_IRQ_STAT_HW_FAIL                               (3)

#define BIT_DSI_0_DSI_IRQ_STAT_DMOF                                  (0)#define MSK_DSI_0_DSI_IRQ_STAT_DMOF                                  (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_DMOF                                  (0)
#define LSB_DSI_0_DSI_IRQ_STAT_DMOF                                  (4)
#define MSB_DSI_0_DSI_IRQ_STAT_DMOF                                  (4)

#define BIT_DSI_0_DSI_IRQ_STAT_COM_ERR                               (0)#define MSK_DSI_0_DSI_IRQ_STAT_COM_ERR                               (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_COM_ERR                               (0)
#define LSB_DSI_0_DSI_IRQ_STAT_COM_ERR                               (5)
#define MSB_DSI_0_DSI_IRQ_STAT_COM_ERR                               (5)

#define BIT_DSI_0_DSI_IRQ_STAT_IQ_ERR                                (0)#define MSK_DSI_0_DSI_IRQ_STAT_IQ_ERR                                (0x1)
#define SFT_DSI_0_DSI_IRQ_STAT_IQ_ERR                                (0)
#define LSB_DSI_0_DSI_IRQ_STAT_IQ_ERR                                (6)
#define MSB_DSI_0_DSI_IRQ_STAT_IQ_ERR                                (6)

typedef struct {
  unsigned short dsiov : 1;
  unsigned short dsiuv : 1;
  unsigned short sync_err : 1;
  unsigned short hw_fail : 1;
  unsigned short dmof : 1;
  unsigned short com_err : 1;
  unsigned short iq_err : 1;
} dsi_0_dsi_irq_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_0_dsi_irq_stat_bf bf;
} dsi_0_dsi_irq_stat_t;


/* DSI_0_DSI_IRQ_MASK */

#define BIT_DSI_0_DSI_IRQ_MASK_DSIOV                                 (0)#define MSK_DSI_0_DSI_IRQ_MASK_DSIOV                                 (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_DSIOV                                 (0)
#define LSB_DSI_0_DSI_IRQ_MASK_DSIOV                                 (0)
#define MSB_DSI_0_DSI_IRQ_MASK_DSIOV                                 (0)

#define BIT_DSI_0_DSI_IRQ_MASK_DSIUV                                 (0)#define MSK_DSI_0_DSI_IRQ_MASK_DSIUV                                 (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_DSIUV                                 (0)
#define LSB_DSI_0_DSI_IRQ_MASK_DSIUV                                 (1)
#define MSB_DSI_0_DSI_IRQ_MASK_DSIUV                                 (1)

#define BIT_DSI_0_DSI_IRQ_MASK_SYNC_ERR                              (0)#define MSK_DSI_0_DSI_IRQ_MASK_SYNC_ERR                              (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_SYNC_ERR                              (0)
#define LSB_DSI_0_DSI_IRQ_MASK_SYNC_ERR                              (2)
#define MSB_DSI_0_DSI_IRQ_MASK_SYNC_ERR                              (2)

#define BIT_DSI_0_DSI_IRQ_MASK_HW_FAIL                               (0)#define MSK_DSI_0_DSI_IRQ_MASK_HW_FAIL                               (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_HW_FAIL                               (0)
#define LSB_DSI_0_DSI_IRQ_MASK_HW_FAIL                               (3)
#define MSB_DSI_0_DSI_IRQ_MASK_HW_FAIL                               (3)

#define BIT_DSI_0_DSI_IRQ_MASK_DMOF                                  (0)#define MSK_DSI_0_DSI_IRQ_MASK_DMOF                                  (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_DMOF                                  (0)
#define LSB_DSI_0_DSI_IRQ_MASK_DMOF                                  (4)
#define MSB_DSI_0_DSI_IRQ_MASK_DMOF                                  (4)

#define BIT_DSI_0_DSI_IRQ_MASK_COM_ERR                               (0)#define MSK_DSI_0_DSI_IRQ_MASK_COM_ERR                               (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_COM_ERR                               (0)
#define LSB_DSI_0_DSI_IRQ_MASK_COM_ERR                               (5)
#define MSB_DSI_0_DSI_IRQ_MASK_COM_ERR                               (5)

#define BIT_DSI_0_DSI_IRQ_MASK_IQ_ERR                                (0)#define MSK_DSI_0_DSI_IRQ_MASK_IQ_ERR                                (0x1)
#define SFT_DSI_0_DSI_IRQ_MASK_IQ_ERR                                (0)
#define LSB_DSI_0_DSI_IRQ_MASK_IQ_ERR                                (6)
#define MSB_DSI_0_DSI_IRQ_MASK_IQ_ERR                                (6)

typedef struct {
  unsigned short dsiov : 1;
  unsigned short dsiuv : 1;
  unsigned short sync_err : 1;
  unsigned short hw_fail : 1;
  unsigned short dmof : 1;
  unsigned short com_err : 1;
  unsigned short iq_err : 1;
} dsi_0_dsi_irq_mask_bf;
		
typedef union {
  unsigned short val;
  dsi_0_dsi_irq_mask_bf bf;
} dsi_0_dsi_irq_mask_t;


/* DSI_0_DSI_CMD */

#define MSK_DSI_0_DSI_CMD_DATA                                       (0xfff)
#define SFT_DSI_0_DSI_CMD_DATA                                       (0)
#define LSB_DSI_0_DSI_CMD_DATA                                       (0)
#define MSB_DSI_0_DSI_CMD_DATA                                       (11)

#define MSK_DSI_0_DSI_CMD_CMD                                        (0xf)
#define SFT_DSI_0_DSI_CMD_CMD                                        (0)
#define LSB_DSI_0_DSI_CMD_CMD                                        (12)
#define MSB_DSI_0_DSI_CMD_CMD                                        (15)

typedef struct {
  unsigned short data : 12;
  unsigned short cmd : 4;
} dsi_0_dsi_cmd_bf;
		
typedef union {
  unsigned short val;
  dsi_0_dsi_cmd_bf bf;
} dsi_0_dsi_cmd_t;


/* DSI_0_CRM_WORD2 */

#define MSK_DSI_0_CRM_WORD2_CRM_WORD2                                (0xffff)
#define SFT_DSI_0_CRM_WORD2_CRM_WORD2                                (0)
#define LSB_DSI_0_CRM_WORD2_CRM_WORD2                                (0)
#define MSB_DSI_0_CRM_WORD2_CRM_WORD2                                (15)

typedef struct {
  unsigned short crm_word2 : 16;
} dsi_0_crm_word2_bf;
		
typedef union {
  unsigned short val;
  dsi_0_crm_word2_bf bf;
} dsi_0_crm_word2_t;


/* DSI_0_CRM_WORD1 */

#define MSK_DSI_0_CRM_WORD1_CRM_WORD1                                (0xffff)
#define SFT_DSI_0_CRM_WORD1_CRM_WORD1                                (0)
#define LSB_DSI_0_CRM_WORD1_CRM_WORD1                                (0)
#define MSB_DSI_0_CRM_WORD1_CRM_WORD1                                (15)

typedef struct {
  unsigned short crm_word1 : 16;
} dsi_0_crm_word1_bf;
		
typedef union {
  unsigned short val;
  dsi_0_crm_word1_bf bf;
} dsi_0_crm_word1_t;


/* DSI_0_PACKET_STAT */

#define MSK_DSI_0_PACKET_STAT_SYMBOL_COUNT                           (0xff)
#define SFT_DSI_0_PACKET_STAT_SYMBOL_COUNT                           (0)
#define LSB_DSI_0_PACKET_STAT_SYMBOL_COUNT                           (0)
#define MSB_DSI_0_PACKET_STAT_SYMBOL_COUNT                           (7)

#define BIT_DSI_0_PACKET_STAT_CLK_ERR                                (0)#define MSK_DSI_0_PACKET_STAT_CLK_ERR                                (0x1)
#define SFT_DSI_0_PACKET_STAT_CLK_ERR                                (0)
#define LSB_DSI_0_PACKET_STAT_CLK_ERR                                (8)
#define MSB_DSI_0_PACKET_STAT_CLK_ERR                                (8)

#define BIT_DSI_0_PACKET_STAT_VDSI_ERR                               (0)#define MSK_DSI_0_PACKET_STAT_VDSI_ERR                               (0x1)
#define SFT_DSI_0_PACKET_STAT_VDSI_ERR                               (0)
#define LSB_DSI_0_PACKET_STAT_VDSI_ERR                               (9)
#define MSB_DSI_0_PACKET_STAT_VDSI_ERR                               (9)

#define BIT_DSI_0_PACKET_STAT_SYMBOL_ERROR                           (0)#define MSK_DSI_0_PACKET_STAT_SYMBOL_ERROR                           (0x1)
#define SFT_DSI_0_PACKET_STAT_SYMBOL_ERROR                           (0)
#define LSB_DSI_0_PACKET_STAT_SYMBOL_ERROR                           (10)
#define MSB_DSI_0_PACKET_STAT_SYMBOL_ERROR                           (10)

#define BIT_DSI_0_PACKET_STAT_TE                                     (0)#define MSK_DSI_0_PACKET_STAT_TE                                     (0x1)
#define SFT_DSI_0_PACKET_STAT_TE                                     (0)
#define LSB_DSI_0_PACKET_STAT_TE                                     (11)
#define MSB_DSI_0_PACKET_STAT_TE                                     (11)

#define BIT_DSI_0_PACKET_STAT_CRC_ERR                                (0)#define MSK_DSI_0_PACKET_STAT_CRC_ERR                                (0x1)
#define SFT_DSI_0_PACKET_STAT_CRC_ERR                                (0)
#define LSB_DSI_0_PACKET_STAT_CRC_ERR                                (12)
#define MSB_DSI_0_PACKET_STAT_CRC_ERR                                (12)

#define BIT_DSI_0_PACKET_STAT_SCE                                    (0)#define MSK_DSI_0_PACKET_STAT_SCE                                    (0x1)
#define SFT_DSI_0_PACKET_STAT_SCE                                    (0)
#define LSB_DSI_0_PACKET_STAT_SCE                                    (13)
#define MSB_DSI_0_PACKET_STAT_SCE                                    (13)

typedef struct {
  unsigned short symbol_count : 8;
  unsigned short clk_err : 1;
  unsigned short vdsi_err : 1;
  unsigned short symbol_error : 1;
  unsigned short te : 1;
  unsigned short crc_err : 1;
  unsigned short sce : 1;
  unsigned short reserved : 2;
} dsi_0_packet_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_0_packet_stat_bf bf;
} dsi_0_packet_stat_t;


/* DSI_0_FRAME_STAT */

#define MSK_DSI_0_FRAME_STAT_PACKET_COUNT                            (0xff)
#define SFT_DSI_0_FRAME_STAT_PACKET_COUNT                            (0)
#define LSB_DSI_0_FRAME_STAT_PACKET_COUNT                            (0)
#define MSB_DSI_0_FRAME_STAT_PACKET_COUNT                            (7)

#define BIT_DSI_0_FRAME_STAT_PC                                      (0)#define MSK_DSI_0_FRAME_STAT_PC                                      (0x1)
#define SFT_DSI_0_FRAME_STAT_PC                                      (0)
#define LSB_DSI_0_FRAME_STAT_PC                                      (15)
#define MSB_DSI_0_FRAME_STAT_PC                                      (15)

typedef struct {
  unsigned short packet_count : 8;
  unsigned short reserved : 7;
  unsigned short pc : 1;
} dsi_0_frame_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_0_frame_stat_bf bf;
} dsi_0_frame_stat_t;


/* DSI_0_WAIT_TIME */

#define MSK_DSI_0_WAIT_TIME_TIME                                     (0x7fff)
#define SFT_DSI_0_WAIT_TIME_TIME                                     (0)
#define LSB_DSI_0_WAIT_TIME_TIME                                     (0)
#define MSB_DSI_0_WAIT_TIME_TIME                                     (14)

typedef struct {
  unsigned short time : 15;
} dsi_0_wait_time_bf;
		
typedef union {
  unsigned short val;
  dsi_0_wait_time_bf bf;
} dsi_0_wait_time_t;


/* DSI_0_SYNC */

#define MSK_DSI_0_SYNC_CHANNELS                                      (0x3)
#define SFT_DSI_0_SYNC_CHANNELS                                      (0)
#define LSB_DSI_0_SYNC_CHANNELS                                      (0)
#define MSB_DSI_0_SYNC_CHANNELS                                      (1)

#define BIT_DSI_0_SYNC_PIN                                           (0)#define MSK_DSI_0_SYNC_PIN                                           (0x1)
#define SFT_DSI_0_SYNC_PIN                                           (0)
#define LSB_DSI_0_SYNC_PIN                                           (4)
#define MSB_DSI_0_SYNC_PIN                                           (4)

typedef struct {
  unsigned short channels : 2;
  unsigned short reserved : 2;
  unsigned short pin : 1;
} dsi_0_sync_bf;
		
typedef union {
  unsigned short val;
  dsi_0_sync_bf bf;
} dsi_0_sync_t;



typedef struct {
  dsi_0_dsi_stat_t                                                   dsi_stat;
  dsi_0_pdcm_period_t                                                pdcm_period;
  dsi_0_dsi_load_t                                                   dsi_load;
  dsi_0_dsi_irq_stat_t                                               dsi_irq_stat;
  dsi_0_dsi_irq_mask_t                                               dsi_irq_mask;
  dsi_0_dsi_cmd_t                                                    dsi_cmd;
  dsi_0_crm_word2_t                                                  crm_word2;
  dsi_0_crm_word1_t                                                  crm_word1;
  dsi_0_packet_stat_t                                                packet_stat;
  dsi_0_frame_stat_t                                                 frame_stat;
  dsi_0_wait_time_t                                                  wait_time;
  dsi_0_sync_t                                                       sync;
} dsi_0_t;

typedef union {
  unsigned short a[sizeof(dsi_0_t)/sizeof(unsigned short)];
  dsi_0_t s;
} dsi_0_u_t;


#define ADDR_DSI_0_DSI_STAT                                          (0x0U)
#define A_DSI_0_DSI_STAT(ba)                                         ((ba) + ADDR_DSI_0_DSI_STAT)
#define R_DSI_0_DSI_STAT(ba)                                         (*(volatile unsigned short *)((unsigned int)A_DSI_0_DSI_STAT(ba)))
#define RES_DSI_0_DSI_STAT                                           (0x0000U)
#define MSB_DSI_0_DSI_STAT                                           (14)
#define LSB_DSI_0_DSI_STAT                                           (0)
#define VBMASK_DSI_0_DSI_STAT                                        (0x7fffU)
#define ROMASK_DSI_0_DSI_STAT                                        (0x7fffU)
#define AADDR_DSI_0_DSI_STAT                                         (BASE_ADDR_DSI_0 + ADDR_DSI_0_DSI_STAT)
#define REG_DSI_0_DSI_STAT                                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_DSI_STAT))

#define ADDR_DSI_0_PDCM_PERIOD                                       (0x4U)
#define A_DSI_0_PDCM_PERIOD(ba)                                      ((ba) + ADDR_DSI_0_PDCM_PERIOD)
#define R_DSI_0_PDCM_PERIOD(ba)                                      (*(volatile unsigned short *)((unsigned int)A_DSI_0_PDCM_PERIOD(ba)))
#define RES_DSI_0_PDCM_PERIOD                                        (0x03e8U)
#define MSB_DSI_0_PDCM_PERIOD                                        (15)
#define LSB_DSI_0_PDCM_PERIOD                                        (0)
#define VBMASK_DSI_0_PDCM_PERIOD                                     (0xffffU)
#define ROMASK_DSI_0_PDCM_PERIOD                                     (0xffffU)
#define AADDR_DSI_0_PDCM_PERIOD                                      (BASE_ADDR_DSI_0 + ADDR_DSI_0_PDCM_PERIOD)
#define REG_DSI_0_PDCM_PERIOD                                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_PDCM_PERIOD))

#define ADDR_DSI_0_DSI_LOAD                                          (0x5U)
#define A_DSI_0_DSI_LOAD(ba)                                         ((ba) + ADDR_DSI_0_DSI_LOAD)
#define R_DSI_0_DSI_LOAD(ba)                                         (*(volatile unsigned short *)((unsigned int)A_DSI_0_DSI_LOAD(ba)))
#define RES_DSI_0_DSI_LOAD                                           (0x4000U)
#define MSB_DSI_0_DSI_LOAD                                           (15)
#define LSB_DSI_0_DSI_LOAD                                           (0)
#define VBMASK_DSI_0_DSI_LOAD                                        (0xc01fU)
#define ROMASK_DSI_0_DSI_LOAD                                        (0xffe0U)
#define AADDR_DSI_0_DSI_LOAD                                         (BASE_ADDR_DSI_0 + ADDR_DSI_0_DSI_LOAD)
#define REG_DSI_0_DSI_LOAD                                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_DSI_LOAD))

#define ADDR_DSI_0_DSI_IRQ_STAT                                      (0x8U)
#define A_DSI_0_DSI_IRQ_STAT(ba)                                     ((ba) + ADDR_DSI_0_DSI_IRQ_STAT)
#define R_DSI_0_DSI_IRQ_STAT(ba)                                     (*(volatile unsigned short *)((unsigned int)A_DSI_0_DSI_IRQ_STAT(ba)))
#define RES_DSI_0_DSI_IRQ_STAT                                       (0x0000U)
#define MSB_DSI_0_DSI_IRQ_STAT                                       (6)
#define LSB_DSI_0_DSI_IRQ_STAT                                       (0)
#define VBMASK_DSI_0_DSI_IRQ_STAT                                    (0x007fU)
#define ROMASK_DSI_0_DSI_IRQ_STAT                                    (0x0000U)
#define AADDR_DSI_0_DSI_IRQ_STAT                                     (BASE_ADDR_DSI_0 + ADDR_DSI_0_DSI_IRQ_STAT)
#define REG_DSI_0_DSI_IRQ_STAT                                       (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_DSI_IRQ_STAT))

#define ADDR_DSI_0_DSI_IRQ_MASK                                      (0x9U)
#define A_DSI_0_DSI_IRQ_MASK(ba)                                     ((ba) + ADDR_DSI_0_DSI_IRQ_MASK)
#define R_DSI_0_DSI_IRQ_MASK(ba)                                     (*(volatile unsigned short *)((unsigned int)A_DSI_0_DSI_IRQ_MASK(ba)))
#define RES_DSI_0_DSI_IRQ_MASK                                       (0x007fU)
#define MSB_DSI_0_DSI_IRQ_MASK                                       (6)
#define LSB_DSI_0_DSI_IRQ_MASK                                       (0)
#define VBMASK_DSI_0_DSI_IRQ_MASK                                    (0x007fU)
#define ROMASK_DSI_0_DSI_IRQ_MASK                                    (0x0000U)
#define AADDR_DSI_0_DSI_IRQ_MASK                                     (BASE_ADDR_DSI_0 + ADDR_DSI_0_DSI_IRQ_MASK)
#define REG_DSI_0_DSI_IRQ_MASK                                       (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_DSI_IRQ_MASK))

#define ADDR_DSI_0_DSI_CMD                                           (0x10U)
#define A_DSI_0_DSI_CMD(ba)                                          ((ba) + ADDR_DSI_0_DSI_CMD)
#define R_DSI_0_DSI_CMD(ba)                                          (*(volatile unsigned short *)((unsigned int)A_DSI_0_DSI_CMD(ba)))
#define RES_DSI_0_DSI_CMD                                            (0x0000U)
#define MSB_DSI_0_DSI_CMD                                            (15)
#define LSB_DSI_0_DSI_CMD                                            (0)
#define VBMASK_DSI_0_DSI_CMD                                         (0xffffU)
#define ROMASK_DSI_0_DSI_CMD                                         (0xffffU)
#define AADDR_DSI_0_DSI_CMD                                          (BASE_ADDR_DSI_0 + ADDR_DSI_0_DSI_CMD)
#define REG_DSI_0_DSI_CMD                                            (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_DSI_CMD))

#define ADDR_DSI_0_CRM_WORD2                                         (0x11U)
#define A_DSI_0_CRM_WORD2(ba)                                        ((ba) + ADDR_DSI_0_CRM_WORD2)
#define R_DSI_0_CRM_WORD2(ba)                                        (*(volatile unsigned short *)((unsigned int)A_DSI_0_CRM_WORD2(ba)))
#define RES_DSI_0_CRM_WORD2                                          (0x00ffU)
#define MSB_DSI_0_CRM_WORD2                                          (15)
#define LSB_DSI_0_CRM_WORD2                                          (0)
#define VBMASK_DSI_0_CRM_WORD2                                       (0xffffU)
#define ROMASK_DSI_0_CRM_WORD2                                       (0xffffU)
#define AADDR_DSI_0_CRM_WORD2                                        (BASE_ADDR_DSI_0 + ADDR_DSI_0_CRM_WORD2)
#define REG_DSI_0_CRM_WORD2                                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_CRM_WORD2))

#define ADDR_DSI_0_CRM_WORD1                                         (0x12U)
#define A_DSI_0_CRM_WORD1(ba)                                        ((ba) + ADDR_DSI_0_CRM_WORD1)
#define R_DSI_0_CRM_WORD1(ba)                                        (*(volatile unsigned short *)((unsigned int)A_DSI_0_CRM_WORD1(ba)))
#define RES_DSI_0_CRM_WORD1                                          (0x0000U)
#define MSB_DSI_0_CRM_WORD1                                          (15)
#define LSB_DSI_0_CRM_WORD1                                          (0)
#define VBMASK_DSI_0_CRM_WORD1                                       (0xffffU)
#define ROMASK_DSI_0_CRM_WORD1                                       (0xffffU)
#define AADDR_DSI_0_CRM_WORD1                                        (BASE_ADDR_DSI_0 + ADDR_DSI_0_CRM_WORD1)
#define REG_DSI_0_CRM_WORD1                                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_CRM_WORD1))

#define ADDR_DSI_0_PACKET_STAT                                       (0x18U)
#define A_DSI_0_PACKET_STAT(ba)                                      ((ba) + ADDR_DSI_0_PACKET_STAT)
#define R_DSI_0_PACKET_STAT(ba)                                      (*(volatile unsigned short *)((unsigned int)A_DSI_0_PACKET_STAT(ba)))
#define RES_DSI_0_PACKET_STAT                                        (0x0000U)
#define MSB_DSI_0_PACKET_STAT                                        (15)
#define LSB_DSI_0_PACKET_STAT                                        (0)
#define VBMASK_DSI_0_PACKET_STAT                                     (0x3fffU)
#define ROMASK_DSI_0_PACKET_STAT                                     (0xffffU)
#define AADDR_DSI_0_PACKET_STAT                                      (BASE_ADDR_DSI_0 + ADDR_DSI_0_PACKET_STAT)
#define REG_DSI_0_PACKET_STAT                                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_PACKET_STAT))

#define ADDR_DSI_0_FRAME_STAT                                        (0x1BU)
#define A_DSI_0_FRAME_STAT(ba)                                       ((ba) + ADDR_DSI_0_FRAME_STAT)
#define R_DSI_0_FRAME_STAT(ba)                                       (*(volatile unsigned short *)((unsigned int)A_DSI_0_FRAME_STAT(ba)))
#define RES_DSI_0_FRAME_STAT                                         (0x0000U)
#define MSB_DSI_0_FRAME_STAT                                         (15)
#define LSB_DSI_0_FRAME_STAT                                         (0)
#define VBMASK_DSI_0_FRAME_STAT                                      (0x80ffU)
#define ROMASK_DSI_0_FRAME_STAT                                      (0xffffU)
#define AADDR_DSI_0_FRAME_STAT                                       (BASE_ADDR_DSI_0 + ADDR_DSI_0_FRAME_STAT)
#define REG_DSI_0_FRAME_STAT                                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_FRAME_STAT))

#define ADDR_DSI_0_WAIT_TIME                                         (0x19U)
#define A_DSI_0_WAIT_TIME(ba)                                        ((ba) + ADDR_DSI_0_WAIT_TIME)
#define R_DSI_0_WAIT_TIME(ba)                                        (*(volatile unsigned short *)((unsigned int)A_DSI_0_WAIT_TIME(ba)))
#define RES_DSI_0_WAIT_TIME                                          (0x0000U)
#define MSB_DSI_0_WAIT_TIME                                          (14)
#define LSB_DSI_0_WAIT_TIME                                          (0)
#define VBMASK_DSI_0_WAIT_TIME                                       (0x7fffU)
#define ROMASK_DSI_0_WAIT_TIME                                       (0x7fffU)
#define AADDR_DSI_0_WAIT_TIME                                        (BASE_ADDR_DSI_0 + ADDR_DSI_0_WAIT_TIME)
#define REG_DSI_0_WAIT_TIME                                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_WAIT_TIME))

#define ADDR_DSI_0_SYNC                                              (0x1AU)
#define A_DSI_0_SYNC(ba)                                             ((ba) + ADDR_DSI_0_SYNC)
#define R_DSI_0_SYNC(ba)                                             (*(volatile unsigned short *)((unsigned int)A_DSI_0_SYNC(ba)))
#define RES_DSI_0_SYNC                                               (0x0000U)
#define MSB_DSI_0_SYNC                                               (4)
#define LSB_DSI_0_SYNC                                               (0)
#define VBMASK_DSI_0_SYNC                                            (0x0013U)
#define ROMASK_DSI_0_SYNC                                            (0x001fU)
#define AADDR_DSI_0_SYNC                                             (BASE_ADDR_DSI_0 + ADDR_DSI_0_SYNC)
#define REG_DSI_0_SYNC                                               (*(volatile unsigned short *)((unsigned int)AADDR_DSI_0_SYNC))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_1 
#define BASE_ADDR_DSI_1 0x00c0U
#define SIZE_DSI_1 0x0020U
#endif

// Register bit field definitions
	 
/* DSI_1_DSI_STAT */

#define MSK_DSI_1_DSI_STAT_PULSECNT                                  (0xff)
#define SFT_DSI_1_DSI_STAT_PULSECNT                                  (0)
#define LSB_DSI_1_DSI_STAT_PULSECNT                                  (0)
#define MSB_DSI_1_DSI_STAT_PULSECNT                                  (7)

#define BIT_DSI_1_DSI_STAT_DSIOV                                     (0)#define MSK_DSI_1_DSI_STAT_DSIOV                                     (0x1)
#define SFT_DSI_1_DSI_STAT_DSIOV                                     (0)
#define LSB_DSI_1_DSI_STAT_DSIOV                                     (8)
#define MSB_DSI_1_DSI_STAT_DSIOV                                     (8)

#define BIT_DSI_1_DSI_STAT_DSIUV                                     (0)#define MSK_DSI_1_DSI_STAT_DSIUV                                     (0x1)
#define SFT_DSI_1_DSI_STAT_DSIUV                                     (0)
#define LSB_DSI_1_DSI_STAT_DSIUV                                     (9)
#define MSB_DSI_1_DSI_STAT_DSIUV                                     (9)

#define BIT_DSI_1_DSI_STAT_SYNC                                      (0)#define MSK_DSI_1_DSI_STAT_SYNC                                      (0x1)
#define SFT_DSI_1_DSI_STAT_SYNC                                      (0)
#define LSB_DSI_1_DSI_STAT_SYNC                                      (10)
#define MSB_DSI_1_DSI_STAT_SYNC                                      (10)

#define MSK_DSI_1_DSI_STAT_SLAVES                                    (0xf)
#define SFT_DSI_1_DSI_STAT_SLAVES                                    (0)
#define LSB_DSI_1_DSI_STAT_SLAVES                                    (11)
#define MSB_DSI_1_DSI_STAT_SLAVES                                    (14)

typedef struct {
  unsigned short pulsecnt : 8;
  unsigned short dsiov : 1;
  unsigned short dsiuv : 1;
  unsigned short sync : 1;
  unsigned short slaves : 4;
} dsi_1_dsi_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_1_dsi_stat_bf bf;
} dsi_1_dsi_stat_t;


/* DSI_1_PDCM_PERIOD */

#define MSK_DSI_1_PDCM_PERIOD_PDCMPER                                (0xffff)
#define SFT_DSI_1_PDCM_PERIOD_PDCMPER                                (0)
#define LSB_DSI_1_PDCM_PERIOD_PDCMPER                                (0)
#define MSB_DSI_1_PDCM_PERIOD_PDCMPER                                (15)

typedef struct {
  unsigned short pdcmper : 16;
} dsi_1_pdcm_period_bf;
		
typedef union {
  unsigned short val;
  dsi_1_pdcm_period_bf bf;
} dsi_1_pdcm_period_t;


/* DSI_1_DSI_LOAD */

#define MSK_DSI_1_DSI_LOAD_LOAD                                      (0x1f)
#define SFT_DSI_1_DSI_LOAD_LOAD                                      (0)
#define LSB_DSI_1_DSI_LOAD_LOAD                                      (0)
#define MSB_DSI_1_DSI_LOAD_LOAD                                      (4)

#define BIT_DSI_1_DSI_LOAD_IDLE                                      (0)#define MSK_DSI_1_DSI_LOAD_IDLE                                      (0x1)
#define SFT_DSI_1_DSI_LOAD_IDLE                                      (0)
#define LSB_DSI_1_DSI_LOAD_IDLE                                      (14)
#define MSB_DSI_1_DSI_LOAD_IDLE                                      (14)

#define BIT_DSI_1_DSI_LOAD_START_MEASUREMENT                         (0)#define MSK_DSI_1_DSI_LOAD_START_MEASUREMENT                         (0x1)
#define SFT_DSI_1_DSI_LOAD_START_MEASUREMENT                         (0)
#define LSB_DSI_1_DSI_LOAD_START_MEASUREMENT                         (15)
#define MSB_DSI_1_DSI_LOAD_START_MEASUREMENT                         (15)

typedef struct {
  unsigned short load : 5;
  unsigned short reserved : 9;
  unsigned short idle : 1;
  unsigned short start_measurement : 1;
} dsi_1_dsi_load_bf;
		
typedef union {
  unsigned short val;
  dsi_1_dsi_load_bf bf;
} dsi_1_dsi_load_t;


/* DSI_1_DSI_IRQ_STAT */

#define BIT_DSI_1_DSI_IRQ_STAT_DSIOV                                 (0)#define MSK_DSI_1_DSI_IRQ_STAT_DSIOV                                 (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_DSIOV                                 (0)
#define LSB_DSI_1_DSI_IRQ_STAT_DSIOV                                 (0)
#define MSB_DSI_1_DSI_IRQ_STAT_DSIOV                                 (0)

#define BIT_DSI_1_DSI_IRQ_STAT_DSIUV                                 (0)#define MSK_DSI_1_DSI_IRQ_STAT_DSIUV                                 (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_DSIUV                                 (0)
#define LSB_DSI_1_DSI_IRQ_STAT_DSIUV                                 (1)
#define MSB_DSI_1_DSI_IRQ_STAT_DSIUV                                 (1)

#define BIT_DSI_1_DSI_IRQ_STAT_SYNC_ERR                              (0)#define MSK_DSI_1_DSI_IRQ_STAT_SYNC_ERR                              (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_SYNC_ERR                              (0)
#define LSB_DSI_1_DSI_IRQ_STAT_SYNC_ERR                              (2)
#define MSB_DSI_1_DSI_IRQ_STAT_SYNC_ERR                              (2)

#define BIT_DSI_1_DSI_IRQ_STAT_HW_FAIL                               (0)#define MSK_DSI_1_DSI_IRQ_STAT_HW_FAIL                               (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_HW_FAIL                               (0)
#define LSB_DSI_1_DSI_IRQ_STAT_HW_FAIL                               (3)
#define MSB_DSI_1_DSI_IRQ_STAT_HW_FAIL                               (3)

#define BIT_DSI_1_DSI_IRQ_STAT_DMOF                                  (0)#define MSK_DSI_1_DSI_IRQ_STAT_DMOF                                  (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_DMOF                                  (0)
#define LSB_DSI_1_DSI_IRQ_STAT_DMOF                                  (4)
#define MSB_DSI_1_DSI_IRQ_STAT_DMOF                                  (4)

#define BIT_DSI_1_DSI_IRQ_STAT_COM_ERR                               (0)#define MSK_DSI_1_DSI_IRQ_STAT_COM_ERR                               (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_COM_ERR                               (0)
#define LSB_DSI_1_DSI_IRQ_STAT_COM_ERR                               (5)
#define MSB_DSI_1_DSI_IRQ_STAT_COM_ERR                               (5)

#define BIT_DSI_1_DSI_IRQ_STAT_IQ_ERR                                (0)#define MSK_DSI_1_DSI_IRQ_STAT_IQ_ERR                                (0x1)
#define SFT_DSI_1_DSI_IRQ_STAT_IQ_ERR                                (0)
#define LSB_DSI_1_DSI_IRQ_STAT_IQ_ERR                                (6)
#define MSB_DSI_1_DSI_IRQ_STAT_IQ_ERR                                (6)

typedef struct {
  unsigned short dsiov : 1;
  unsigned short dsiuv : 1;
  unsigned short sync_err : 1;
  unsigned short hw_fail : 1;
  unsigned short dmof : 1;
  unsigned short com_err : 1;
  unsigned short iq_err : 1;
} dsi_1_dsi_irq_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_1_dsi_irq_stat_bf bf;
} dsi_1_dsi_irq_stat_t;


/* DSI_1_DSI_IRQ_MASK */

#define BIT_DSI_1_DSI_IRQ_MASK_DSIOV                                 (0)#define MSK_DSI_1_DSI_IRQ_MASK_DSIOV                                 (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_DSIOV                                 (0)
#define LSB_DSI_1_DSI_IRQ_MASK_DSIOV                                 (0)
#define MSB_DSI_1_DSI_IRQ_MASK_DSIOV                                 (0)

#define BIT_DSI_1_DSI_IRQ_MASK_DSIUV                                 (0)#define MSK_DSI_1_DSI_IRQ_MASK_DSIUV                                 (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_DSIUV                                 (0)
#define LSB_DSI_1_DSI_IRQ_MASK_DSIUV                                 (1)
#define MSB_DSI_1_DSI_IRQ_MASK_DSIUV                                 (1)

#define BIT_DSI_1_DSI_IRQ_MASK_SYNC_ERR                              (0)#define MSK_DSI_1_DSI_IRQ_MASK_SYNC_ERR                              (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_SYNC_ERR                              (0)
#define LSB_DSI_1_DSI_IRQ_MASK_SYNC_ERR                              (2)
#define MSB_DSI_1_DSI_IRQ_MASK_SYNC_ERR                              (2)

#define BIT_DSI_1_DSI_IRQ_MASK_HW_FAIL                               (0)#define MSK_DSI_1_DSI_IRQ_MASK_HW_FAIL                               (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_HW_FAIL                               (0)
#define LSB_DSI_1_DSI_IRQ_MASK_HW_FAIL                               (3)
#define MSB_DSI_1_DSI_IRQ_MASK_HW_FAIL                               (3)

#define BIT_DSI_1_DSI_IRQ_MASK_DMOF                                  (0)#define MSK_DSI_1_DSI_IRQ_MASK_DMOF                                  (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_DMOF                                  (0)
#define LSB_DSI_1_DSI_IRQ_MASK_DMOF                                  (4)
#define MSB_DSI_1_DSI_IRQ_MASK_DMOF                                  (4)

#define BIT_DSI_1_DSI_IRQ_MASK_COM_ERR                               (0)#define MSK_DSI_1_DSI_IRQ_MASK_COM_ERR                               (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_COM_ERR                               (0)
#define LSB_DSI_1_DSI_IRQ_MASK_COM_ERR                               (5)
#define MSB_DSI_1_DSI_IRQ_MASK_COM_ERR                               (5)

#define BIT_DSI_1_DSI_IRQ_MASK_IQ_ERR                                (0)#define MSK_DSI_1_DSI_IRQ_MASK_IQ_ERR                                (0x1)
#define SFT_DSI_1_DSI_IRQ_MASK_IQ_ERR                                (0)
#define LSB_DSI_1_DSI_IRQ_MASK_IQ_ERR                                (6)
#define MSB_DSI_1_DSI_IRQ_MASK_IQ_ERR                                (6)

typedef struct {
  unsigned short dsiov : 1;
  unsigned short dsiuv : 1;
  unsigned short sync_err : 1;
  unsigned short hw_fail : 1;
  unsigned short dmof : 1;
  unsigned short com_err : 1;
  unsigned short iq_err : 1;
} dsi_1_dsi_irq_mask_bf;
		
typedef union {
  unsigned short val;
  dsi_1_dsi_irq_mask_bf bf;
} dsi_1_dsi_irq_mask_t;


/* DSI_1_DSI_CMD */

#define MSK_DSI_1_DSI_CMD_DATA                                       (0xfff)
#define SFT_DSI_1_DSI_CMD_DATA                                       (0)
#define LSB_DSI_1_DSI_CMD_DATA                                       (0)
#define MSB_DSI_1_DSI_CMD_DATA                                       (11)

#define MSK_DSI_1_DSI_CMD_CMD                                        (0xf)
#define SFT_DSI_1_DSI_CMD_CMD                                        (0)
#define LSB_DSI_1_DSI_CMD_CMD                                        (12)
#define MSB_DSI_1_DSI_CMD_CMD                                        (15)

typedef struct {
  unsigned short data : 12;
  unsigned short cmd : 4;
} dsi_1_dsi_cmd_bf;
		
typedef union {
  unsigned short val;
  dsi_1_dsi_cmd_bf bf;
} dsi_1_dsi_cmd_t;


/* DSI_1_CRM_WORD2 */

#define MSK_DSI_1_CRM_WORD2_CRM_WORD2                                (0xffff)
#define SFT_DSI_1_CRM_WORD2_CRM_WORD2                                (0)
#define LSB_DSI_1_CRM_WORD2_CRM_WORD2                                (0)
#define MSB_DSI_1_CRM_WORD2_CRM_WORD2                                (15)

typedef struct {
  unsigned short crm_word2 : 16;
} dsi_1_crm_word2_bf;
		
typedef union {
  unsigned short val;
  dsi_1_crm_word2_bf bf;
} dsi_1_crm_word2_t;


/* DSI_1_CRM_WORD1 */

#define MSK_DSI_1_CRM_WORD1_CRM_WORD1                                (0xffff)
#define SFT_DSI_1_CRM_WORD1_CRM_WORD1                                (0)
#define LSB_DSI_1_CRM_WORD1_CRM_WORD1                                (0)
#define MSB_DSI_1_CRM_WORD1_CRM_WORD1                                (15)

typedef struct {
  unsigned short crm_word1 : 16;
} dsi_1_crm_word1_bf;
		
typedef union {
  unsigned short val;
  dsi_1_crm_word1_bf bf;
} dsi_1_crm_word1_t;


/* DSI_1_PACKET_STAT */

#define MSK_DSI_1_PACKET_STAT_SYMBOL_COUNT                           (0xff)
#define SFT_DSI_1_PACKET_STAT_SYMBOL_COUNT                           (0)
#define LSB_DSI_1_PACKET_STAT_SYMBOL_COUNT                           (0)
#define MSB_DSI_1_PACKET_STAT_SYMBOL_COUNT                           (7)

#define BIT_DSI_1_PACKET_STAT_CLK_ERR                                (0)#define MSK_DSI_1_PACKET_STAT_CLK_ERR                                (0x1)
#define SFT_DSI_1_PACKET_STAT_CLK_ERR                                (0)
#define LSB_DSI_1_PACKET_STAT_CLK_ERR                                (8)
#define MSB_DSI_1_PACKET_STAT_CLK_ERR                                (8)

#define BIT_DSI_1_PACKET_STAT_VDSI_ERR                               (0)#define MSK_DSI_1_PACKET_STAT_VDSI_ERR                               (0x1)
#define SFT_DSI_1_PACKET_STAT_VDSI_ERR                               (0)
#define LSB_DSI_1_PACKET_STAT_VDSI_ERR                               (9)
#define MSB_DSI_1_PACKET_STAT_VDSI_ERR                               (9)

#define BIT_DSI_1_PACKET_STAT_SYMBOL_ERROR                           (0)#define MSK_DSI_1_PACKET_STAT_SYMBOL_ERROR                           (0x1)
#define SFT_DSI_1_PACKET_STAT_SYMBOL_ERROR                           (0)
#define LSB_DSI_1_PACKET_STAT_SYMBOL_ERROR                           (10)
#define MSB_DSI_1_PACKET_STAT_SYMBOL_ERROR                           (10)

#define BIT_DSI_1_PACKET_STAT_TE                                     (0)#define MSK_DSI_1_PACKET_STAT_TE                                     (0x1)
#define SFT_DSI_1_PACKET_STAT_TE                                     (0)
#define LSB_DSI_1_PACKET_STAT_TE                                     (11)
#define MSB_DSI_1_PACKET_STAT_TE                                     (11)

#define BIT_DSI_1_PACKET_STAT_CRC_ERR                                (0)#define MSK_DSI_1_PACKET_STAT_CRC_ERR                                (0x1)
#define SFT_DSI_1_PACKET_STAT_CRC_ERR                                (0)
#define LSB_DSI_1_PACKET_STAT_CRC_ERR                                (12)
#define MSB_DSI_1_PACKET_STAT_CRC_ERR                                (12)

#define BIT_DSI_1_PACKET_STAT_SCE                                    (0)#define MSK_DSI_1_PACKET_STAT_SCE                                    (0x1)
#define SFT_DSI_1_PACKET_STAT_SCE                                    (0)
#define LSB_DSI_1_PACKET_STAT_SCE                                    (13)
#define MSB_DSI_1_PACKET_STAT_SCE                                    (13)

typedef struct {
  unsigned short symbol_count : 8;
  unsigned short clk_err : 1;
  unsigned short vdsi_err : 1;
  unsigned short symbol_error : 1;
  unsigned short te : 1;
  unsigned short crc_err : 1;
  unsigned short sce : 1;
  unsigned short reserved : 2;
} dsi_1_packet_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_1_packet_stat_bf bf;
} dsi_1_packet_stat_t;


/* DSI_1_FRAME_STAT */

#define MSK_DSI_1_FRAME_STAT_PACKET_COUNT                            (0xff)
#define SFT_DSI_1_FRAME_STAT_PACKET_COUNT                            (0)
#define LSB_DSI_1_FRAME_STAT_PACKET_COUNT                            (0)
#define MSB_DSI_1_FRAME_STAT_PACKET_COUNT                            (7)

#define BIT_DSI_1_FRAME_STAT_PC                                      (0)#define MSK_DSI_1_FRAME_STAT_PC                                      (0x1)
#define SFT_DSI_1_FRAME_STAT_PC                                      (0)
#define LSB_DSI_1_FRAME_STAT_PC                                      (15)
#define MSB_DSI_1_FRAME_STAT_PC                                      (15)

typedef struct {
  unsigned short packet_count : 8;
  unsigned short reserved : 7;
  unsigned short pc : 1;
} dsi_1_frame_stat_bf;
		
typedef union {
  unsigned short val;
  dsi_1_frame_stat_bf bf;
} dsi_1_frame_stat_t;


/* DSI_1_WAIT_TIME */

#define MSK_DSI_1_WAIT_TIME_TIME                                     (0x7fff)
#define SFT_DSI_1_WAIT_TIME_TIME                                     (0)
#define LSB_DSI_1_WAIT_TIME_TIME                                     (0)
#define MSB_DSI_1_WAIT_TIME_TIME                                     (14)

typedef struct {
  unsigned short time : 15;
} dsi_1_wait_time_bf;
		
typedef union {
  unsigned short val;
  dsi_1_wait_time_bf bf;
} dsi_1_wait_time_t;


/* DSI_1_SYNC */

#define MSK_DSI_1_SYNC_CHANNELS                                      (0x3)
#define SFT_DSI_1_SYNC_CHANNELS                                      (0)
#define LSB_DSI_1_SYNC_CHANNELS                                      (0)
#define MSB_DSI_1_SYNC_CHANNELS                                      (1)

#define BIT_DSI_1_SYNC_PIN                                           (0)#define MSK_DSI_1_SYNC_PIN                                           (0x1)
#define SFT_DSI_1_SYNC_PIN                                           (0)
#define LSB_DSI_1_SYNC_PIN                                           (4)
#define MSB_DSI_1_SYNC_PIN                                           (4)

typedef struct {
  unsigned short channels : 2;
  unsigned short reserved : 2;
  unsigned short pin : 1;
} dsi_1_sync_bf;
		
typedef union {
  unsigned short val;
  dsi_1_sync_bf bf;
} dsi_1_sync_t;



typedef struct {
  dsi_1_dsi_stat_t                                                   dsi_stat;
  dsi_1_pdcm_period_t                                                pdcm_period;
  dsi_1_dsi_load_t                                                   dsi_load;
  dsi_1_dsi_irq_stat_t                                               dsi_irq_stat;
  dsi_1_dsi_irq_mask_t                                               dsi_irq_mask;
  dsi_1_dsi_cmd_t                                                    dsi_cmd;
  dsi_1_crm_word2_t                                                  crm_word2;
  dsi_1_crm_word1_t                                                  crm_word1;
  dsi_1_packet_stat_t                                                packet_stat;
  dsi_1_frame_stat_t                                                 frame_stat;
  dsi_1_wait_time_t                                                  wait_time;
  dsi_1_sync_t                                                       sync;
} dsi_1_t;

typedef union {
  unsigned short a[sizeof(dsi_1_t)/sizeof(unsigned short)];
  dsi_1_t s;
} dsi_1_u_t;


#define ADDR_DSI_1_DSI_STAT                                          (0x0U)
#define A_DSI_1_DSI_STAT(ba)                                         ((ba) + ADDR_DSI_1_DSI_STAT)
#define R_DSI_1_DSI_STAT(ba)                                         (*(volatile unsigned short *)((unsigned int)A_DSI_1_DSI_STAT(ba)))
#define RES_DSI_1_DSI_STAT                                           (0x0000U)
#define MSB_DSI_1_DSI_STAT                                           (14)
#define LSB_DSI_1_DSI_STAT                                           (0)
#define VBMASK_DSI_1_DSI_STAT                                        (0x7fffU)
#define ROMASK_DSI_1_DSI_STAT                                        (0x7fffU)
#define AADDR_DSI_1_DSI_STAT                                         (BASE_ADDR_DSI_1 + ADDR_DSI_1_DSI_STAT)
#define REG_DSI_1_DSI_STAT                                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_DSI_STAT))

#define ADDR_DSI_1_PDCM_PERIOD                                       (0x4U)
#define A_DSI_1_PDCM_PERIOD(ba)                                      ((ba) + ADDR_DSI_1_PDCM_PERIOD)
#define R_DSI_1_PDCM_PERIOD(ba)                                      (*(volatile unsigned short *)((unsigned int)A_DSI_1_PDCM_PERIOD(ba)))
#define RES_DSI_1_PDCM_PERIOD                                        (0x03e8U)
#define MSB_DSI_1_PDCM_PERIOD                                        (15)
#define LSB_DSI_1_PDCM_PERIOD                                        (0)
#define VBMASK_DSI_1_PDCM_PERIOD                                     (0xffffU)
#define ROMASK_DSI_1_PDCM_PERIOD                                     (0xffffU)
#define AADDR_DSI_1_PDCM_PERIOD                                      (BASE_ADDR_DSI_1 + ADDR_DSI_1_PDCM_PERIOD)
#define REG_DSI_1_PDCM_PERIOD                                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_PDCM_PERIOD))

#define ADDR_DSI_1_DSI_LOAD                                          (0x5U)
#define A_DSI_1_DSI_LOAD(ba)                                         ((ba) + ADDR_DSI_1_DSI_LOAD)
#define R_DSI_1_DSI_LOAD(ba)                                         (*(volatile unsigned short *)((unsigned int)A_DSI_1_DSI_LOAD(ba)))
#define RES_DSI_1_DSI_LOAD                                           (0x4000U)
#define MSB_DSI_1_DSI_LOAD                                           (15)
#define LSB_DSI_1_DSI_LOAD                                           (0)
#define VBMASK_DSI_1_DSI_LOAD                                        (0xc01fU)
#define ROMASK_DSI_1_DSI_LOAD                                        (0xffe0U)
#define AADDR_DSI_1_DSI_LOAD                                         (BASE_ADDR_DSI_1 + ADDR_DSI_1_DSI_LOAD)
#define REG_DSI_1_DSI_LOAD                                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_DSI_LOAD))

#define ADDR_DSI_1_DSI_IRQ_STAT                                      (0x8U)
#define A_DSI_1_DSI_IRQ_STAT(ba)                                     ((ba) + ADDR_DSI_1_DSI_IRQ_STAT)
#define R_DSI_1_DSI_IRQ_STAT(ba)                                     (*(volatile unsigned short *)((unsigned int)A_DSI_1_DSI_IRQ_STAT(ba)))
#define RES_DSI_1_DSI_IRQ_STAT                                       (0x0000U)
#define MSB_DSI_1_DSI_IRQ_STAT                                       (6)
#define LSB_DSI_1_DSI_IRQ_STAT                                       (0)
#define VBMASK_DSI_1_DSI_IRQ_STAT                                    (0x007fU)
#define ROMASK_DSI_1_DSI_IRQ_STAT                                    (0x0000U)
#define AADDR_DSI_1_DSI_IRQ_STAT                                     (BASE_ADDR_DSI_1 + ADDR_DSI_1_DSI_IRQ_STAT)
#define REG_DSI_1_DSI_IRQ_STAT                                       (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_DSI_IRQ_STAT))

#define ADDR_DSI_1_DSI_IRQ_MASK                                      (0x9U)
#define A_DSI_1_DSI_IRQ_MASK(ba)                                     ((ba) + ADDR_DSI_1_DSI_IRQ_MASK)
#define R_DSI_1_DSI_IRQ_MASK(ba)                                     (*(volatile unsigned short *)((unsigned int)A_DSI_1_DSI_IRQ_MASK(ba)))
#define RES_DSI_1_DSI_IRQ_MASK                                       (0x007fU)
#define MSB_DSI_1_DSI_IRQ_MASK                                       (6)
#define LSB_DSI_1_DSI_IRQ_MASK                                       (0)
#define VBMASK_DSI_1_DSI_IRQ_MASK                                    (0x007fU)
#define ROMASK_DSI_1_DSI_IRQ_MASK                                    (0x0000U)
#define AADDR_DSI_1_DSI_IRQ_MASK                                     (BASE_ADDR_DSI_1 + ADDR_DSI_1_DSI_IRQ_MASK)
#define REG_DSI_1_DSI_IRQ_MASK                                       (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_DSI_IRQ_MASK))

#define ADDR_DSI_1_DSI_CMD                                           (0x10U)
#define A_DSI_1_DSI_CMD(ba)                                          ((ba) + ADDR_DSI_1_DSI_CMD)
#define R_DSI_1_DSI_CMD(ba)                                          (*(volatile unsigned short *)((unsigned int)A_DSI_1_DSI_CMD(ba)))
#define RES_DSI_1_DSI_CMD                                            (0x0000U)
#define MSB_DSI_1_DSI_CMD                                            (15)
#define LSB_DSI_1_DSI_CMD                                            (0)
#define VBMASK_DSI_1_DSI_CMD                                         (0xffffU)
#define ROMASK_DSI_1_DSI_CMD                                         (0xffffU)
#define AADDR_DSI_1_DSI_CMD                                          (BASE_ADDR_DSI_1 + ADDR_DSI_1_DSI_CMD)
#define REG_DSI_1_DSI_CMD                                            (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_DSI_CMD))

#define ADDR_DSI_1_CRM_WORD2                                         (0x11U)
#define A_DSI_1_CRM_WORD2(ba)                                        ((ba) + ADDR_DSI_1_CRM_WORD2)
#define R_DSI_1_CRM_WORD2(ba)                                        (*(volatile unsigned short *)((unsigned int)A_DSI_1_CRM_WORD2(ba)))
#define RES_DSI_1_CRM_WORD2                                          (0x00ffU)
#define MSB_DSI_1_CRM_WORD2                                          (15)
#define LSB_DSI_1_CRM_WORD2                                          (0)
#define VBMASK_DSI_1_CRM_WORD2                                       (0xffffU)
#define ROMASK_DSI_1_CRM_WORD2                                       (0xffffU)
#define AADDR_DSI_1_CRM_WORD2                                        (BASE_ADDR_DSI_1 + ADDR_DSI_1_CRM_WORD2)
#define REG_DSI_1_CRM_WORD2                                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_CRM_WORD2))

#define ADDR_DSI_1_CRM_WORD1                                         (0x12U)
#define A_DSI_1_CRM_WORD1(ba)                                        ((ba) + ADDR_DSI_1_CRM_WORD1)
#define R_DSI_1_CRM_WORD1(ba)                                        (*(volatile unsigned short *)((unsigned int)A_DSI_1_CRM_WORD1(ba)))
#define RES_DSI_1_CRM_WORD1                                          (0x0000U)
#define MSB_DSI_1_CRM_WORD1                                          (15)
#define LSB_DSI_1_CRM_WORD1                                          (0)
#define VBMASK_DSI_1_CRM_WORD1                                       (0xffffU)
#define ROMASK_DSI_1_CRM_WORD1                                       (0xffffU)
#define AADDR_DSI_1_CRM_WORD1                                        (BASE_ADDR_DSI_1 + ADDR_DSI_1_CRM_WORD1)
#define REG_DSI_1_CRM_WORD1                                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_CRM_WORD1))

#define ADDR_DSI_1_PACKET_STAT                                       (0x18U)
#define A_DSI_1_PACKET_STAT(ba)                                      ((ba) + ADDR_DSI_1_PACKET_STAT)
#define R_DSI_1_PACKET_STAT(ba)                                      (*(volatile unsigned short *)((unsigned int)A_DSI_1_PACKET_STAT(ba)))
#define RES_DSI_1_PACKET_STAT                                        (0x0000U)
#define MSB_DSI_1_PACKET_STAT                                        (15)
#define LSB_DSI_1_PACKET_STAT                                        (0)
#define VBMASK_DSI_1_PACKET_STAT                                     (0x3fffU)
#define ROMASK_DSI_1_PACKET_STAT                                     (0xffffU)
#define AADDR_DSI_1_PACKET_STAT                                      (BASE_ADDR_DSI_1 + ADDR_DSI_1_PACKET_STAT)
#define REG_DSI_1_PACKET_STAT                                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_PACKET_STAT))

#define ADDR_DSI_1_FRAME_STAT                                        (0x1BU)
#define A_DSI_1_FRAME_STAT(ba)                                       ((ba) + ADDR_DSI_1_FRAME_STAT)
#define R_DSI_1_FRAME_STAT(ba)                                       (*(volatile unsigned short *)((unsigned int)A_DSI_1_FRAME_STAT(ba)))
#define RES_DSI_1_FRAME_STAT                                         (0x0000U)
#define MSB_DSI_1_FRAME_STAT                                         (15)
#define LSB_DSI_1_FRAME_STAT                                         (0)
#define VBMASK_DSI_1_FRAME_STAT                                      (0x80ffU)
#define ROMASK_DSI_1_FRAME_STAT                                      (0xffffU)
#define AADDR_DSI_1_FRAME_STAT                                       (BASE_ADDR_DSI_1 + ADDR_DSI_1_FRAME_STAT)
#define REG_DSI_1_FRAME_STAT                                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_FRAME_STAT))

#define ADDR_DSI_1_WAIT_TIME                                         (0x19U)
#define A_DSI_1_WAIT_TIME(ba)                                        ((ba) + ADDR_DSI_1_WAIT_TIME)
#define R_DSI_1_WAIT_TIME(ba)                                        (*(volatile unsigned short *)((unsigned int)A_DSI_1_WAIT_TIME(ba)))
#define RES_DSI_1_WAIT_TIME                                          (0x0000U)
#define MSB_DSI_1_WAIT_TIME                                          (14)
#define LSB_DSI_1_WAIT_TIME                                          (0)
#define VBMASK_DSI_1_WAIT_TIME                                       (0x7fffU)
#define ROMASK_DSI_1_WAIT_TIME                                       (0x7fffU)
#define AADDR_DSI_1_WAIT_TIME                                        (BASE_ADDR_DSI_1 + ADDR_DSI_1_WAIT_TIME)
#define REG_DSI_1_WAIT_TIME                                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_WAIT_TIME))

#define ADDR_DSI_1_SYNC                                              (0x1AU)
#define A_DSI_1_SYNC(ba)                                             ((ba) + ADDR_DSI_1_SYNC)
#define R_DSI_1_SYNC(ba)                                             (*(volatile unsigned short *)((unsigned int)A_DSI_1_SYNC(ba)))
#define RES_DSI_1_SYNC                                               (0x0000U)
#define MSB_DSI_1_SYNC                                               (4)
#define LSB_DSI_1_SYNC                                               (0)
#define VBMASK_DSI_1_SYNC                                            (0x0013U)
#define ROMASK_DSI_1_SYNC                                            (0x001fU)
#define AADDR_DSI_1_SYNC                                             (BASE_ADDR_DSI_1 + ADDR_DSI_1_SYNC)
#define REG_DSI_1_SYNC                                               (*(volatile unsigned short *)((unsigned int)AADDR_DSI_1_SYNC))

 


// Instance base addresses

#ifndef BASE_ADDR_SPI_CMD_STAT 
#define BASE_ADDR_SPI_CMD_STAT 0x0100U
#define SIZE_SPI_CMD_STAT 0x0010U
#endif

// Register bit field definitions
	 
/* SPI_CMD_STAT_BUF_VALID_COUNT */

#define MSK_SPI_CMD_STAT_BUF_VALID_COUNT_VALID_COUNT                 (0xfff)
#define SFT_SPI_CMD_STAT_BUF_VALID_COUNT_VALID_COUNT                 (0)
#define LSB_SPI_CMD_STAT_BUF_VALID_COUNT_VALID_COUNT                 (0)
#define MSB_SPI_CMD_STAT_BUF_VALID_COUNT_VALID_COUNT                 (11)

typedef struct {
  unsigned short valid_count : 12;
} spi_cmd_stat_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  spi_cmd_stat_buf_valid_count_bf bf;
} spi_cmd_stat_buf_valid_count_t;


/* SPI_CMD_STAT_BUF_FREE */

#define MSK_SPI_CMD_STAT_BUF_FREE_FREE                               (0xffff)
#define SFT_SPI_CMD_STAT_BUF_FREE_FREE                               (0)
#define LSB_SPI_CMD_STAT_BUF_FREE_FREE                               (0)
#define MSB_SPI_CMD_STAT_BUF_FREE_FREE                               (15)

typedef struct {
  unsigned short free : 16;
} spi_cmd_stat_buf_free_bf;
		
typedef union {
  unsigned short val;
  spi_cmd_stat_buf_free_bf bf;
} spi_cmd_stat_buf_free_t;


/* SPI_CMD_STAT_BUF_READ_POINTER */

#define MSK_SPI_CMD_STAT_BUF_READ_POINTER_READ_POINTER               (0xffff)
#define SFT_SPI_CMD_STAT_BUF_READ_POINTER_READ_POINTER               (0)
#define LSB_SPI_CMD_STAT_BUF_READ_POINTER_READ_POINTER               (0)
#define MSB_SPI_CMD_STAT_BUF_READ_POINTER_READ_POINTER               (15)

typedef struct {
  unsigned short read_pointer : 16;
} spi_cmd_stat_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  spi_cmd_stat_buf_read_pointer_bf bf;
} spi_cmd_stat_buf_read_pointer_t;


/* SPI_CMD_STAT_BUF_WRITE_POINTER */

#define MSK_SPI_CMD_STAT_BUF_WRITE_POINTER_WRITE_POINTER             (0xffff)
#define SFT_SPI_CMD_STAT_BUF_WRITE_POINTER_WRITE_POINTER             (0)
#define LSB_SPI_CMD_STAT_BUF_WRITE_POINTER_WRITE_POINTER             (0)
#define MSB_SPI_CMD_STAT_BUF_WRITE_POINTER_WRITE_POINTER             (15)

typedef struct {
  unsigned short write_pointer : 16;
} spi_cmd_stat_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  spi_cmd_stat_buf_write_pointer_bf bf;
} spi_cmd_stat_buf_write_pointer_t;


/* SPI_CMD_STAT_BUF_VALID_POINTER */

#define MSK_SPI_CMD_STAT_BUF_VALID_POINTER_VALID_POINTER             (0xffff)
#define SFT_SPI_CMD_STAT_BUF_VALID_POINTER_VALID_POINTER             (0)
#define LSB_SPI_CMD_STAT_BUF_VALID_POINTER_VALID_POINTER             (0)
#define MSB_SPI_CMD_STAT_BUF_VALID_POINTER_VALID_POINTER             (15)

typedef struct {
  unsigned short valid_pointer : 16;
} spi_cmd_stat_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  spi_cmd_stat_buf_valid_pointer_bf bf;
} spi_cmd_stat_buf_valid_pointer_t;



typedef struct {
  spi_cmd_stat_buf_valid_count_t                                     buf_valid_count;
  spi_cmd_stat_buf_free_t                                            buf_free;
  spi_cmd_stat_buf_read_pointer_t                                    buf_read_pointer;
  spi_cmd_stat_buf_write_pointer_t                                   buf_write_pointer;
  spi_cmd_stat_buf_valid_pointer_t                                   buf_valid_pointer;
} spi_cmd_stat_t;

typedef union {
  unsigned short a[sizeof(spi_cmd_stat_t)/sizeof(unsigned short)];
  spi_cmd_stat_t s;
} spi_cmd_stat_u_t;


#define ADDR_SPI_CMD_STAT_BUF_VALID_COUNT                            (0x0U)
#define A_SPI_CMD_STAT_BUF_VALID_COUNT(ba)                           ((ba) + ADDR_SPI_CMD_STAT_BUF_VALID_COUNT)
#define R_SPI_CMD_STAT_BUF_VALID_COUNT(ba)                           (*(volatile unsigned short *)((unsigned int)A_SPI_CMD_STAT_BUF_VALID_COUNT(ba)))
#define RES_SPI_CMD_STAT_BUF_VALID_COUNT                             (0x0000U)
#define MSB_SPI_CMD_STAT_BUF_VALID_COUNT                             (11)
#define LSB_SPI_CMD_STAT_BUF_VALID_COUNT                             (0)
#define VBMASK_SPI_CMD_STAT_BUF_VALID_COUNT                          (0x0fffU)
#define ROMASK_SPI_CMD_STAT_BUF_VALID_COUNT                          (0x0fffU)
#define AADDR_SPI_CMD_STAT_BUF_VALID_COUNT                           (BASE_ADDR_SPI_CMD_STAT + ADDR_SPI_CMD_STAT_BUF_VALID_COUNT)
#define REG_SPI_CMD_STAT_BUF_VALID_COUNT                             (*(volatile unsigned short *)((unsigned int)AADDR_SPI_CMD_STAT_BUF_VALID_COUNT))

#define ADDR_SPI_CMD_STAT_BUF_FREE                                   (0x2U)
#define A_SPI_CMD_STAT_BUF_FREE(ba)                                  ((ba) + ADDR_SPI_CMD_STAT_BUF_FREE)
#define R_SPI_CMD_STAT_BUF_FREE(ba)                                  (*(volatile unsigned short *)((unsigned int)A_SPI_CMD_STAT_BUF_FREE(ba)))
#define RES_SPI_CMD_STAT_BUF_FREE                                    (0x0000U)
#define MSB_SPI_CMD_STAT_BUF_FREE                                    (15)
#define LSB_SPI_CMD_STAT_BUF_FREE                                    (0)
#define VBMASK_SPI_CMD_STAT_BUF_FREE                                 (0xffffU)
#define ROMASK_SPI_CMD_STAT_BUF_FREE                                 (0xffffU)
#define AADDR_SPI_CMD_STAT_BUF_FREE                                  (BASE_ADDR_SPI_CMD_STAT + ADDR_SPI_CMD_STAT_BUF_FREE)
#define REG_SPI_CMD_STAT_BUF_FREE                                    (*(volatile unsigned short *)((unsigned int)AADDR_SPI_CMD_STAT_BUF_FREE))

#define ADDR_SPI_CMD_STAT_BUF_READ_POINTER                           (0x8U)
#define A_SPI_CMD_STAT_BUF_READ_POINTER(ba)                          ((ba) + ADDR_SPI_CMD_STAT_BUF_READ_POINTER)
#define R_SPI_CMD_STAT_BUF_READ_POINTER(ba)                          (*(volatile unsigned short *)((unsigned int)A_SPI_CMD_STAT_BUF_READ_POINTER(ba)))
#define RES_SPI_CMD_STAT_BUF_READ_POINTER                            (0x0000U)
#define MSB_SPI_CMD_STAT_BUF_READ_POINTER                            (15)
#define LSB_SPI_CMD_STAT_BUF_READ_POINTER                            (0)
#define VBMASK_SPI_CMD_STAT_BUF_READ_POINTER                         (0xffffU)
#define ROMASK_SPI_CMD_STAT_BUF_READ_POINTER                         (0xffffU)
#define AADDR_SPI_CMD_STAT_BUF_READ_POINTER                          (BASE_ADDR_SPI_CMD_STAT + ADDR_SPI_CMD_STAT_BUF_READ_POINTER)
#define REG_SPI_CMD_STAT_BUF_READ_POINTER                            (*(volatile unsigned short *)((unsigned int)AADDR_SPI_CMD_STAT_BUF_READ_POINTER))

#define ADDR_SPI_CMD_STAT_BUF_WRITE_POINTER                          (0x9U)
#define A_SPI_CMD_STAT_BUF_WRITE_POINTER(ba)                         ((ba) + ADDR_SPI_CMD_STAT_BUF_WRITE_POINTER)
#define R_SPI_CMD_STAT_BUF_WRITE_POINTER(ba)                         (*(volatile unsigned short *)((unsigned int)A_SPI_CMD_STAT_BUF_WRITE_POINTER(ba)))
#define RES_SPI_CMD_STAT_BUF_WRITE_POINTER                           (0x0000U)
#define MSB_SPI_CMD_STAT_BUF_WRITE_POINTER                           (15)
#define LSB_SPI_CMD_STAT_BUF_WRITE_POINTER                           (0)
#define VBMASK_SPI_CMD_STAT_BUF_WRITE_POINTER                        (0xffffU)
#define ROMASK_SPI_CMD_STAT_BUF_WRITE_POINTER                        (0xffffU)
#define AADDR_SPI_CMD_STAT_BUF_WRITE_POINTER                         (BASE_ADDR_SPI_CMD_STAT + ADDR_SPI_CMD_STAT_BUF_WRITE_POINTER)
#define REG_SPI_CMD_STAT_BUF_WRITE_POINTER                           (*(volatile unsigned short *)((unsigned int)AADDR_SPI_CMD_STAT_BUF_WRITE_POINTER))

#define ADDR_SPI_CMD_STAT_BUF_VALID_POINTER                          (0xAU)
#define A_SPI_CMD_STAT_BUF_VALID_POINTER(ba)                         ((ba) + ADDR_SPI_CMD_STAT_BUF_VALID_POINTER)
#define R_SPI_CMD_STAT_BUF_VALID_POINTER(ba)                         (*(volatile unsigned short *)((unsigned int)A_SPI_CMD_STAT_BUF_VALID_POINTER(ba)))
#define RES_SPI_CMD_STAT_BUF_VALID_POINTER                           (0x0000U)
#define MSB_SPI_CMD_STAT_BUF_VALID_POINTER                           (15)
#define LSB_SPI_CMD_STAT_BUF_VALID_POINTER                           (0)
#define VBMASK_SPI_CMD_STAT_BUF_VALID_POINTER                        (0xffffU)
#define ROMASK_SPI_CMD_STAT_BUF_VALID_POINTER                        (0xffffU)
#define AADDR_SPI_CMD_STAT_BUF_VALID_POINTER                         (BASE_ADDR_SPI_CMD_STAT + ADDR_SPI_CMD_STAT_BUF_VALID_POINTER)
#define REG_SPI_CMD_STAT_BUF_VALID_POINTER                           (*(volatile unsigned short *)((unsigned int)AADDR_SPI_CMD_STAT_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CMD_STAT_0 
#define BASE_ADDR_DSI_CMD_STAT_0 0x0110U
#define SIZE_DSI_CMD_STAT_0 0x0010U
#endif

// Register bit field definitions
	 
/* DSI_CMD_STAT_0_BUF_VALID_COUNT */

#define MSK_DSI_CMD_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (0xfff)
#define SFT_DSI_CMD_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (0)
#define LSB_DSI_CMD_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (0)
#define MSB_DSI_CMD_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (11)

typedef struct {
  unsigned short valid_count : 12;
} dsi_cmd_stat_0_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_0_buf_valid_count_bf bf;
} dsi_cmd_stat_0_buf_valid_count_t;


/* DSI_CMD_STAT_0_BUF_FREE */

#define MSK_DSI_CMD_STAT_0_BUF_FREE_FREE                             (0xffff)
#define SFT_DSI_CMD_STAT_0_BUF_FREE_FREE                             (0)
#define LSB_DSI_CMD_STAT_0_BUF_FREE_FREE                             (0)
#define MSB_DSI_CMD_STAT_0_BUF_FREE_FREE                             (15)

typedef struct {
  unsigned short free : 16;
} dsi_cmd_stat_0_buf_free_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_0_buf_free_bf bf;
} dsi_cmd_stat_0_buf_free_t;


/* DSI_CMD_STAT_0_BUF_READ_POINTER */

#define MSK_DSI_CMD_STAT_0_BUF_READ_POINTER_READ_POINTER             (0xffff)
#define SFT_DSI_CMD_STAT_0_BUF_READ_POINTER_READ_POINTER             (0)
#define LSB_DSI_CMD_STAT_0_BUF_READ_POINTER_READ_POINTER             (0)
#define MSB_DSI_CMD_STAT_0_BUF_READ_POINTER_READ_POINTER             (15)

typedef struct {
  unsigned short read_pointer : 16;
} dsi_cmd_stat_0_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_0_buf_read_pointer_bf bf;
} dsi_cmd_stat_0_buf_read_pointer_t;


/* DSI_CMD_STAT_0_BUF_WRITE_POINTER */

#define MSK_DSI_CMD_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (0xffff)
#define SFT_DSI_CMD_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define LSB_DSI_CMD_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define MSB_DSI_CMD_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (15)

typedef struct {
  unsigned short write_pointer : 16;
} dsi_cmd_stat_0_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_0_buf_write_pointer_bf bf;
} dsi_cmd_stat_0_buf_write_pointer_t;


/* DSI_CMD_STAT_0_BUF_VALID_POINTER */

#define MSK_DSI_CMD_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (0xffff)
#define SFT_DSI_CMD_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (0)
#define LSB_DSI_CMD_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (0)
#define MSB_DSI_CMD_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (15)

typedef struct {
  unsigned short valid_pointer : 16;
} dsi_cmd_stat_0_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_0_buf_valid_pointer_bf bf;
} dsi_cmd_stat_0_buf_valid_pointer_t;



typedef struct {
  dsi_cmd_stat_0_buf_valid_count_t                                   buf_valid_count;
  dsi_cmd_stat_0_buf_free_t                                          buf_free;
  dsi_cmd_stat_0_buf_read_pointer_t                                  buf_read_pointer;
  dsi_cmd_stat_0_buf_write_pointer_t                                 buf_write_pointer;
  dsi_cmd_stat_0_buf_valid_pointer_t                                 buf_valid_pointer;
} dsi_cmd_stat_0_t;

typedef union {
  unsigned short a[sizeof(dsi_cmd_stat_0_t)/sizeof(unsigned short)];
  dsi_cmd_stat_0_t s;
} dsi_cmd_stat_0_u_t;


#define ADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT                          (0x0U)
#define A_DSI_CMD_STAT_0_BUF_VALID_COUNT(ba)                         ((ba) + ADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT)
#define R_DSI_CMD_STAT_0_BUF_VALID_COUNT(ba)                         (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_0_BUF_VALID_COUNT(ba)))
#define RES_DSI_CMD_STAT_0_BUF_VALID_COUNT                           (0x0000U)
#define MSB_DSI_CMD_STAT_0_BUF_VALID_COUNT                           (11)
#define LSB_DSI_CMD_STAT_0_BUF_VALID_COUNT                           (0)
#define VBMASK_DSI_CMD_STAT_0_BUF_VALID_COUNT                        (0x0fffU)
#define ROMASK_DSI_CMD_STAT_0_BUF_VALID_COUNT                        (0x0fffU)
#define AADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT                         (BASE_ADDR_DSI_CMD_STAT_0 + ADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT)
#define REG_DSI_CMD_STAT_0_BUF_VALID_COUNT                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_0_BUF_VALID_COUNT))

#define ADDR_DSI_CMD_STAT_0_BUF_FREE                                 (0x2U)
#define A_DSI_CMD_STAT_0_BUF_FREE(ba)                                ((ba) + ADDR_DSI_CMD_STAT_0_BUF_FREE)
#define R_DSI_CMD_STAT_0_BUF_FREE(ba)                                (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_0_BUF_FREE(ba)))
#define RES_DSI_CMD_STAT_0_BUF_FREE                                  (0x0000U)
#define MSB_DSI_CMD_STAT_0_BUF_FREE                                  (15)
#define LSB_DSI_CMD_STAT_0_BUF_FREE                                  (0)
#define VBMASK_DSI_CMD_STAT_0_BUF_FREE                               (0xffffU)
#define ROMASK_DSI_CMD_STAT_0_BUF_FREE                               (0xffffU)
#define AADDR_DSI_CMD_STAT_0_BUF_FREE                                (BASE_ADDR_DSI_CMD_STAT_0 + ADDR_DSI_CMD_STAT_0_BUF_FREE)
#define REG_DSI_CMD_STAT_0_BUF_FREE                                  (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_0_BUF_FREE))

#define ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER                         (0x8U)
#define A_DSI_CMD_STAT_0_BUF_READ_POINTER(ba)                        ((ba) + ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER)
#define R_DSI_CMD_STAT_0_BUF_READ_POINTER(ba)                        (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_0_BUF_READ_POINTER(ba)))
#define RES_DSI_CMD_STAT_0_BUF_READ_POINTER                          (0x0000U)
#define MSB_DSI_CMD_STAT_0_BUF_READ_POINTER                          (15)
#define LSB_DSI_CMD_STAT_0_BUF_READ_POINTER                          (0)
#define VBMASK_DSI_CMD_STAT_0_BUF_READ_POINTER                       (0xffffU)
#define ROMASK_DSI_CMD_STAT_0_BUF_READ_POINTER                       (0xffffU)
#define AADDR_DSI_CMD_STAT_0_BUF_READ_POINTER                        (BASE_ADDR_DSI_CMD_STAT_0 + ADDR_DSI_CMD_STAT_0_BUF_READ_POINTER)
#define REG_DSI_CMD_STAT_0_BUF_READ_POINTER                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_0_BUF_READ_POINTER))

#define ADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER                        (0x9U)
#define A_DSI_CMD_STAT_0_BUF_WRITE_POINTER(ba)                       ((ba) + ADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER)
#define R_DSI_CMD_STAT_0_BUF_WRITE_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_0_BUF_WRITE_POINTER(ba)))
#define RES_DSI_CMD_STAT_0_BUF_WRITE_POINTER                         (0x0000U)
#define MSB_DSI_CMD_STAT_0_BUF_WRITE_POINTER                         (15)
#define LSB_DSI_CMD_STAT_0_BUF_WRITE_POINTER                         (0)
#define VBMASK_DSI_CMD_STAT_0_BUF_WRITE_POINTER                      (0xffffU)
#define ROMASK_DSI_CMD_STAT_0_BUF_WRITE_POINTER                      (0xffffU)
#define AADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER                       (BASE_ADDR_DSI_CMD_STAT_0 + ADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER)
#define REG_DSI_CMD_STAT_0_BUF_WRITE_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_0_BUF_WRITE_POINTER))

#define ADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER                        (0xAU)
#define A_DSI_CMD_STAT_0_BUF_VALID_POINTER(ba)                       ((ba) + ADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER)
#define R_DSI_CMD_STAT_0_BUF_VALID_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_0_BUF_VALID_POINTER(ba)))
#define RES_DSI_CMD_STAT_0_BUF_VALID_POINTER                         (0x0000U)
#define MSB_DSI_CMD_STAT_0_BUF_VALID_POINTER                         (15)
#define LSB_DSI_CMD_STAT_0_BUF_VALID_POINTER                         (0)
#define VBMASK_DSI_CMD_STAT_0_BUF_VALID_POINTER                      (0xffffU)
#define ROMASK_DSI_CMD_STAT_0_BUF_VALID_POINTER                      (0xffffU)
#define AADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER                       (BASE_ADDR_DSI_CMD_STAT_0 + ADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER)
#define REG_DSI_CMD_STAT_0_BUF_VALID_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_0_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CMD_STAT_1 
#define BASE_ADDR_DSI_CMD_STAT_1 0x0120U
#define SIZE_DSI_CMD_STAT_1 0x0010U
#endif

// Register bit field definitions
	 
/* DSI_CMD_STAT_1_BUF_VALID_COUNT */

#define MSK_DSI_CMD_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (0xfff)
#define SFT_DSI_CMD_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (0)
#define LSB_DSI_CMD_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (0)
#define MSB_DSI_CMD_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (11)

typedef struct {
  unsigned short valid_count : 12;
} dsi_cmd_stat_1_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_1_buf_valid_count_bf bf;
} dsi_cmd_stat_1_buf_valid_count_t;


/* DSI_CMD_STAT_1_BUF_FREE */

#define MSK_DSI_CMD_STAT_1_BUF_FREE_FREE                             (0xffff)
#define SFT_DSI_CMD_STAT_1_BUF_FREE_FREE                             (0)
#define LSB_DSI_CMD_STAT_1_BUF_FREE_FREE                             (0)
#define MSB_DSI_CMD_STAT_1_BUF_FREE_FREE                             (15)

typedef struct {
  unsigned short free : 16;
} dsi_cmd_stat_1_buf_free_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_1_buf_free_bf bf;
} dsi_cmd_stat_1_buf_free_t;


/* DSI_CMD_STAT_1_BUF_READ_POINTER */

#define MSK_DSI_CMD_STAT_1_BUF_READ_POINTER_READ_POINTER             (0xffff)
#define SFT_DSI_CMD_STAT_1_BUF_READ_POINTER_READ_POINTER             (0)
#define LSB_DSI_CMD_STAT_1_BUF_READ_POINTER_READ_POINTER             (0)
#define MSB_DSI_CMD_STAT_1_BUF_READ_POINTER_READ_POINTER             (15)

typedef struct {
  unsigned short read_pointer : 16;
} dsi_cmd_stat_1_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_1_buf_read_pointer_bf bf;
} dsi_cmd_stat_1_buf_read_pointer_t;


/* DSI_CMD_STAT_1_BUF_WRITE_POINTER */

#define MSK_DSI_CMD_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (0xffff)
#define SFT_DSI_CMD_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define LSB_DSI_CMD_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define MSB_DSI_CMD_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (15)

typedef struct {
  unsigned short write_pointer : 16;
} dsi_cmd_stat_1_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_1_buf_write_pointer_bf bf;
} dsi_cmd_stat_1_buf_write_pointer_t;


/* DSI_CMD_STAT_1_BUF_VALID_POINTER */

#define MSK_DSI_CMD_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (0xffff)
#define SFT_DSI_CMD_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (0)
#define LSB_DSI_CMD_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (0)
#define MSB_DSI_CMD_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (15)

typedef struct {
  unsigned short valid_pointer : 16;
} dsi_cmd_stat_1_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_cmd_stat_1_buf_valid_pointer_bf bf;
} dsi_cmd_stat_1_buf_valid_pointer_t;



typedef struct {
  dsi_cmd_stat_1_buf_valid_count_t                                   buf_valid_count;
  dsi_cmd_stat_1_buf_free_t                                          buf_free;
  dsi_cmd_stat_1_buf_read_pointer_t                                  buf_read_pointer;
  dsi_cmd_stat_1_buf_write_pointer_t                                 buf_write_pointer;
  dsi_cmd_stat_1_buf_valid_pointer_t                                 buf_valid_pointer;
} dsi_cmd_stat_1_t;

typedef union {
  unsigned short a[sizeof(dsi_cmd_stat_1_t)/sizeof(unsigned short)];
  dsi_cmd_stat_1_t s;
} dsi_cmd_stat_1_u_t;


#define ADDR_DSI_CMD_STAT_1_BUF_VALID_COUNT                          (0x0U)
#define A_DSI_CMD_STAT_1_BUF_VALID_COUNT(ba)                         ((ba) + ADDR_DSI_CMD_STAT_1_BUF_VALID_COUNT)
#define R_DSI_CMD_STAT_1_BUF_VALID_COUNT(ba)                         (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_1_BUF_VALID_COUNT(ba)))
#define RES_DSI_CMD_STAT_1_BUF_VALID_COUNT                           (0x0000U)
#define MSB_DSI_CMD_STAT_1_BUF_VALID_COUNT                           (11)
#define LSB_DSI_CMD_STAT_1_BUF_VALID_COUNT                           (0)
#define VBMASK_DSI_CMD_STAT_1_BUF_VALID_COUNT                        (0x0fffU)
#define ROMASK_DSI_CMD_STAT_1_BUF_VALID_COUNT                        (0x0fffU)
#define AADDR_DSI_CMD_STAT_1_BUF_VALID_COUNT                         (BASE_ADDR_DSI_CMD_STAT_1 + ADDR_DSI_CMD_STAT_1_BUF_VALID_COUNT)
#define REG_DSI_CMD_STAT_1_BUF_VALID_COUNT                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_1_BUF_VALID_COUNT))

#define ADDR_DSI_CMD_STAT_1_BUF_FREE                                 (0x2U)
#define A_DSI_CMD_STAT_1_BUF_FREE(ba)                                ((ba) + ADDR_DSI_CMD_STAT_1_BUF_FREE)
#define R_DSI_CMD_STAT_1_BUF_FREE(ba)                                (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_1_BUF_FREE(ba)))
#define RES_DSI_CMD_STAT_1_BUF_FREE                                  (0x0000U)
#define MSB_DSI_CMD_STAT_1_BUF_FREE                                  (15)
#define LSB_DSI_CMD_STAT_1_BUF_FREE                                  (0)
#define VBMASK_DSI_CMD_STAT_1_BUF_FREE                               (0xffffU)
#define ROMASK_DSI_CMD_STAT_1_BUF_FREE                               (0xffffU)
#define AADDR_DSI_CMD_STAT_1_BUF_FREE                                (BASE_ADDR_DSI_CMD_STAT_1 + ADDR_DSI_CMD_STAT_1_BUF_FREE)
#define REG_DSI_CMD_STAT_1_BUF_FREE                                  (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_1_BUF_FREE))

#define ADDR_DSI_CMD_STAT_1_BUF_READ_POINTER                         (0x8U)
#define A_DSI_CMD_STAT_1_BUF_READ_POINTER(ba)                        ((ba) + ADDR_DSI_CMD_STAT_1_BUF_READ_POINTER)
#define R_DSI_CMD_STAT_1_BUF_READ_POINTER(ba)                        (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_1_BUF_READ_POINTER(ba)))
#define RES_DSI_CMD_STAT_1_BUF_READ_POINTER                          (0x0000U)
#define MSB_DSI_CMD_STAT_1_BUF_READ_POINTER                          (15)
#define LSB_DSI_CMD_STAT_1_BUF_READ_POINTER                          (0)
#define VBMASK_DSI_CMD_STAT_1_BUF_READ_POINTER                       (0xffffU)
#define ROMASK_DSI_CMD_STAT_1_BUF_READ_POINTER                       (0xffffU)
#define AADDR_DSI_CMD_STAT_1_BUF_READ_POINTER                        (BASE_ADDR_DSI_CMD_STAT_1 + ADDR_DSI_CMD_STAT_1_BUF_READ_POINTER)
#define REG_DSI_CMD_STAT_1_BUF_READ_POINTER                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_1_BUF_READ_POINTER))

#define ADDR_DSI_CMD_STAT_1_BUF_WRITE_POINTER                        (0x9U)
#define A_DSI_CMD_STAT_1_BUF_WRITE_POINTER(ba)                       ((ba) + ADDR_DSI_CMD_STAT_1_BUF_WRITE_POINTER)
#define R_DSI_CMD_STAT_1_BUF_WRITE_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_1_BUF_WRITE_POINTER(ba)))
#define RES_DSI_CMD_STAT_1_BUF_WRITE_POINTER                         (0x0000U)
#define MSB_DSI_CMD_STAT_1_BUF_WRITE_POINTER                         (15)
#define LSB_DSI_CMD_STAT_1_BUF_WRITE_POINTER                         (0)
#define VBMASK_DSI_CMD_STAT_1_BUF_WRITE_POINTER                      (0xffffU)
#define ROMASK_DSI_CMD_STAT_1_BUF_WRITE_POINTER                      (0xffffU)
#define AADDR_DSI_CMD_STAT_1_BUF_WRITE_POINTER                       (BASE_ADDR_DSI_CMD_STAT_1 + ADDR_DSI_CMD_STAT_1_BUF_WRITE_POINTER)
#define REG_DSI_CMD_STAT_1_BUF_WRITE_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_1_BUF_WRITE_POINTER))

#define ADDR_DSI_CMD_STAT_1_BUF_VALID_POINTER                        (0xAU)
#define A_DSI_CMD_STAT_1_BUF_VALID_POINTER(ba)                       ((ba) + ADDR_DSI_CMD_STAT_1_BUF_VALID_POINTER)
#define R_DSI_CMD_STAT_1_BUF_VALID_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CMD_STAT_1_BUF_VALID_POINTER(ba)))
#define RES_DSI_CMD_STAT_1_BUF_VALID_POINTER                         (0x0000U)
#define MSB_DSI_CMD_STAT_1_BUF_VALID_POINTER                         (15)
#define LSB_DSI_CMD_STAT_1_BUF_VALID_POINTER                         (0)
#define VBMASK_DSI_CMD_STAT_1_BUF_VALID_POINTER                      (0xffffU)
#define ROMASK_DSI_CMD_STAT_1_BUF_VALID_POINTER                      (0xffffU)
#define AADDR_DSI_CMD_STAT_1_BUF_VALID_POINTER                       (BASE_ADDR_DSI_CMD_STAT_1 + ADDR_DSI_CMD_STAT_1_BUF_VALID_POINTER)
#define REG_DSI_CMD_STAT_1_BUF_VALID_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CMD_STAT_1_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CRM_STAT_0 
#define BASE_ADDR_DSI_CRM_STAT_0 0x0130U
#define SIZE_DSI_CRM_STAT_0 0x0010U
#endif

// Register bit field definitions
	 
/* DSI_CRM_STAT_0_BUF_VALID_COUNT */

#define MSK_DSI_CRM_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (0xfff)
#define SFT_DSI_CRM_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (0)
#define LSB_DSI_CRM_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (0)
#define MSB_DSI_CRM_STAT_0_BUF_VALID_COUNT_VALID_COUNT               (11)

typedef struct {
  unsigned short valid_count : 12;
} dsi_crm_stat_0_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_0_buf_valid_count_bf bf;
} dsi_crm_stat_0_buf_valid_count_t;


/* DSI_CRM_STAT_0_BUF_FREE */

#define MSK_DSI_CRM_STAT_0_BUF_FREE_FREE                             (0xffff)
#define SFT_DSI_CRM_STAT_0_BUF_FREE_FREE                             (0)
#define LSB_DSI_CRM_STAT_0_BUF_FREE_FREE                             (0)
#define MSB_DSI_CRM_STAT_0_BUF_FREE_FREE                             (15)

typedef struct {
  unsigned short free : 16;
} dsi_crm_stat_0_buf_free_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_0_buf_free_bf bf;
} dsi_crm_stat_0_buf_free_t;


/* DSI_CRM_STAT_0_BUF_READ_POINTER */

#define MSK_DSI_CRM_STAT_0_BUF_READ_POINTER_READ_POINTER             (0xffff)
#define SFT_DSI_CRM_STAT_0_BUF_READ_POINTER_READ_POINTER             (0)
#define LSB_DSI_CRM_STAT_0_BUF_READ_POINTER_READ_POINTER             (0)
#define MSB_DSI_CRM_STAT_0_BUF_READ_POINTER_READ_POINTER             (15)

typedef struct {
  unsigned short read_pointer : 16;
} dsi_crm_stat_0_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_0_buf_read_pointer_bf bf;
} dsi_crm_stat_0_buf_read_pointer_t;


/* DSI_CRM_STAT_0_BUF_WRITE_POINTER */

#define MSK_DSI_CRM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (0xffff)
#define SFT_DSI_CRM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define LSB_DSI_CRM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define MSB_DSI_CRM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER           (15)

typedef struct {
  unsigned short write_pointer : 16;
} dsi_crm_stat_0_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_0_buf_write_pointer_bf bf;
} dsi_crm_stat_0_buf_write_pointer_t;


/* DSI_CRM_STAT_0_BUF_VALID_POINTER */

#define MSK_DSI_CRM_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (0xffff)
#define SFT_DSI_CRM_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (0)
#define LSB_DSI_CRM_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (0)
#define MSB_DSI_CRM_STAT_0_BUF_VALID_POINTER_VALID_POINTER           (15)

typedef struct {
  unsigned short valid_pointer : 16;
} dsi_crm_stat_0_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_0_buf_valid_pointer_bf bf;
} dsi_crm_stat_0_buf_valid_pointer_t;



typedef struct {
  dsi_crm_stat_0_buf_valid_count_t                                   buf_valid_count;
  dsi_crm_stat_0_buf_free_t                                          buf_free;
  dsi_crm_stat_0_buf_read_pointer_t                                  buf_read_pointer;
  dsi_crm_stat_0_buf_write_pointer_t                                 buf_write_pointer;
  dsi_crm_stat_0_buf_valid_pointer_t                                 buf_valid_pointer;
} dsi_crm_stat_0_t;

typedef union {
  unsigned short a[sizeof(dsi_crm_stat_0_t)/sizeof(unsigned short)];
  dsi_crm_stat_0_t s;
} dsi_crm_stat_0_u_t;


#define ADDR_DSI_CRM_STAT_0_BUF_VALID_COUNT                          (0x0U)
#define A_DSI_CRM_STAT_0_BUF_VALID_COUNT(ba)                         ((ba) + ADDR_DSI_CRM_STAT_0_BUF_VALID_COUNT)
#define R_DSI_CRM_STAT_0_BUF_VALID_COUNT(ba)                         (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_0_BUF_VALID_COUNT(ba)))
#define RES_DSI_CRM_STAT_0_BUF_VALID_COUNT                           (0x0000U)
#define MSB_DSI_CRM_STAT_0_BUF_VALID_COUNT                           (11)
#define LSB_DSI_CRM_STAT_0_BUF_VALID_COUNT                           (0)
#define VBMASK_DSI_CRM_STAT_0_BUF_VALID_COUNT                        (0x0fffU)
#define ROMASK_DSI_CRM_STAT_0_BUF_VALID_COUNT                        (0x0fffU)
#define AADDR_DSI_CRM_STAT_0_BUF_VALID_COUNT                         (BASE_ADDR_DSI_CRM_STAT_0 + ADDR_DSI_CRM_STAT_0_BUF_VALID_COUNT)
#define REG_DSI_CRM_STAT_0_BUF_VALID_COUNT                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_0_BUF_VALID_COUNT))

#define ADDR_DSI_CRM_STAT_0_BUF_FREE                                 (0x2U)
#define A_DSI_CRM_STAT_0_BUF_FREE(ba)                                ((ba) + ADDR_DSI_CRM_STAT_0_BUF_FREE)
#define R_DSI_CRM_STAT_0_BUF_FREE(ba)                                (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_0_BUF_FREE(ba)))
#define RES_DSI_CRM_STAT_0_BUF_FREE                                  (0x0000U)
#define MSB_DSI_CRM_STAT_0_BUF_FREE                                  (15)
#define LSB_DSI_CRM_STAT_0_BUF_FREE                                  (0)
#define VBMASK_DSI_CRM_STAT_0_BUF_FREE                               (0xffffU)
#define ROMASK_DSI_CRM_STAT_0_BUF_FREE                               (0xffffU)
#define AADDR_DSI_CRM_STAT_0_BUF_FREE                                (BASE_ADDR_DSI_CRM_STAT_0 + ADDR_DSI_CRM_STAT_0_BUF_FREE)
#define REG_DSI_CRM_STAT_0_BUF_FREE                                  (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_0_BUF_FREE))

#define ADDR_DSI_CRM_STAT_0_BUF_READ_POINTER                         (0x8U)
#define A_DSI_CRM_STAT_0_BUF_READ_POINTER(ba)                        ((ba) + ADDR_DSI_CRM_STAT_0_BUF_READ_POINTER)
#define R_DSI_CRM_STAT_0_BUF_READ_POINTER(ba)                        (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_0_BUF_READ_POINTER(ba)))
#define RES_DSI_CRM_STAT_0_BUF_READ_POINTER                          (0x0000U)
#define MSB_DSI_CRM_STAT_0_BUF_READ_POINTER                          (15)
#define LSB_DSI_CRM_STAT_0_BUF_READ_POINTER                          (0)
#define VBMASK_DSI_CRM_STAT_0_BUF_READ_POINTER                       (0xffffU)
#define ROMASK_DSI_CRM_STAT_0_BUF_READ_POINTER                       (0xffffU)
#define AADDR_DSI_CRM_STAT_0_BUF_READ_POINTER                        (BASE_ADDR_DSI_CRM_STAT_0 + ADDR_DSI_CRM_STAT_0_BUF_READ_POINTER)
#define REG_DSI_CRM_STAT_0_BUF_READ_POINTER                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_0_BUF_READ_POINTER))

#define ADDR_DSI_CRM_STAT_0_BUF_WRITE_POINTER                        (0x9U)
#define A_DSI_CRM_STAT_0_BUF_WRITE_POINTER(ba)                       ((ba) + ADDR_DSI_CRM_STAT_0_BUF_WRITE_POINTER)
#define R_DSI_CRM_STAT_0_BUF_WRITE_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_0_BUF_WRITE_POINTER(ba)))
#define RES_DSI_CRM_STAT_0_BUF_WRITE_POINTER                         (0x0000U)
#define MSB_DSI_CRM_STAT_0_BUF_WRITE_POINTER                         (15)
#define LSB_DSI_CRM_STAT_0_BUF_WRITE_POINTER                         (0)
#define VBMASK_DSI_CRM_STAT_0_BUF_WRITE_POINTER                      (0xffffU)
#define ROMASK_DSI_CRM_STAT_0_BUF_WRITE_POINTER                      (0xffffU)
#define AADDR_DSI_CRM_STAT_0_BUF_WRITE_POINTER                       (BASE_ADDR_DSI_CRM_STAT_0 + ADDR_DSI_CRM_STAT_0_BUF_WRITE_POINTER)
#define REG_DSI_CRM_STAT_0_BUF_WRITE_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_0_BUF_WRITE_POINTER))

#define ADDR_DSI_CRM_STAT_0_BUF_VALID_POINTER                        (0xAU)
#define A_DSI_CRM_STAT_0_BUF_VALID_POINTER(ba)                       ((ba) + ADDR_DSI_CRM_STAT_0_BUF_VALID_POINTER)
#define R_DSI_CRM_STAT_0_BUF_VALID_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_0_BUF_VALID_POINTER(ba)))
#define RES_DSI_CRM_STAT_0_BUF_VALID_POINTER                         (0x0000U)
#define MSB_DSI_CRM_STAT_0_BUF_VALID_POINTER                         (15)
#define LSB_DSI_CRM_STAT_0_BUF_VALID_POINTER                         (0)
#define VBMASK_DSI_CRM_STAT_0_BUF_VALID_POINTER                      (0xffffU)
#define ROMASK_DSI_CRM_STAT_0_BUF_VALID_POINTER                      (0xffffU)
#define AADDR_DSI_CRM_STAT_0_BUF_VALID_POINTER                       (BASE_ADDR_DSI_CRM_STAT_0 + ADDR_DSI_CRM_STAT_0_BUF_VALID_POINTER)
#define REG_DSI_CRM_STAT_0_BUF_VALID_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_0_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CRM_STAT_1 
#define BASE_ADDR_DSI_CRM_STAT_1 0x0140U
#define SIZE_DSI_CRM_STAT_1 0x0010U
#endif

// Register bit field definitions
	 
/* DSI_CRM_STAT_1_BUF_VALID_COUNT */

#define MSK_DSI_CRM_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (0xfff)
#define SFT_DSI_CRM_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (0)
#define LSB_DSI_CRM_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (0)
#define MSB_DSI_CRM_STAT_1_BUF_VALID_COUNT_VALID_COUNT               (11)

typedef struct {
  unsigned short valid_count : 12;
} dsi_crm_stat_1_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_1_buf_valid_count_bf bf;
} dsi_crm_stat_1_buf_valid_count_t;


/* DSI_CRM_STAT_1_BUF_FREE */

#define MSK_DSI_CRM_STAT_1_BUF_FREE_FREE                             (0xffff)
#define SFT_DSI_CRM_STAT_1_BUF_FREE_FREE                             (0)
#define LSB_DSI_CRM_STAT_1_BUF_FREE_FREE                             (0)
#define MSB_DSI_CRM_STAT_1_BUF_FREE_FREE                             (15)

typedef struct {
  unsigned short free : 16;
} dsi_crm_stat_1_buf_free_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_1_buf_free_bf bf;
} dsi_crm_stat_1_buf_free_t;


/* DSI_CRM_STAT_1_BUF_READ_POINTER */

#define MSK_DSI_CRM_STAT_1_BUF_READ_POINTER_READ_POINTER             (0xffff)
#define SFT_DSI_CRM_STAT_1_BUF_READ_POINTER_READ_POINTER             (0)
#define LSB_DSI_CRM_STAT_1_BUF_READ_POINTER_READ_POINTER             (0)
#define MSB_DSI_CRM_STAT_1_BUF_READ_POINTER_READ_POINTER             (15)

typedef struct {
  unsigned short read_pointer : 16;
} dsi_crm_stat_1_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_1_buf_read_pointer_bf bf;
} dsi_crm_stat_1_buf_read_pointer_t;


/* DSI_CRM_STAT_1_BUF_WRITE_POINTER */

#define MSK_DSI_CRM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (0xffff)
#define SFT_DSI_CRM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define LSB_DSI_CRM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (0)
#define MSB_DSI_CRM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER           (15)

typedef struct {
  unsigned short write_pointer : 16;
} dsi_crm_stat_1_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_1_buf_write_pointer_bf bf;
} dsi_crm_stat_1_buf_write_pointer_t;


/* DSI_CRM_STAT_1_BUF_VALID_POINTER */

#define MSK_DSI_CRM_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (0xffff)
#define SFT_DSI_CRM_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (0)
#define LSB_DSI_CRM_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (0)
#define MSB_DSI_CRM_STAT_1_BUF_VALID_POINTER_VALID_POINTER           (15)

typedef struct {
  unsigned short valid_pointer : 16;
} dsi_crm_stat_1_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_crm_stat_1_buf_valid_pointer_bf bf;
} dsi_crm_stat_1_buf_valid_pointer_t;



typedef struct {
  dsi_crm_stat_1_buf_valid_count_t                                   buf_valid_count;
  dsi_crm_stat_1_buf_free_t                                          buf_free;
  dsi_crm_stat_1_buf_read_pointer_t                                  buf_read_pointer;
  dsi_crm_stat_1_buf_write_pointer_t                                 buf_write_pointer;
  dsi_crm_stat_1_buf_valid_pointer_t                                 buf_valid_pointer;
} dsi_crm_stat_1_t;

typedef union {
  unsigned short a[sizeof(dsi_crm_stat_1_t)/sizeof(unsigned short)];
  dsi_crm_stat_1_t s;
} dsi_crm_stat_1_u_t;


#define ADDR_DSI_CRM_STAT_1_BUF_VALID_COUNT                          (0x0U)
#define A_DSI_CRM_STAT_1_BUF_VALID_COUNT(ba)                         ((ba) + ADDR_DSI_CRM_STAT_1_BUF_VALID_COUNT)
#define R_DSI_CRM_STAT_1_BUF_VALID_COUNT(ba)                         (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_1_BUF_VALID_COUNT(ba)))
#define RES_DSI_CRM_STAT_1_BUF_VALID_COUNT                           (0x0000U)
#define MSB_DSI_CRM_STAT_1_BUF_VALID_COUNT                           (11)
#define LSB_DSI_CRM_STAT_1_BUF_VALID_COUNT                           (0)
#define VBMASK_DSI_CRM_STAT_1_BUF_VALID_COUNT                        (0x0fffU)
#define ROMASK_DSI_CRM_STAT_1_BUF_VALID_COUNT                        (0x0fffU)
#define AADDR_DSI_CRM_STAT_1_BUF_VALID_COUNT                         (BASE_ADDR_DSI_CRM_STAT_1 + ADDR_DSI_CRM_STAT_1_BUF_VALID_COUNT)
#define REG_DSI_CRM_STAT_1_BUF_VALID_COUNT                           (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_1_BUF_VALID_COUNT))

#define ADDR_DSI_CRM_STAT_1_BUF_FREE                                 (0x2U)
#define A_DSI_CRM_STAT_1_BUF_FREE(ba)                                ((ba) + ADDR_DSI_CRM_STAT_1_BUF_FREE)
#define R_DSI_CRM_STAT_1_BUF_FREE(ba)                                (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_1_BUF_FREE(ba)))
#define RES_DSI_CRM_STAT_1_BUF_FREE                                  (0x0000U)
#define MSB_DSI_CRM_STAT_1_BUF_FREE                                  (15)
#define LSB_DSI_CRM_STAT_1_BUF_FREE                                  (0)
#define VBMASK_DSI_CRM_STAT_1_BUF_FREE                               (0xffffU)
#define ROMASK_DSI_CRM_STAT_1_BUF_FREE                               (0xffffU)
#define AADDR_DSI_CRM_STAT_1_BUF_FREE                                (BASE_ADDR_DSI_CRM_STAT_1 + ADDR_DSI_CRM_STAT_1_BUF_FREE)
#define REG_DSI_CRM_STAT_1_BUF_FREE                                  (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_1_BUF_FREE))

#define ADDR_DSI_CRM_STAT_1_BUF_READ_POINTER                         (0x8U)
#define A_DSI_CRM_STAT_1_BUF_READ_POINTER(ba)                        ((ba) + ADDR_DSI_CRM_STAT_1_BUF_READ_POINTER)
#define R_DSI_CRM_STAT_1_BUF_READ_POINTER(ba)                        (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_1_BUF_READ_POINTER(ba)))
#define RES_DSI_CRM_STAT_1_BUF_READ_POINTER                          (0x0000U)
#define MSB_DSI_CRM_STAT_1_BUF_READ_POINTER                          (15)
#define LSB_DSI_CRM_STAT_1_BUF_READ_POINTER                          (0)
#define VBMASK_DSI_CRM_STAT_1_BUF_READ_POINTER                       (0xffffU)
#define ROMASK_DSI_CRM_STAT_1_BUF_READ_POINTER                       (0xffffU)
#define AADDR_DSI_CRM_STAT_1_BUF_READ_POINTER                        (BASE_ADDR_DSI_CRM_STAT_1 + ADDR_DSI_CRM_STAT_1_BUF_READ_POINTER)
#define REG_DSI_CRM_STAT_1_BUF_READ_POINTER                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_1_BUF_READ_POINTER))

#define ADDR_DSI_CRM_STAT_1_BUF_WRITE_POINTER                        (0x9U)
#define A_DSI_CRM_STAT_1_BUF_WRITE_POINTER(ba)                       ((ba) + ADDR_DSI_CRM_STAT_1_BUF_WRITE_POINTER)
#define R_DSI_CRM_STAT_1_BUF_WRITE_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_1_BUF_WRITE_POINTER(ba)))
#define RES_DSI_CRM_STAT_1_BUF_WRITE_POINTER                         (0x0000U)
#define MSB_DSI_CRM_STAT_1_BUF_WRITE_POINTER                         (15)
#define LSB_DSI_CRM_STAT_1_BUF_WRITE_POINTER                         (0)
#define VBMASK_DSI_CRM_STAT_1_BUF_WRITE_POINTER                      (0xffffU)
#define ROMASK_DSI_CRM_STAT_1_BUF_WRITE_POINTER                      (0xffffU)
#define AADDR_DSI_CRM_STAT_1_BUF_WRITE_POINTER                       (BASE_ADDR_DSI_CRM_STAT_1 + ADDR_DSI_CRM_STAT_1_BUF_WRITE_POINTER)
#define REG_DSI_CRM_STAT_1_BUF_WRITE_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_1_BUF_WRITE_POINTER))

#define ADDR_DSI_CRM_STAT_1_BUF_VALID_POINTER                        (0xAU)
#define A_DSI_CRM_STAT_1_BUF_VALID_POINTER(ba)                       ((ba) + ADDR_DSI_CRM_STAT_1_BUF_VALID_POINTER)
#define R_DSI_CRM_STAT_1_BUF_VALID_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_CRM_STAT_1_BUF_VALID_POINTER(ba)))
#define RES_DSI_CRM_STAT_1_BUF_VALID_POINTER                         (0x0000U)
#define MSB_DSI_CRM_STAT_1_BUF_VALID_POINTER                         (15)
#define LSB_DSI_CRM_STAT_1_BUF_VALID_POINTER                         (0)
#define VBMASK_DSI_CRM_STAT_1_BUF_VALID_POINTER                      (0xffffU)
#define ROMASK_DSI_CRM_STAT_1_BUF_VALID_POINTER                      (0xffffU)
#define AADDR_DSI_CRM_STAT_1_BUF_VALID_POINTER                       (BASE_ADDR_DSI_CRM_STAT_1 + ADDR_DSI_CRM_STAT_1_BUF_VALID_POINTER)
#define REG_DSI_CRM_STAT_1_BUF_VALID_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_CRM_STAT_1_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_PDCM_STAT_0 
#define BASE_ADDR_DSI_PDCM_STAT_0 0x0150U
#define SIZE_DSI_PDCM_STAT_0 0x0010U
#endif

// Register bit field definitions
	 
/* DSI_PDCM_STAT_0_BUF_VALID_COUNT */

#define MSK_DSI_PDCM_STAT_0_BUF_VALID_COUNT_VALID_COUNT              (0xfff)
#define SFT_DSI_PDCM_STAT_0_BUF_VALID_COUNT_VALID_COUNT              (0)
#define LSB_DSI_PDCM_STAT_0_BUF_VALID_COUNT_VALID_COUNT              (0)
#define MSB_DSI_PDCM_STAT_0_BUF_VALID_COUNT_VALID_COUNT              (11)

typedef struct {
  unsigned short valid_count : 12;
} dsi_pdcm_stat_0_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_0_buf_valid_count_bf bf;
} dsi_pdcm_stat_0_buf_valid_count_t;


/* DSI_PDCM_STAT_0_BUF_FREE */

#define MSK_DSI_PDCM_STAT_0_BUF_FREE_FREE                            (0xffff)
#define SFT_DSI_PDCM_STAT_0_BUF_FREE_FREE                            (0)
#define LSB_DSI_PDCM_STAT_0_BUF_FREE_FREE                            (0)
#define MSB_DSI_PDCM_STAT_0_BUF_FREE_FREE                            (15)

typedef struct {
  unsigned short free : 16;
} dsi_pdcm_stat_0_buf_free_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_0_buf_free_bf bf;
} dsi_pdcm_stat_0_buf_free_t;


/* DSI_PDCM_STAT_0_BUF_READ_POINTER */

#define MSK_DSI_PDCM_STAT_0_BUF_READ_POINTER_READ_POINTER            (0xffff)
#define SFT_DSI_PDCM_STAT_0_BUF_READ_POINTER_READ_POINTER            (0)
#define LSB_DSI_PDCM_STAT_0_BUF_READ_POINTER_READ_POINTER            (0)
#define MSB_DSI_PDCM_STAT_0_BUF_READ_POINTER_READ_POINTER            (15)

typedef struct {
  unsigned short read_pointer : 16;
} dsi_pdcm_stat_0_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_0_buf_read_pointer_bf bf;
} dsi_pdcm_stat_0_buf_read_pointer_t;


/* DSI_PDCM_STAT_0_BUF_WRITE_POINTER */

#define MSK_DSI_PDCM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER          (0xffff)
#define SFT_DSI_PDCM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER          (0)
#define LSB_DSI_PDCM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER          (0)
#define MSB_DSI_PDCM_STAT_0_BUF_WRITE_POINTER_WRITE_POINTER          (15)

typedef struct {
  unsigned short write_pointer : 16;
} dsi_pdcm_stat_0_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_0_buf_write_pointer_bf bf;
} dsi_pdcm_stat_0_buf_write_pointer_t;


/* DSI_PDCM_STAT_0_BUF_VALID_POINTER */

#define MSK_DSI_PDCM_STAT_0_BUF_VALID_POINTER_VALID_POINTER          (0xffff)
#define SFT_DSI_PDCM_STAT_0_BUF_VALID_POINTER_VALID_POINTER          (0)
#define LSB_DSI_PDCM_STAT_0_BUF_VALID_POINTER_VALID_POINTER          (0)
#define MSB_DSI_PDCM_STAT_0_BUF_VALID_POINTER_VALID_POINTER          (15)

typedef struct {
  unsigned short valid_pointer : 16;
} dsi_pdcm_stat_0_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_0_buf_valid_pointer_bf bf;
} dsi_pdcm_stat_0_buf_valid_pointer_t;



typedef struct {
  dsi_pdcm_stat_0_buf_valid_count_t                                  buf_valid_count;
  dsi_pdcm_stat_0_buf_free_t                                         buf_free;
  dsi_pdcm_stat_0_buf_read_pointer_t                                 buf_read_pointer;
  dsi_pdcm_stat_0_buf_write_pointer_t                                buf_write_pointer;
  dsi_pdcm_stat_0_buf_valid_pointer_t                                buf_valid_pointer;
} dsi_pdcm_stat_0_t;

typedef union {
  unsigned short a[sizeof(dsi_pdcm_stat_0_t)/sizeof(unsigned short)];
  dsi_pdcm_stat_0_t s;
} dsi_pdcm_stat_0_u_t;


#define ADDR_DSI_PDCM_STAT_0_BUF_VALID_COUNT                         (0x0U)
#define A_DSI_PDCM_STAT_0_BUF_VALID_COUNT(ba)                        ((ba) + ADDR_DSI_PDCM_STAT_0_BUF_VALID_COUNT)
#define R_DSI_PDCM_STAT_0_BUF_VALID_COUNT(ba)                        (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_0_BUF_VALID_COUNT(ba)))
#define RES_DSI_PDCM_STAT_0_BUF_VALID_COUNT                          (0x0000U)
#define MSB_DSI_PDCM_STAT_0_BUF_VALID_COUNT                          (11)
#define LSB_DSI_PDCM_STAT_0_BUF_VALID_COUNT                          (0)
#define VBMASK_DSI_PDCM_STAT_0_BUF_VALID_COUNT                       (0x0fffU)
#define ROMASK_DSI_PDCM_STAT_0_BUF_VALID_COUNT                       (0x0fffU)
#define AADDR_DSI_PDCM_STAT_0_BUF_VALID_COUNT                        (BASE_ADDR_DSI_PDCM_STAT_0 + ADDR_DSI_PDCM_STAT_0_BUF_VALID_COUNT)
#define REG_DSI_PDCM_STAT_0_BUF_VALID_COUNT                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_0_BUF_VALID_COUNT))

#define ADDR_DSI_PDCM_STAT_0_BUF_FREE                                (0x2U)
#define A_DSI_PDCM_STAT_0_BUF_FREE(ba)                               ((ba) + ADDR_DSI_PDCM_STAT_0_BUF_FREE)
#define R_DSI_PDCM_STAT_0_BUF_FREE(ba)                               (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_0_BUF_FREE(ba)))
#define RES_DSI_PDCM_STAT_0_BUF_FREE                                 (0x0000U)
#define MSB_DSI_PDCM_STAT_0_BUF_FREE                                 (15)
#define LSB_DSI_PDCM_STAT_0_BUF_FREE                                 (0)
#define VBMASK_DSI_PDCM_STAT_0_BUF_FREE                              (0xffffU)
#define ROMASK_DSI_PDCM_STAT_0_BUF_FREE                              (0xffffU)
#define AADDR_DSI_PDCM_STAT_0_BUF_FREE                               (BASE_ADDR_DSI_PDCM_STAT_0 + ADDR_DSI_PDCM_STAT_0_BUF_FREE)
#define REG_DSI_PDCM_STAT_0_BUF_FREE                                 (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_0_BUF_FREE))

#define ADDR_DSI_PDCM_STAT_0_BUF_READ_POINTER                        (0x8U)
#define A_DSI_PDCM_STAT_0_BUF_READ_POINTER(ba)                       ((ba) + ADDR_DSI_PDCM_STAT_0_BUF_READ_POINTER)
#define R_DSI_PDCM_STAT_0_BUF_READ_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_0_BUF_READ_POINTER(ba)))
#define RES_DSI_PDCM_STAT_0_BUF_READ_POINTER                         (0x0000U)
#define MSB_DSI_PDCM_STAT_0_BUF_READ_POINTER                         (15)
#define LSB_DSI_PDCM_STAT_0_BUF_READ_POINTER                         (0)
#define VBMASK_DSI_PDCM_STAT_0_BUF_READ_POINTER                      (0xffffU)
#define ROMASK_DSI_PDCM_STAT_0_BUF_READ_POINTER                      (0xffffU)
#define AADDR_DSI_PDCM_STAT_0_BUF_READ_POINTER                       (BASE_ADDR_DSI_PDCM_STAT_0 + ADDR_DSI_PDCM_STAT_0_BUF_READ_POINTER)
#define REG_DSI_PDCM_STAT_0_BUF_READ_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_0_BUF_READ_POINTER))

#define ADDR_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                       (0x9U)
#define A_DSI_PDCM_STAT_0_BUF_WRITE_POINTER(ba)                      ((ba) + ADDR_DSI_PDCM_STAT_0_BUF_WRITE_POINTER)
#define R_DSI_PDCM_STAT_0_BUF_WRITE_POINTER(ba)                      (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_0_BUF_WRITE_POINTER(ba)))
#define RES_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                        (0x0000U)
#define MSB_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                        (15)
#define LSB_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                        (0)
#define VBMASK_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                     (0xffffU)
#define ROMASK_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                     (0xffffU)
#define AADDR_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                      (BASE_ADDR_DSI_PDCM_STAT_0 + ADDR_DSI_PDCM_STAT_0_BUF_WRITE_POINTER)
#define REG_DSI_PDCM_STAT_0_BUF_WRITE_POINTER                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_0_BUF_WRITE_POINTER))

#define ADDR_DSI_PDCM_STAT_0_BUF_VALID_POINTER                       (0xAU)
#define A_DSI_PDCM_STAT_0_BUF_VALID_POINTER(ba)                      ((ba) + ADDR_DSI_PDCM_STAT_0_BUF_VALID_POINTER)
#define R_DSI_PDCM_STAT_0_BUF_VALID_POINTER(ba)                      (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_0_BUF_VALID_POINTER(ba)))
#define RES_DSI_PDCM_STAT_0_BUF_VALID_POINTER                        (0x0000U)
#define MSB_DSI_PDCM_STAT_0_BUF_VALID_POINTER                        (15)
#define LSB_DSI_PDCM_STAT_0_BUF_VALID_POINTER                        (0)
#define VBMASK_DSI_PDCM_STAT_0_BUF_VALID_POINTER                     (0xffffU)
#define ROMASK_DSI_PDCM_STAT_0_BUF_VALID_POINTER                     (0xffffU)
#define AADDR_DSI_PDCM_STAT_0_BUF_VALID_POINTER                      (BASE_ADDR_DSI_PDCM_STAT_0 + ADDR_DSI_PDCM_STAT_0_BUF_VALID_POINTER)
#define REG_DSI_PDCM_STAT_0_BUF_VALID_POINTER                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_0_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_DSI_PDCM_STAT_1 
#define BASE_ADDR_DSI_PDCM_STAT_1 0x0160U
#define SIZE_DSI_PDCM_STAT_1 0x0010U
#endif

// Register bit field definitions
	 
/* DSI_PDCM_STAT_1_BUF_VALID_COUNT */

#define MSK_DSI_PDCM_STAT_1_BUF_VALID_COUNT_VALID_COUNT              (0xfff)
#define SFT_DSI_PDCM_STAT_1_BUF_VALID_COUNT_VALID_COUNT              (0)
#define LSB_DSI_PDCM_STAT_1_BUF_VALID_COUNT_VALID_COUNT              (0)
#define MSB_DSI_PDCM_STAT_1_BUF_VALID_COUNT_VALID_COUNT              (11)

typedef struct {
  unsigned short valid_count : 12;
} dsi_pdcm_stat_1_buf_valid_count_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_1_buf_valid_count_bf bf;
} dsi_pdcm_stat_1_buf_valid_count_t;


/* DSI_PDCM_STAT_1_BUF_FREE */

#define MSK_DSI_PDCM_STAT_1_BUF_FREE_FREE                            (0xffff)
#define SFT_DSI_PDCM_STAT_1_BUF_FREE_FREE                            (0)
#define LSB_DSI_PDCM_STAT_1_BUF_FREE_FREE                            (0)
#define MSB_DSI_PDCM_STAT_1_BUF_FREE_FREE                            (15)

typedef struct {
  unsigned short free : 16;
} dsi_pdcm_stat_1_buf_free_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_1_buf_free_bf bf;
} dsi_pdcm_stat_1_buf_free_t;


/* DSI_PDCM_STAT_1_BUF_READ_POINTER */

#define MSK_DSI_PDCM_STAT_1_BUF_READ_POINTER_READ_POINTER            (0xffff)
#define SFT_DSI_PDCM_STAT_1_BUF_READ_POINTER_READ_POINTER            (0)
#define LSB_DSI_PDCM_STAT_1_BUF_READ_POINTER_READ_POINTER            (0)
#define MSB_DSI_PDCM_STAT_1_BUF_READ_POINTER_READ_POINTER            (15)

typedef struct {
  unsigned short read_pointer : 16;
} dsi_pdcm_stat_1_buf_read_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_1_buf_read_pointer_bf bf;
} dsi_pdcm_stat_1_buf_read_pointer_t;


/* DSI_PDCM_STAT_1_BUF_WRITE_POINTER */

#define MSK_DSI_PDCM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER          (0xffff)
#define SFT_DSI_PDCM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER          (0)
#define LSB_DSI_PDCM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER          (0)
#define MSB_DSI_PDCM_STAT_1_BUF_WRITE_POINTER_WRITE_POINTER          (15)

typedef struct {
  unsigned short write_pointer : 16;
} dsi_pdcm_stat_1_buf_write_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_1_buf_write_pointer_bf bf;
} dsi_pdcm_stat_1_buf_write_pointer_t;


/* DSI_PDCM_STAT_1_BUF_VALID_POINTER */

#define MSK_DSI_PDCM_STAT_1_BUF_VALID_POINTER_VALID_POINTER          (0xffff)
#define SFT_DSI_PDCM_STAT_1_BUF_VALID_POINTER_VALID_POINTER          (0)
#define LSB_DSI_PDCM_STAT_1_BUF_VALID_POINTER_VALID_POINTER          (0)
#define MSB_DSI_PDCM_STAT_1_BUF_VALID_POINTER_VALID_POINTER          (15)

typedef struct {
  unsigned short valid_pointer : 16;
} dsi_pdcm_stat_1_buf_valid_pointer_bf;
		
typedef union {
  unsigned short val;
  dsi_pdcm_stat_1_buf_valid_pointer_bf bf;
} dsi_pdcm_stat_1_buf_valid_pointer_t;



typedef struct {
  dsi_pdcm_stat_1_buf_valid_count_t                                  buf_valid_count;
  dsi_pdcm_stat_1_buf_free_t                                         buf_free;
  dsi_pdcm_stat_1_buf_read_pointer_t                                 buf_read_pointer;
  dsi_pdcm_stat_1_buf_write_pointer_t                                buf_write_pointer;
  dsi_pdcm_stat_1_buf_valid_pointer_t                                buf_valid_pointer;
} dsi_pdcm_stat_1_t;

typedef union {
  unsigned short a[sizeof(dsi_pdcm_stat_1_t)/sizeof(unsigned short)];
  dsi_pdcm_stat_1_t s;
} dsi_pdcm_stat_1_u_t;


#define ADDR_DSI_PDCM_STAT_1_BUF_VALID_COUNT                         (0x0U)
#define A_DSI_PDCM_STAT_1_BUF_VALID_COUNT(ba)                        ((ba) + ADDR_DSI_PDCM_STAT_1_BUF_VALID_COUNT)
#define R_DSI_PDCM_STAT_1_BUF_VALID_COUNT(ba)                        (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_1_BUF_VALID_COUNT(ba)))
#define RES_DSI_PDCM_STAT_1_BUF_VALID_COUNT                          (0x0000U)
#define MSB_DSI_PDCM_STAT_1_BUF_VALID_COUNT                          (11)
#define LSB_DSI_PDCM_STAT_1_BUF_VALID_COUNT                          (0)
#define VBMASK_DSI_PDCM_STAT_1_BUF_VALID_COUNT                       (0x0fffU)
#define ROMASK_DSI_PDCM_STAT_1_BUF_VALID_COUNT                       (0x0fffU)
#define AADDR_DSI_PDCM_STAT_1_BUF_VALID_COUNT                        (BASE_ADDR_DSI_PDCM_STAT_1 + ADDR_DSI_PDCM_STAT_1_BUF_VALID_COUNT)
#define REG_DSI_PDCM_STAT_1_BUF_VALID_COUNT                          (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_1_BUF_VALID_COUNT))

#define ADDR_DSI_PDCM_STAT_1_BUF_FREE                                (0x2U)
#define A_DSI_PDCM_STAT_1_BUF_FREE(ba)                               ((ba) + ADDR_DSI_PDCM_STAT_1_BUF_FREE)
#define R_DSI_PDCM_STAT_1_BUF_FREE(ba)                               (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_1_BUF_FREE(ba)))
#define RES_DSI_PDCM_STAT_1_BUF_FREE                                 (0x0000U)
#define MSB_DSI_PDCM_STAT_1_BUF_FREE                                 (15)
#define LSB_DSI_PDCM_STAT_1_BUF_FREE                                 (0)
#define VBMASK_DSI_PDCM_STAT_1_BUF_FREE                              (0xffffU)
#define ROMASK_DSI_PDCM_STAT_1_BUF_FREE                              (0xffffU)
#define AADDR_DSI_PDCM_STAT_1_BUF_FREE                               (BASE_ADDR_DSI_PDCM_STAT_1 + ADDR_DSI_PDCM_STAT_1_BUF_FREE)
#define REG_DSI_PDCM_STAT_1_BUF_FREE                                 (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_1_BUF_FREE))

#define ADDR_DSI_PDCM_STAT_1_BUF_READ_POINTER                        (0x8U)
#define A_DSI_PDCM_STAT_1_BUF_READ_POINTER(ba)                       ((ba) + ADDR_DSI_PDCM_STAT_1_BUF_READ_POINTER)
#define R_DSI_PDCM_STAT_1_BUF_READ_POINTER(ba)                       (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_1_BUF_READ_POINTER(ba)))
#define RES_DSI_PDCM_STAT_1_BUF_READ_POINTER                         (0x0000U)
#define MSB_DSI_PDCM_STAT_1_BUF_READ_POINTER                         (15)
#define LSB_DSI_PDCM_STAT_1_BUF_READ_POINTER                         (0)
#define VBMASK_DSI_PDCM_STAT_1_BUF_READ_POINTER                      (0xffffU)
#define ROMASK_DSI_PDCM_STAT_1_BUF_READ_POINTER                      (0xffffU)
#define AADDR_DSI_PDCM_STAT_1_BUF_READ_POINTER                       (BASE_ADDR_DSI_PDCM_STAT_1 + ADDR_DSI_PDCM_STAT_1_BUF_READ_POINTER)
#define REG_DSI_PDCM_STAT_1_BUF_READ_POINTER                         (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_1_BUF_READ_POINTER))

#define ADDR_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                       (0x9U)
#define A_DSI_PDCM_STAT_1_BUF_WRITE_POINTER(ba)                      ((ba) + ADDR_DSI_PDCM_STAT_1_BUF_WRITE_POINTER)
#define R_DSI_PDCM_STAT_1_BUF_WRITE_POINTER(ba)                      (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_1_BUF_WRITE_POINTER(ba)))
#define RES_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                        (0x0000U)
#define MSB_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                        (15)
#define LSB_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                        (0)
#define VBMASK_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                     (0xffffU)
#define ROMASK_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                     (0xffffU)
#define AADDR_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                      (BASE_ADDR_DSI_PDCM_STAT_1 + ADDR_DSI_PDCM_STAT_1_BUF_WRITE_POINTER)
#define REG_DSI_PDCM_STAT_1_BUF_WRITE_POINTER                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_1_BUF_WRITE_POINTER))

#define ADDR_DSI_PDCM_STAT_1_BUF_VALID_POINTER                       (0xAU)
#define A_DSI_PDCM_STAT_1_BUF_VALID_POINTER(ba)                      ((ba) + ADDR_DSI_PDCM_STAT_1_BUF_VALID_POINTER)
#define R_DSI_PDCM_STAT_1_BUF_VALID_POINTER(ba)                      (*(volatile unsigned short *)((unsigned int)A_DSI_PDCM_STAT_1_BUF_VALID_POINTER(ba)))
#define RES_DSI_PDCM_STAT_1_BUF_VALID_POINTER                        (0x0000U)
#define MSB_DSI_PDCM_STAT_1_BUF_VALID_POINTER                        (15)
#define LSB_DSI_PDCM_STAT_1_BUF_VALID_POINTER                        (0)
#define VBMASK_DSI_PDCM_STAT_1_BUF_VALID_POINTER                     (0xffffU)
#define ROMASK_DSI_PDCM_STAT_1_BUF_VALID_POINTER                     (0xffffU)
#define AADDR_DSI_PDCM_STAT_1_BUF_VALID_POINTER                      (BASE_ADDR_DSI_PDCM_STAT_1 + ADDR_DSI_PDCM_STAT_1_BUF_VALID_POINTER)
#define REG_DSI_PDCM_STAT_1_BUF_VALID_POINTER                        (*(volatile unsigned short *)((unsigned int)AADDR_DSI_PDCM_STAT_1_BUF_VALID_POINTER))

 


// Instance base addresses

#ifndef BASE_ADDR_SPI_CMD_BUF 
#define BASE_ADDR_SPI_CMD_BUF 0x0400U
#define SIZE_SPI_CMD_BUF 0x0100U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CMD_BUF_0 
#define BASE_ADDR_DSI_CMD_BUF_0 0x0500U
#define SIZE_DSI_CMD_BUF_0 0x0080U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CMD_BUF_1 
#define BASE_ADDR_DSI_CMD_BUF_1 0x0580U
#define SIZE_DSI_CMD_BUF_1 0x0080U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CRM_BUF_0 
#define BASE_ADDR_DSI_CRM_BUF_0 0x0600U
#define SIZE_DSI_CRM_BUF_0 0x0080U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_CRM_BUF_1 
#define BASE_ADDR_DSI_CRM_BUF_1 0x0680U
#define SIZE_DSI_CRM_BUF_1 0x0080U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_TDMA_0 
#define BASE_ADDR_DSI_TDMA_0 0x0700U
#define SIZE_DSI_TDMA_0 0x0030U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_TDMA_1 
#define BASE_ADDR_DSI_TDMA_1 0x0730U
#define SIZE_DSI_TDMA_1 0x0030U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_PDCM_BUF_0 
#define BASE_ADDR_DSI_PDCM_BUF_0 0x0800U
#define SIZE_DSI_PDCM_BUF_0 0x0400U
#endif

// Register bit field definitions
	 



 


// Instance base addresses

#ifndef BASE_ADDR_DSI_PDCM_BUF_1 
#define BASE_ADDR_DSI_PDCM_BUF_1 0x0C00U
#define SIZE_DSI_PDCM_BUF_1 0x0400U
#endif

// Register bit field definitions
	 



 

#endif