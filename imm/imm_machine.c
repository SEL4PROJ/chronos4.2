
/*******************************************************************************
 *
 * Chronos: A Timing Analyzer for Embedded Software
 * =============================================================================
 * http://www.comp.nus.edu.sg/~rpembed/chronos/
 *
 * Copyright (C) 2005 Xianfeng Li
 *
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 2, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 *
 * $Id: ss_machine.c,v 1.2 2006/06/24 08:55:05 lixianfe Exp $
 *
 *
 ******************************************************************************/


#include "../common.h"
#include "imm_machine.h"

extern int	pipe_ibuf_size, pipe_iwin_size;



/* number of instances for each function unit class */
int
pfu_quant[] = {
    1,	    /* P_FUClass_NA = 0, */
    1,	    /* P_IntALU,	*/
    1,	    /* P_Int_Mult_Div, */
    1,	    /* P_Mem_Port,	*/
    1,	    /* P_FP_Adder,	*/
    1,	    /* P_FP_Mult_Div,	*/
    1,	    /* P_CoProc,	*/
    1,	    /* P_Sync,		*/
    1,	    /* P_Branch,	*/
    1	    /* NUM_PFU_CLASSES	*/
};


enum ss_pfu_class fu2pfu[] = {
  P_FUClass_NA,		// FUClass_NA = 0,	
  P_IntALU,		// IntALU,		
  P_Int_Mult_Div,	// IntMULT,		
  P_Int_Mult_Div,	// IntDIV,		
  P_FP_Adder,		// FloatADD,		
  P_FP_Adder,		// FloatCMP,		
  P_FP_Adder,		// FloatCVT,		
  P_FP_Mult_Div,	// FloatMULT,		
  P_FP_Mult_Div,	// FloatDIV,		
  P_FP_Mult_Div,	// FloatSQRT,		
  P_Mem_Port,		// RdPort,		
  P_Mem_Port, 		// WrPort,		
  P_CoProc,		// CoProc,		
  P_Sync,		// Sync,		
  P_Branch,		// Branch,		
};

static int UNUSED
inst_win_size_ss(void)
{
    return pipe_ibuf_size + pipe_iwin_size;
}

