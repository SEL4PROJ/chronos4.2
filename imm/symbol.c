/* symbol.c - program symbol and line data routines */

/* SimpleScalar(TM) Tool Suite
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 * All Rights Reserved. 
 * 
 * THIS IS A LEGAL DOCUMENT, BY USING SIMPLESCALAR,
 * YOU ARE AGREEING TO THESE TERMS AND CONDITIONS.
 * 
 * No portion of this work may be used by any commercial entity, or for any
 * commercial purpose, without the prior, written permission of SimpleScalar,
 * LLC (info@simplescalar.com). Nonprofit and noncommercial use is permitted
 * as described below.
 * 
 * 1. SimpleScalar is provided AS IS, with no warranty of any kind, express
 * or implied. The user of the program accepts full responsibility for the
 * application of the program and the use of any results.
 * 
 * 2. Nonprofit and noncommercial use is encouraged. SimpleScalar may be
 * downloaded, compiled, executed, copied, and modified solely for nonprofit,
 * educational, noncommercial research, and noncommercial scholarship
 * purposes provided that this notice in its entirety accompanies all copies.
 * Copies of the modified software can be delivered to persons who use it
 * solely for nonprofit, educational, noncommercial research, and
 * noncommercial scholarship purposes provided that this notice in its
 * entirety accompanies all copies.
 * 
 * 3. ALL COMMERCIAL USE, AND ALL USE BY FOR PROFIT ENTITIES, IS EXPRESSLY
 * PROHIBITED WITHOUT A LICENSE FROM SIMPLESCALAR, LLC (info@simplescalar.com).
 * 
 * 4. No nonprofit user may place any restrictions on the use of this software,
 * including as modified by the user, by any other authorized user.
 * 
 * 5. Noncommercial and nonprofit users may distribute copies of SimpleScalar
 * in compiled or executable form as set forth in Section 2, provided that
 * either: (A) it is accompanied by the corresponding machine-readable source
 * code, or (B) it is accompanied by a written offer, with no time limit, to
 * give anyone a machine-readable copy of the corresponding source code in
 * return for reimbursement of the cost of distribution. This written offer
 * must permit verbatim duplication by anyone, or (C) it is distributed by
 * someone who received only the executable form, and is accompanied by a
 * copy of the written offer of source code.
 * 
 * 6. SimpleScalar was developed by Todd M. Austin, Ph.D. The tool suite is
 * currently maintained by SimpleScalar LLC (info@simplescalar.com). US Mail:
 * 2395 Timbercrest Court, Ann Arbor, MI 48105.
 * 
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 */


#include <stdio.h>
#include <stdlib.h>

#include "../common.h"
#include "host.h"
//#include "misc.h"
#ifdef BFD_LOADER
#include <bfd.h>
#else /* !BFD_LOADER */
#include "ecoff.h"
#endif /* BFD_LOADER */
//#include "loader.h"
#include "symbol.h"

#include "../mem_value.h"

/* #define PRINT_SYMS */

/* symbol database in no particular order */
struct sym_sym_t *sym_db = NULL;

/* all symbol sorted by address */
int sym_nsyms = 0;
struct sym_sym_t **sym_syms = NULL;

/* all symbols sorted by name */
struct sym_sym_t **sym_syms_by_name = NULL;

/* text symbols sorted by address */
int sym_ntextsyms = 0;
struct sym_sym_t **sym_textsyms = NULL;

/* text symbols sorted by name */
struct sym_sym_t **sym_textsyms_by_name = NULL;

/* data symbols sorted by address */
int sym_ndatasyms = 0;
struct sym_sym_t **sym_datasyms = NULL;

/* data symbols sorted by name */
struct sym_sym_t **sym_datasyms_by_name = NULL;

/* symbols loaded? */
static int syms_loaded = FALSE;

extern int ld_text_base, ld_text_size;

unsigned preemption_addr;

#ifdef PRINT_SYMS
/* convert BFD symbols flags to a printable string */
static char *			/* symbol flags string */
flags2str(unsigned int flags)	/* bfd symbol flags */
{
  static char buf[256];
  char *p;

  if (!flags)
    return "";

  p = buf;
  *p = '\0';

  if (flags & BSF_LOCAL)
    {
      *p++ = 'L';
      *p++ = '|';
    }
  if (flags & BSF_GLOBAL)
    {
      *p++ = 'G';
      *p++ = '|';
    }
  if (flags & BSF_DEBUGGING)
    {
      *p++ = 'D';
      *p++ = '|';
    }
  if (flags & BSF_FUNCTION)
    {
      *p++ = 'F';
      *p++ = '|';
    }
  if (flags & BSF_KEEP)
    {
      *p++ = 'K';
      *p++ = '|';
    }
  if (flags & BSF_KEEP_G)
    {
      *p++ = 'k'; *p++ = '|';
    }
  if (flags & BSF_WEAK)
    {
      *p++ = 'W';
      *p++ = '|';
    }
  if (flags & BSF_SECTION_SYM)
    {
      *p++ = 'S'; *p++ = '|';
    }
  if (flags & BSF_OLD_COMMON)
    {
      *p++ = 'O';
      *p++ = '|';
    }
  if (flags & BSF_NOT_AT_END)
    {
      *p++ = 'N';
      *p++ = '|';
    }
  if (flags & BSF_CONSTRUCTOR)
    {
      *p++ = 'C';
      *p++ = '|';
    }
  if (flags & BSF_WARNING)
    {
      *p++ = 'w';
      *p++ = '|';
    }
  if (flags & BSF_INDIRECT)
    {
      *p++ = 'I';
      *p++ = '|';
    }
  if (flags & BSF_FILE)
    {
      *p++ = 'f';
      *p++ = '|';
    }

  if (p == buf)
    panic("no flags detected");

  *--p = '\0';
  return buf;
}
#endif /* PRINT_SYMS */

/* qsort helper function */
static int
acmp(struct sym_sym_t **sym1, struct sym_sym_t **sym2)
{
  return (int)((*sym1)->addr - (*sym2)->addr);
}

/* qsort helper function */
static int
ncmp(struct sym_sym_t **sym1, struct sym_sym_t **sym2)
{
  return strcmp((*sym1)->name, (*sym2)->name);
}

#define RELEVANT_SCOPE(SYM)						\
(/* global symbol */							\
 ((SYM)->flags & BSF_GLOBAL)						\
 || (/* local symbol */							\
     (((SYM)->flags & (BSF_LOCAL|BSF_DEBUGGING)) == BSF_LOCAL)		\
     && (SYM)->name[0] != '$')						\
 || (/* compiler local */						\
     load_locals							\
     && ((/* basic block idents */					\
	  ((SYM)->flags&(BSF_LOCAL|BSF_DEBUGGING))==(BSF_LOCAL|BSF_DEBUGGING)\
	  && (SYM)->name[0] == '$')					\
	 || (/* local constant idents */				\
	     ((SYM)->flags & (BSF_LOCAL|BSF_DEBUGGING)) == (BSF_LOCAL)	\
	     && (SYM)->name[0] == '$'))))
     

/* load symbols out of FNAME */
void
sym_loadsyms(char *fname)
{
  int i, debug_cnt;
  FILE *fobj;
  char s[4096];
  int num_symbols;

  if (syms_loaded)
    {
      /* symbols are already loaded */
      /* FIXME: can't handle symbols from multiple files */
      return;
    }

  fobj = fopen(fname, "r");
  if (!fobj)
    fatal("cannot open imm file `%s'", fname);

  /* Do one scan to find all symbol lines. */
  num_symbols = 0;
  while (fgets(s, sizeof(s), fobj) != NULL) {
    if (s[0] == 's')
      num_symbols++;
  }

  /* allocate symbol space */
  sym_db = (struct sym_sym_t *)calloc(num_symbols, sizeof(struct sym_sym_t));
  if (!sym_db)
    fatal("out of virtual memory");

  fseek(fobj, 0, SEEK_SET);

  sym_nsyms = 0; sym_ndatasyms = 0; sym_ntextsyms = 0;

  /* convert symbols to internal format */
  while (fgets(s, sizeof(s), fobj) != NULL) {
    int ret;
    char sym_name[4096];
    unsigned long address;
    unsigned long size;
    char flags[32];
    int is_text;
    if (s[0] != 's')
      continue;

    ret = sscanf(s, "%*s %s %li %li %s", sym_name, &address, &size, flags);
    if (ret != 4) {
      if (ret == 3)
        flags[0] = '\0';
      else
        fatal("Bad symbol line: %s", s);
    }

    /* get the preemption point function address */
    if (strcmp(sym_name, "preemptionPoint") == 0) {
        //preemption_addr = address;
    }

    if (flags[0] == 't')
      is_text = 1;
    else if (flags[0] == 'd')
      is_text = 0;
    else
      continue;

    sym_db[sym_nsyms].name = mystrdup(sym_name);
    sym_db[sym_nsyms].initialized = /* FIXME: ??? */TRUE;
    sym_db[sym_nsyms].pub = /* FIXME: ??? */TRUE;
    sym_db[sym_nsyms].local = /* FIXME: ??? */FALSE;
    sym_db[sym_nsyms].addr = address;

    if (is_text) {
      sym_db[sym_nsyms].seg = ss_text;
      sym_ntextsyms++;
    } 
    else {
      global_memory_add(sym_db[sym_nsyms].addr, 0);
      sym_db[sym_nsyms].seg = ss_data;
      sym_ndatasyms++;
    }
    sym_nsyms++;
  }

  /* done with the executable, close it */
  if (fclose(fobj))
    fatal("could not close executable `%s'", fname);

  /*
   * generate various sortings
   */

  /* all symbols sorted by address and name */
  sym_syms =
    (struct sym_sym_t **)calloc(sym_nsyms, sizeof(struct sym_sym_t *));
  if (!sym_syms)
    fatal("out of virtual memory");

  sym_syms_by_name =
    (struct sym_sym_t **)calloc(sym_nsyms, sizeof(struct sym_sym_t *));
  if (!sym_syms_by_name)
    fatal("out of virtual memory");

  for (debug_cnt=0, i=0; i<sym_nsyms; i++)
    {
      sym_syms[debug_cnt] = &sym_db[i];
      sym_syms_by_name[debug_cnt] = &sym_db[i];
      debug_cnt++;
    }
  /* sanity check */
  if (debug_cnt != sym_nsyms)
    panic("could not locate all symbols");

  /* sort by address */
  qsort(sym_syms, sym_nsyms, sizeof(struct sym_sym_t *), (void *)acmp);

  /* sort by name */
  qsort(sym_syms_by_name, sym_nsyms, sizeof(struct sym_sym_t *), (void *)ncmp);

  /* text segment sorted by address and name */
  sym_textsyms =
    (struct sym_sym_t **)calloc(sym_ntextsyms, sizeof(struct sym_sym_t *));
  if (!sym_textsyms)
    fatal("out of virtual memory");

  sym_textsyms_by_name =
    (struct sym_sym_t **)calloc(sym_ntextsyms, sizeof(struct sym_sym_t *));
  if (!sym_textsyms_by_name)
    fatal("out of virtual memory");

  for (debug_cnt=0, i=0; i<sym_nsyms; i++)
    {
      if (sym_db[i].seg == ss_text)
	{
	  sym_textsyms[debug_cnt] = &sym_db[i];
	  sym_textsyms_by_name[debug_cnt] = &sym_db[i];
	  debug_cnt++;
	}
    }
  /* sanity check */
  if (debug_cnt != sym_ntextsyms)
    panic("could not locate all text symbols");

  /* sort by address */
  qsort(sym_textsyms, sym_ntextsyms, sizeof(struct sym_sym_t *), (void *)acmp);

  /* sort by name */
  qsort(sym_textsyms_by_name, sym_ntextsyms,
	sizeof(struct sym_sym_t *), (void *)ncmp);

  /* data segment sorted by address and name */
  sym_datasyms =
    (struct sym_sym_t **)calloc(sym_ndatasyms, sizeof(struct sym_sym_t *));
  if (!sym_datasyms)
    fatal("out of virtual memory");

  sym_datasyms_by_name =
    (struct sym_sym_t **)calloc(sym_ndatasyms, sizeof(struct sym_sym_t *));
  if (!sym_datasyms_by_name)
    fatal("out of virtual memory");

  for (debug_cnt=0, i=0; i<sym_nsyms; i++)
    {
      if (sym_db[i].seg == ss_data)
	{
	  sym_datasyms[debug_cnt] = &sym_db[i];
	  sym_datasyms_by_name[debug_cnt] = &sym_db[i];
	  debug_cnt++;
	}
    }
  /* sanity check */
  if (debug_cnt != sym_ndatasyms)
    panic("could not locate all data symbols");
      
  /* sort by address */
  qsort(sym_datasyms, sym_ndatasyms, sizeof(struct sym_sym_t *), (void *)acmp);

  /* sort by name */
  qsort(sym_datasyms_by_name, sym_ndatasyms,
	sizeof(struct sym_sym_t *), (void *)ncmp);

  /* compute symbol sizes */
  for (i=0; i<sym_ntextsyms; i++)
    {
      sym_textsyms[i]->size =
	(i != (sym_ntextsyms - 1)
	 ? (sym_textsyms[i+1]->addr - sym_textsyms[i]->addr)
	 : ((ld_text_base + ld_text_size) - sym_textsyms[i]->addr));
    }
// commented by LXF
#if 0
  for (i=0; i<sym_ndatasyms; i++)
    {
      sym_datasyms[i]->size =
	(i != (sym_ndatasyms - 1)
	 ? (sym_datasyms[i+1]->addr - sym_datasyms[i]->addr)
	 : ((ld_data_base + ld_data_size) - sym_datasyms[i]->addr));
    }
#endif

  /* symbols are now available for use */
  syms_loaded = TRUE;
}

/* dump symbol SYM to output stream FD */
void
sym_dumpsym(struct sym_sym_t *sym,	/* symbol to display */
	    FILE *fd)			/* output stream */
{
  fprintf(fd,
    "sym `%s': %s seg, init-%s, pub-%s, local-%s, addr=0x%08x, size=%d\n",
	  sym->name,
	  sym->seg == ss_data ? "data" : "text",
	  sym->initialized ? "y" : "n",
	  sym->pub ? "y" : "n",
	  sym->local ? "y" : "n",
	  sym->addr,
	  sym->size);
}

/* dump all symbols to output stream FD */
void
sym_dumpsyms(FILE *fd)			/* output stream */
{
  int i;

  for (i=0; i < sym_nsyms; i++)
    sym_dumpsym(sym_syms[i], fd);
}

/* dump all symbols to output stream FD */
static void UNUSED
sym_dumptextsyms(FILE *fd)			/* output stream */
{
  int i;

  for (i=0; i < sym_ntextsyms; i++)
    sym_dumpsym(sym_textsyms[i], fd);
}

/* dump all symbol state to output stream FD */
void
sym_dumpstate(FILE *fd)			/* output stream */
{
  int i;

  if (fd == NULL)
    fd = stderr;

  fprintf(fd, "** All symbols sorted by address:\n");
  for (i=0; i < sym_nsyms; i++)
    sym_dumpsym(sym_syms[i], fd);

  fprintf(fd, "\n** All symbols sorted by name:\n");
  for (i=0; i < sym_nsyms; i++)
    sym_dumpsym(sym_syms_by_name[i], fd);

  fprintf(fd, "** Text symbols sorted by address:\n");
  for (i=0; i < sym_ntextsyms; i++)
    sym_dumpsym(sym_textsyms[i], fd);

  fprintf(fd, "\n** Text symbols sorted by name:\n");
  for (i=0; i < sym_ntextsyms; i++)
    sym_dumpsym(sym_textsyms_by_name[i], fd);

  fprintf(fd, "** Data symbols sorted by address:\n");
  for (i=0; i < sym_ndatasyms; i++)
    sym_dumpsym(sym_datasyms[i], fd);

  fprintf(fd, "\n** Data symbols sorted by name:\n");
  for (i=0; i < sym_ndatasyms; i++)
    sym_dumpsym(sym_datasyms_by_name[i], fd);
}

const char *
sym_lookup_name(md_addr_t addr, int exact, enum sym_db_t db)
{
  struct sym_sym_t *sym = sym_bind_addr(addr, NULL, exact, db);
  if (sym == NULL)
    return NULL;
  return sym->name;
}

/* bind address ADDR to a symbol in symbol database DB, the address must
   match exactly if EXACT is non-zero, the index of the symbol in the
   requested symbol database is returned in *PINDEX if the pointer is
   non-NULL */
struct sym_sym_t *			/* symbol found, or NULL */
sym_bind_addr(md_addr_t addr,		/* address of symbol to locate */
	      int *pindex,		/* ptr to index result var */
	      int exact,		/* require exact address match? */
	      enum sym_db_t db)		/* symbol database to search */
{
  int nsyms, low, high, pos;
  struct sym_sym_t **syms;

  switch (db)
    {
    case sdb_any:
      syms = sym_syms;
      nsyms = sym_nsyms;
      break;
    case sdb_text:
      syms = sym_textsyms;
      nsyms = sym_ntextsyms;
      break;
    case sdb_data:
      syms = sym_datasyms;
      nsyms = sym_ndatasyms;
      break;
    default:
      panic("bogus symbol database");
    }

  /* any symbols to search? */
  if (!nsyms)
    {
      if (pindex)
	*pindex = -1;
      return NULL;
    }

  /* binary search symbol database (sorted by address) */
  low = 0;
  high = nsyms-1;
  pos = (low + high) >> 1;
  while (!(/* exact match */
	   (exact && syms[pos]->addr == addr)
	   /* in bounds match */
	   || (!exact
	       && syms[pos]->addr <= addr
	       && addr < (syms[pos]->addr + MAX(1, syms[pos]->size)))))
    {
      if (addr < syms[pos]->addr)
	high = pos - 1;
      else
	low = pos + 1;
      if (high >= low)
	pos = (low + high) >> 1;
      else
	{
	  if (pindex)
	    *pindex = -1;
	  return NULL;
	}
    }

  /* bound! */
  if (pindex)
    *pindex = pos;
  return syms[pos];
}

/* bind name NAME to a symbol in symbol database DB, the index of the symbol
   in the requested symbol database is returned in *PINDEX if the pointer is
   non-NULL */
struct sym_sym_t *				/* symbol found, or NULL */
sym_bind_name(char *name,			/* symbol name to locate */
	      int *pindex,			/* ptr to index result var */
	      enum sym_db_t db)			/* symbol database to search */
{
  int nsyms, low, high, pos, cmp;
  struct sym_sym_t **syms;

  switch (db)
    {
    case sdb_any:
      syms = sym_syms_by_name;
      nsyms = sym_nsyms;
      break;
    case sdb_text:
      syms = sym_textsyms_by_name;
      nsyms = sym_ntextsyms;
      break;
    case sdb_data:
      syms = sym_datasyms_by_name;
      nsyms = sym_ndatasyms;
      break;
    default:
      panic("bogus symbol database");
    }

  /* any symbols to search? */
  if (!nsyms)
    {
      if (pindex)
	*pindex = -1;
      return NULL;
    }

  /* binary search symbol database (sorted by name) */
  low = 0;
  high = nsyms-1;
  pos = (low + high) >> 1;
  while (!(/* exact string match */!(cmp = strcmp(syms[pos]->name, name))))
    {
      if (cmp > 0)
	high = pos - 1;
      else
	low = pos + 1;
      if (high >= low)
	pos = (low + high) >> 1;
      else
	{
	  if (pindex)
	    *pindex = -1;
	  return NULL;
	}
    }

  /* bound! */
  if (pindex)
    *pindex = pos;
  return syms[pos];
}
