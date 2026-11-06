(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module paths and module names changed; 334 of its 373 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/text_ofMal.v, with its module paths and module names changed; 17 of its 43 lines of code are new or changed and 347 lines of the source are left out. *)
(* text_of (fuzz_link.asan 0x87dc0, listing offset AF_text_of = 0x5bf4) on image A against its contract
   lib/A/Prog/text_of_c.v `text_of_acontract` (aleaf_alloc_rd over the caller's journal), by the walk of
   lib/A/Prog/text_of*.v:
     text_ofHead.v  to_head   entry .. the TABLE cut (+0x144) and the U16 cut (+0x1a8)
     text_ofTable.v to_table  the TABLE cut .. ret (the selector's text)
     text_ofU16.v   to_u16    the U16 cut .. the MALLOC cut (v mod 320, the cursor, memchr)
     text_ofMal.v   to_mal    the MALLOC cut .. ret (malloc, checked_memcpy, the NUL, *own)
   cut interface lib/A/Prog/text_ofDefs.v and lib/A/Prog/text_ofKit.v.

   Section hypotheses (each discharged at the image in text_of_img.v): LAWS (AR_laws), TL (PALib), LV (LinkVals),
   MTL (the meter's laws), TB (PcapSyms), MEMCHR (wrapper_memchr), MC_RO (memchr's constants are read-only image
   bytes), MALLOCW (the malloc rule with the wild trace, lib/A/Rt/LinkMallocDepotW.v), AMCPY (checked_memcpy),
   HSEGS (pa_segs = tfibsegs). The malloc arm's premise TO_HO (the shadow hull of *own at the call) is the Pre's
   conjunct (text_ofKit.v to_pre_ho).

   Proves text_of (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d YC5d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0n YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym LinkSyms LinkList LinkAddr LinkPa
  LinkPaLib LinkWalk link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepotW.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  text_of_c text_ofDefs text_ofKit text_ofHead text_ofTable text_ofU16 text_ofMal.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis MTL : ameter_laws MT.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis MEMCHR : amemchr_realizesM SEGS B 0x10360 0x10380 (pa_sigma LS___interceptor_trampoline_memchr).
Hypothesis MC_RO : forall a, 0x10360 <= a < 0x10380 -> in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).
Hypothesis MALLOCW : amalloc04_rule_dw (SK := SK) SEGS B MT.
Hypothesis AMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.

Theorem text_of_aproof : forall rlo rhi, text_of_acontract SK SEGS rlo rhi B MT CTX.
Proof.
  assert (TAB : to_table_obl SK B MT CTX)
    by exact (to_table SK B MT CTX LAWS LV MTL (fun cx HPX => to_pre_happ SK B MT CTX cx HPX)).
  assert (MAL : to_mal_obl SK B MT CTX) by exact (to_mal SK B MT CTX LAWS TL LV MTL TB HSEGS MALLOCW AMCPY (to_pre_ho SK B MT CTX)).
  exact (to_head SK B MT CTX LAWS TL LV TAB (to_u16 SK B MT CTX LAWS MEMCHR MC_RO MAL)).
Qed.

End b.
End a.

Print Assumptions text_of_aproof.
