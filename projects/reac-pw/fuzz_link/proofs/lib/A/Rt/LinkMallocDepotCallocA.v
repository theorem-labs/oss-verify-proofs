(* link's instance of lib/A/Rt/LinkMallocDepotCalloc.v acalloc04_rule_d (the calloc rule with the io clause and the
   depot step of the trace calloc hands to the malloc model), at lib/A/LinkACalloc.v link_acalloc04's instance: segs
   := tfibsegs, the journal YCbq.ajournal at the sink head SK (passed by name), YCbq.acall_kept, the trivial meter,
   pc 0x540d0 (DEC_A_wrap_calloc), trace pc0 0x545a0 (DEC_A_calloc_ra0), cmax 8856, cdepth 2192, for every certificate
   B of link's image with LinkACalloc.v's Section hypotheses TS, TL, HD. Built as link_acalloc04 is, from
   LinkMallocDepotCalloc.v acalloc04_rule_d_triv with LinkACalloc.v link_calloc_univ0 and link_calloc_realizes. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YI16 YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YGCalloc YCbpCalloc YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AFl0 ACeh DecodeCalloc DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import LinkACalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepotCalloc.
Import ListNotations.
Open Scope Z_scope.

Section c.
Variable B : asyms.
Hypothesis TS : PcapSyms B.
Hypothesis TL : TfibLib B.
Hypothesis HD : forall t, as_dhash B t = tfib_dhash t.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}
  {SK : OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YI16.sink_head}.
Definition link_acalloc04_d :
  acalloc04_rule_d tfibsegs B (as_universe B) (@ajournal rc SK tfibsegs B) (@acall_kept rc tfibsegs B)
    (mo_ok ameter_triv) (mo_le ameter_triv) (mo_malloc ameter_triv)
    DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH :=
  acalloc04_rule_d_triv (SK := SK) tfibsegs B tfib_segs_low (tl_env B TL) (AR_laws_ok tfibsegs B)
    (model_laws_ok (as_universe B) (ts_universe B TS))
    DEC_A_wrap_calloc DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH
    (link_calloc_univ0 B TL) (link_calloc_realizes B TS TL HD).
End b.
End c.

About link_acalloc04_d.
Print Assumptions link_acalloc04_d.
