(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan-ubsan image B, the cf allocator bridge, part 1 (row G-BCF): the
   trace-universe premise of the cf call-site rules from the caller-context premise of the `_x` journal rules. The B
   twin of lib/A/CfRBridgeCtx.v at c6394a5bd7e (a Theorem Labs lane R), RE-PROVED at image B: the same names and the same
   statements over image B's tables.
   A journal rule (lib/B/W_journal_x.v Section hc: amalloc_cf_rule_c_x, afree_cf_rule_c_x, afree_null_cf_rule_c_x,
   arealloc_cf_rule_c_x) gives `In (raZ regsT :: spine ch) CTX` at its own K0 table (lib/B/YCk0.v CTX_AMALLOC /
   CTX_AFREE / CTX_AREALLOC). The call-site rules (Reusable/YGcallx.v aj_malloc_at_x_ct / aj_free_at_x_ct, and this
   tree's CfRBridgeAjFreeNB / CfRBridgeAjReallocB) take `In (call_trace ly pc0 regs ch) (as_universe B)` and turn it
   into the P'' realizes texts' `admits` themselves (YG01.admits_fix, from universe_ok). At B := TfibB (lib/B/YD2l.v;
   as_universe TfibB is univ_of Tfib_universe [], whose fixed part is lib/B/YCej.v's Tfib_universe) the entry pc of
   each interceptor's trace is the pc0 of K0's site table (lib/B/YCk0.v:196-201: 0x540e4 malloc, 0x53f84 free,
   0x54380 realloc), checked by computation, and K0's closure (YCk0.v K0_CLOSED) gives the membership.
   cf_tr_ok / cf_trace_ok keep the A file's body `In tr (as_universe B)`, the form the rules take on this carry.
   No function is proved (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YCbq K0Closure.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCej YD2l CfImgB YCk0.
Import ListNotations.
Local Open Scope Z_scope.

(* The trace premise, one name (the layer's YGcfInstBase.v Section b text). *)
Section b.
Variable B : asyms.
Definition cf_tr_ok (tr : list Z) (S : astate) : Prop := In tr (as_universe B).
Definition cf_trace_ok (ly : alayout) (pc0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) (S : astate) : Prop :=
  cf_tr_ok (call_trace ly pc0 regs ch) S.
End b.

(* malloc: the trace of __wrap_malloc's unwinder starts at pc_malloc_ra0 (K0's CTX_AMALLOC site, pc0 0x540e4). *)
Lemma cfr_ctx_amalloc : forall ly regs ch S, In (raZ regs :: spine ch) CTX_AMALLOC ->
cf_trace_ok TfibB ly (pc_malloc_ra0 (as_code TfibB)) regs ch S.
Proof.
intros ly regs ch S H. unfold cf_trace_ok, cf_tr_ok.
let x' := eval vm_compute in (pc_malloc_ra0 (as_code TfibB)) in
replace (pc_malloc_ra0 (as_code TfibB)) with x' by (vm_compute; reflexivity).
exact (k0_amalloc ly regs ch H).
Qed.

(* free, of a block or of NULL: the trace starts at pc_free_ra0 (K0's CTX_AFREE site, pc0 0x53f84). *)
Lemma cfr_ctx_afree : forall ly regs ch S, In (raZ regs :: spine ch) CTX_AFREE ->
cf_trace_ok TfibB ly (pc_free_ra0 (as_code TfibB)) regs ch S.
Proof.
intros ly regs ch S H. unfold cf_trace_ok, cf_tr_ok.
let x' := eval vm_compute in (pc_free_ra0 (as_code TfibB)) in
replace (pc_free_ra0 (as_code TfibB)) with x' by (vm_compute; reflexivity).
exact (k0_afree ly regs ch H).
Qed.

(* realloc: the trace starts at image B's cf_pc_realloc_ra0 (CfImgB.v; K0's CTX_AREALLOC site, pc0 0x54380). *)
Lemma cfr_ctx_arealloc : forall ly regs ch S, In (raZ regs :: spine ch) CTX_AREALLOC ->
cf_trace_ok TfibB ly (@cf_pc_realloc_ra0 CfImg_B) regs ch S.
Proof.
intros ly regs ch S H. unfold cf_trace_ok, cf_tr_ok.
let x' := eval vm_compute in (@cf_pc_realloc_ra0 CfImg_B) in
replace (@cf_pc_realloc_ra0 CfImg_B) with x' by (vm_compute; reflexivity).
exact (k0_arealloc ly regs ch H).
Qed.

(* POSITIVE CONTROLS: each lemma's conclusion, through admits_fix at YCej.v's Tfib_universe_ok, fills the
   trace-universe slot of the cf form it feeds, at B := TfibB and image B's CfImg (the forms as this tree states them:
   Reusable/YG0dcf.v amalloc_realizes_cf / afree_realizes_cf, Reusable/YGcfRealloc.v arealloc_realizes_cf /
   arealloc_null_realizes_cf). Each term type-checks only if the conclusion is the `In` text that admits_fix reads. *)
Section ctl.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
#[local] Existing Instance CfImg_B.
Variable segs : list Segment.
Check (fun (H : amalloc_realizes_cf segs TfibB) ly S Hp W regs mem md n ch P G N L C =>
  H ly S Hp W regs mem md n ch P G N L (admits_fix _ _ S Tfib_universe_ok (cfr_ctx_amalloc ly regs ch S C))).
Check (fun (H : afree_realizes_cf segs TfibB) ly S Hp W regs mem md p n ch P B0 G NH C =>
  H ly S Hp W regs mem md p n ch P B0 G NH (admits_fix _ _ S Tfib_universe_ok (cfr_ctx_afree ly regs ch S C))).
Check (fun (Hp : list Z) (pc : Z) (H : YGcfRealloc.arealloc_realizes_cf segs TfibB Hp pc)
  ly S W regs mem md p n_old n ch P R I G1 G2 N L C =>
  H ly S W regs mem md p n_old n ch P R I G1 G2 N L (admits_fix _ _ S Tfib_universe_ok (cfr_ctx_arealloc ly regs ch S C))).
Check (fun (Hp : list Z) (pc : Z) (H : YGcfRealloc.arealloc_null_realizes_cf segs TfibB Hp pc)
  ly S W regs mem md n ch P R G0 G1 N L C =>
  H ly S W regs mem md n ch P R G0 G1 N L (admits_fix _ _ S Tfib_universe_ok (cfr_ctx_arealloc ly regs ch S C))).
End ctl.

Print Assumptions cfr_ctx_amalloc.
Print Assumptions cfr_ctx_afree.
Print Assumptions cfr_ctx_arealloc.
