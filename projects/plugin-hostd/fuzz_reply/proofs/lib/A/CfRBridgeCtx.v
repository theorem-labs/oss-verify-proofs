(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan, the cf allocator bridge (a Theorem Labs lane R, new file), part 1:
   the trace-universe premise of the cf realizes forms from the caller-context premise of the `_x` journal rules.
   A journal rule (W_journal_x.v:1438 amalloc_cf_rule_c_x, :770 afree_cf_rule_c_x, :794 afree_null_cf_rule_c_x,
   :816 arealloc_cf_rule_c_x) gives `In (raZ regsT :: spine ch) CTX` at its own K0 table (A/ACk0.v CTX_AMALLOC /
   CTX_AFREE / CTX_AREALLOC); the cf realizes forms take `In (call_trace ly pc0 regs ch) (as_universe B)`
   (Reusable/YG0dcf.v:145 amalloc_realizes_cf, :167 afree_realizes_cf; YGcfRealloc's arealloc forms at
   cf_pc_realloc_ra0).  At B := TfibB (A/AD2l.v; as_universe TfibB is Tfib_universe) the entry pc of each
   interceptor's trace is the pc0 of K0's site table (ACk0.v:180-182), checked by computation, and K0's closure
   theorem (ACk0.v:196-201, kernel-checked by K0_CLOSED) gives the membership.
   The conclusions are stated through cf_tr_ok / cf_trace_ok, the layer's ONE name for the trace premise (TkSecLink,
   commit d48cd401d143, YGcfInstBase.v Section b, same text and argument order): today's body is
   `In tr (as_universe B)`, the form this tree's cf rules take; the P'' round edits only cf_tr_ok's body to
   `admits (as_universe B) tr S` (A7d a3e599d9f79e YG01.v:158) and closes these three by admits_fix with reply's
   universe_ok (as_universe TfibB): every trace here is FIXED (Tfib_universe, ACej.v:202-244).
   No function is proved (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YCbq K0Closure.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACej AD2l CfImgA ACk0.
Import ListNotations.
Local Open Scope Z_scope.

(* The trace premise, one name (the layer's YGcfInstBase.v Section b text). *)
Section b.
Variable B : asyms.
Definition cf_tr_ok (tr : list Z) (S : astate) : Prop := In tr (as_universe B).
Definition cf_trace_ok (ly : alayout) (pc0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) (S : astate) : Prop :=
  cf_tr_ok (call_trace ly pc0 regs ch) S.
End b.

(* malloc: the trace of __wrap_malloc's unwinder starts at pc_malloc_ra0 (K0's CTX_AMALLOC site, pc0 0x5408c). *)
Lemma cfr_ctx_amalloc : forall ly regs ch S, In (raZ regs :: spine ch) CTX_AMALLOC ->
cf_trace_ok TfibB ly (pc_malloc_ra0 (as_code TfibB)) regs ch S.
Proof.
intros ly regs ch S H. unfold cf_trace_ok, cf_tr_ok.
let x' := eval vm_compute in (pc_malloc_ra0 (as_code TfibB)) in
replace (pc_malloc_ra0 (as_code TfibB)) with x' by (vm_compute; reflexivity).
exact (k0_amalloc ly regs ch H).
Qed.

(* free, of a block or of NULL: the trace starts at pc_free_ra0 (K0's CTX_AFREE site, pc0 0x53f2c). *)
Lemma cfr_ctx_afree : forall ly regs ch S, In (raZ regs :: spine ch) CTX_AFREE ->
cf_trace_ok TfibB ly (pc_free_ra0 (as_code TfibB)) regs ch S.
Proof.
intros ly regs ch S H. unfold cf_trace_ok, cf_tr_ok.
let x' := eval vm_compute in (pc_free_ra0 (as_code TfibB)) in
replace (pc_free_ra0 (as_code TfibB)) with x' by (vm_compute; reflexivity).
exact (k0_afree ly regs ch H).
Qed.

(* realloc: the trace starts at image A's cf_pc_realloc_ra0 (CfImgA.v:50; K0's CTX_AREALLOC site, pc0 0x54328). *)
Lemma cfr_ctx_arealloc : forall ly regs ch S, In (raZ regs :: spine ch) CTX_AREALLOC ->
cf_trace_ok TfibB ly (@cf_pc_realloc_ra0 CfImg_A) regs ch S.
Proof.
intros ly regs ch S H. unfold cf_trace_ok, cf_tr_ok.
let x' := eval vm_compute in (@cf_pc_realloc_ra0 CfImg_A) in
replace (@cf_pc_realloc_ra0 CfImg_A) with x' by (vm_compute; reflexivity).
exact (k0_arealloc ly regs ch H).
Qed.

(* POSITIVE CONTROLS: each lemma's conclusion, through admits_fix (YG01.v; every trace here is FIXED), fills the
   trace slot of the cf form it feeds, at B := TfibB and image A's CfImg (the forms as this tree states them:
   Reusable/YG0dcf.v amalloc_realizes_cf / afree_realizes_cf, Reusable/YGcfRealloc.v arealloc_realizes_cf /
   arealloc_null_realizes_cf, whose trace premise is `admits (as_universe B) (call_trace ..) S`).  Each term
   type-checks only if the conclusion, converted, is that premise's exact text.  HU is the universe's bounds
   (universe_ok (as_universe TfibB)), which a top discharges by its image fact. *)
Section ctl.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
#[local] Existing Instance CfImg_A.
Variable segs : list Segment.
Variable HU : universe_ok (as_universe TfibB).
Check (fun (H : amalloc_realizes_cf segs TfibB) ly S Hp W regs mem md n ch P G N L C =>
  H ly S Hp W regs mem md n ch P G N L (admits_fix _ _ S HU (cfr_ctx_amalloc ly regs ch S C))).
Check (fun (H : afree_realizes_cf segs TfibB) ly S Hp W regs mem md p n ch P B0 G NH C =>
  H ly S Hp W regs mem md p n ch P B0 G NH (admits_fix _ _ S HU (cfr_ctx_afree ly regs ch S C))).
Check (fun (Hp : list Z) (pc : Z) (H : YGcfRealloc.arealloc_realizes_cf segs TfibB Hp pc)
  ly S W regs mem md p n_old n ch P R I G1 G2 N L C =>
  H ly S W regs mem md p n_old n ch P R I G1 G2 N L (admits_fix _ _ S HU (cfr_ctx_arealloc ly regs ch S C))).
Check (fun (Hp : list Z) (pc : Z) (H : YGcfRealloc.arealloc_null_realizes_cf segs TfibB Hp pc)
  ly S W regs mem md n ch P R G0 G1 N L C =>
  H ly S W regs mem md n ch P R G0 G1 N L (admits_fix _ _ S HU (cfr_ctx_arealloc ly regs ch S C))).
End ctl.

Print Assumptions cfr_ctx_amalloc.
Print Assumptions cfr_ctx_afree.
Print Assumptions cfr_ctx_arealloc.
