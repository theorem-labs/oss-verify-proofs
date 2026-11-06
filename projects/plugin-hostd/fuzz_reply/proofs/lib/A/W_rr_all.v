(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the composition of the ASan walk of fuzz_reply's relay_remove: the segment
   statements of lib/A/W_relay_remove_cx.v give rr_spec (rr_all_stmt), by plain application at the cut points. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (a Theorem Labs lane, lane RR_x): the composition concludes the generic
   rr_spec_x (any ARx, PST, room record RP); the entry record takes the head set Hp and the room budget kr. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Variable CTX_AFREE : list (list Z).

Theorem rr_all : rr_all_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold rr_all_stmt. intros PRO SCAN SCANS MATCH TAIL.
unfold rr_spec_x. intros W ly S Hp regs mem md ch G0 FD es j h c O mx cap out. cbv zeta.
intros Hpre H32 Hcnt Hrg H10 HFD Hl Hw Hrel Hout Hrom Hsrc (rest & Hperm) Htm Hbb Hmo kr HRM HCNT Hroom Hctx.
pose (cx := mkRcx regs ly S Hp W mem md ch G0 FD es j h c O mx cap out rest kr).
assert (HC : RCTX CTX_AFREE cx) by (split; [exact Hroom | exact Hctx]).
assert (HB : RBASE B ARx MT RP MMAX RG cx).
{ unfold RBASE, rsp0, rnth, rtr. cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx
    rxcap rxout rxrest rxkr cx].
  repeat (split; [assumption|]); assumption. }
change (SRr SEGS (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx)) (rPOST B PST ARx MT RP RG cx)).
apply (PRO cx HB).
- intros W2 c2 HL. apply (SCANS SCAN cx 0%nat W2 c2 HB HL).
  + intros i W3 c3 HM. apply (MATCH cx i W3 c3 HB HC HM).
    intros W4 c4 HU. exact (TAIL cx (Some i) W4 c4 HB HU).
  + intros W3 c3 HU. exact (TAIL cx None W3 c3 HB HU).
- intros W2 c2 HU. exact (TAIL cx None W2 c2 HB HU).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the composition at a world relation R: the segment statements' R twins
   (W_relay_remove_cx.v rr_*_stmt_xR) give W_contract_xR_relay.rr_spec_xR (a Theorem Labs lane's), by the same application.
   rr_all is rr_all_xR at R := wle (rr_all_stmt_wle, rr_spec_x_wle). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
(* :46 rr_all *)
Theorem rr_all_xR : rr_all_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
unfold rr_all_stmt_xR. intros PRO SCAN SCANS MATCH TAIL.
unfold rr_spec_xR. intros W ly S Hp regs mem md ch G0 FD es j h c O mx cap out. cbv zeta.
intros Hpre H32 Hcnt Hrg H10 HFD Hl Hw Hrel Hout Hrom Hsrc (rest & Hperm) Htm Hbb Hmo kr HRM HCNT Hroom Hctx.
pose (cx := mkRcx regs ly S Hp W mem md ch G0 FD es j h c O mx cap out rest kr).
assert (HC : RCTX CTX_AFREE cx) by (split; [exact Hroom | exact Hctx]).
assert (HB : RBASE B ARx MT RP MMAX RG cx).
{ unfold RBASE, rsp0, rnth, rtr. cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx
    rxcap rxout rxrest rxkr cx].
  repeat (split; [assumption|]); assumption. }
change (YA0nH.SRrG SEGS R (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx)) (rPOST_xR B PST ARx MT RP RG R cx)).
apply (PRO cx HB).
- intros W2 c2 HL. apply (SCANS SCAN cx 0%nat W2 c2 HB HL).
  + intros i W3 c3 HM. apply (MATCH cx i W3 c3 HB HC HM).
    intros W4 c4 HU. exact (TAIL cx (Some i) W4 c4 HB HU).
  + intros W3 c3 HU. exact (TAIL cx None W3 c3 HB HU).
- intros W2 c2 HU. exact (TAIL cx None W2 c2 HB HU).
Qed.
End wR.

End a.
