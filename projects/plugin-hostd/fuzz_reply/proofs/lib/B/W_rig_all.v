(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE-B twin of lib/A/W_rig_all.v (text unchanged but the imports): the composition of the ASan walk of fuzz_reply's relay_instance_gone: the
   segment statements of lib/A/W_relay_instance_gone_cx.v give rig_spec (rig_all_stmt), by plain application at the
   cut points.  Route (b), step 3 (the image-A twin's RIG_x round, a Theorem Labs lane f4cd818e98d): over any allocator relation
   ARx, the program statics PST and the room record RP; the entry record carries rig_spec_x's head set Hp and room
   budget kr; the conclusion is rig_spec_x. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_instance_gone_cx.
(* route R: a Theorem Labs lane's B rig_spec_xR and SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
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

Theorem rig_all : rig_all_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof.
unfold rig_all_stmt. intros PRO TOP KEY STEP KEYS OUTER TAIL.
unfold rig_spec_x. intros W ly S Hp regs mem md ch G0 ID es hs c O mx cap out. cbv zeta.
intros Hpre H32 Hcnt Hrg H10 HID Hl Hrel Hout Hrom Hlen Hsrc Hnd (rest & Hperm) Htm Hbb Hmo kr Hroom Hcntk
  Hsp Hctx.
pose (cx := mkGcx regs ly S Hp W mem md ch G0 ID es hs c O mx cap out rest kr).
assert (HC : GCTX CTX_AFREE cx) by (split; [exact Hsp | exact Hctx]).
assert (HB : GBASE B ARx MT RP MMAX RG cx).
{ unfold GBASE, gsp0, gps, gtr. cbn [gxregs gxly gxS gxHp gxW gxmem gxmd gxch gxG0 gxID gxes gxhs gxc gxO gxmx gxcap
    gxout gxrest gxkr cx].
  repeat (split; [assumption|]); assumption. }
change (SRr SEGS (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx)) (gPOST B PST ARx MT RP RG cx)).
apply (PRO cx HB).
- intros W2 c2 HO. apply (OUTER TOP KEY KEYS STEP cx 0%nat W2 c2 HB HC HO).
  intros W3 c3 HU. exact (TAIL cx W3 c3 HB HU).
- intros W2 c2 HU. exact (TAIL cx W2 c2 HB HU).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): rig_all at a world relation R, the composition of the segments' R statements
   (W_relay_instance_gone_cx.v Section wR) into a Theorem Labs lane's B rig_spec_xR (W_contract_xR_relayB.v).  The proof is
   rig_all's text with each name -> its R twin and SRr SEGS -> SRrG SEGS R; it reads no law of R.  Image A's twin:
   lib/A/W_rig_all.v Section wR. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Theorem rig_all_xR : rig_all_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE R.
Proof.
unfold rig_all_stmt_xR. intros PRO TOP KEY STEP KEYS OUTER TAIL.
unfold rig_spec_xR. intros W ly S Hp regs mem md ch G0 ID es hs c O mx cap out. cbv zeta.
intros Hpre H32 Hcnt Hrg H10 HID Hl Hrel Hout Hrom Hlen Hsrc Hnd (rest & Hperm) Htm Hbb Hmo kr Hroom Hcntk
  Hsp Hctx.
pose (cx := mkGcx regs ly S Hp W mem md ch G0 ID es hs c O mx cap out rest kr).
assert (HC : GCTX CTX_AFREE cx) by (split; [exact Hsp | exact Hctx]).
assert (HB : GBASE B ARx MT RP MMAX RG cx).
{ unfold GBASE, gsp0, gps, gtr. cbn [gxregs gxly gxS gxHp gxW gxmem gxmd gxch gxG0 gxID gxes gxhs gxc gxO gxmx gxcap
    gxout gxrest gxkr cx].
  repeat (split; [assumption|]); assumption. }
change (SRrG SEGS R (gxW cx) (cfg_at SEGS A_rig_entryP (gxregs cx) (gxmem cx) (gxmd cx)) (gPOST_xR B PST ARx MT RP RG R cx)).
apply (PRO cx HB).
- intros W2 c2 HO. apply (OUTER TOP KEY KEYS STEP cx 0%nat W2 c2 HB HC HO).
  intros W3 c3 HU. exact (TAIL cx W3 c3 HB HU).
- intros W2 c2 HU. exact (TAIL cx W2 c2 HB HU).
Qed.
End wR.
(* at R := wle *)
Lemma rig_all_of_xR : rig_all_stmt_xR B PST ARx MT RP MMAX RG CTX_AFREE (@wle SEGS) -> rig_all_stmt B PST ARx MT RP MMAX RG CTX_AFREE.
Proof. intros H. exact H. Qed.
End a.
