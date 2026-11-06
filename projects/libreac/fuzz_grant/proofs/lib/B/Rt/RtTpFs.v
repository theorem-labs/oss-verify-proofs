(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_grant image B (a Theorem Labs lane); rdword_cell_c8 adapted from proofs/cgif/cgif_file_fuzzer/lib/YG0s.v:50-55 (rdword_cell). proves no function (kind: segment lemma). *)
(* RT_TP_FS (lib/B/Prog/GrantBContracts.v:367) asks, of every state that
   satisfies AR, that the 8-byte word at the thread pointer (__asan::fake_stack_tls, PT_TLS offset 0) is the fake
   stack's base ly_F. AR already carries that word: its constant cells (ARm.am_const, Reusable/YG0n.v:211) hold for
   every cell of as_const B ly, and image B's Tfib_const_sym (lib/B/YF0m.v:26)
   contains `c8 (ATp 0) (AF 0)`. So RT_TP_FS follows from AR alone, for every B whose as_const has that cell:
   `rt_tp_fs_of_const` below. Its image-B instance needs only `In (c8 (ATp 0) (AF 0)) (as_const B ly)`, which the B
   core's TfibSyms (ts_const : as_const B ly = Tfib_const ly) gives by computation (lib/B/YF0l.v / YF0m.v; lib/B/GrantBCloseInst.v:181 grantB_TP_FS).
   No at-main fact is used here: the at-main half of the same cell is part of AR's discharge at main (measured: in
   all 50 hand-off states of YB01 the word at RT_TP 0x5d8910 is the literal KWord 4096 * V424, with KRange V424
   [1531, 34359733495] and the app-band KDisj; internal notes). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section tp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* rdword_cell (Reusable/YG0s.v:49) for a cell at any address expression with any value expression. *)
Lemma rdword_cell_c8 : forall ly rd e v, 0 <= aeval B ly v < 2 ^ 64 ->
  cell_holds B ly rd (c8 e v) -> rdword rd (aeval B ly e) = Some (aeval B ly v).
Proof.
intros ly rd e v Hv Hc. unfold cell_holds in Hc. cbn [c_at c_val c_w c8] in Hc.
unfold rdword.
pose proof (Hc 0%nat ltac:(lia)) as H0. pose proof (Hc 1%nat ltac:(lia)) as H1. pose proof (Hc 2%nat ltac:(lia)) as H2.
pose proof (Hc 3%nat ltac:(lia)) as H3. pose proof (Hc 4%nat ltac:(lia)) as H4. pose proof (Hc 5%nat ltac:(lia)) as H5.
pose proof (Hc 6%nat ltac:(lia)) as H6. pose proof (Hc 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* The fake stack's base lies in app memory (layout_ok's lo_app over owned_extents, Reusable/YG0f.v:295, :319), so it
   is below 2 ^ 64. *)
Lemma ly_F_range : forall ly, layout_ok ly -> 0 <= ly_F ly < 2 ^ 64.
Proof.
intros ly HL. pose proof (lo_app ly HL) as HA. unfold owned_extents in HA.
pose proof (proj1 (Forall_forall _ _) HA (ly_F ly, kFakeStackSize) ltac:(cbn; tauto)) as Hin.
cbn [fst snd] in Hin. unfold in_app, kLowShadowBeg, kHighMemBeg, kFakeStackSize in Hin.
pose proof (proj1 (@ASAN_CEIL_range rc)) as CR. lia.
Qed.

(* RT_TP_FS's statement, over any image whose constant cells include the thread-pointer cell. *)
Lemma rt_tp_fs_of_const :
  (forall ly, In (c8 (ATp 0) (AF 0)) (as_const B ly)) ->
  forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  rdword (aview segs (w_H W) mem) (as_tp B) = Some (ly_F ly).
Proof.
intros Hin ly S W mem md [HM _].
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ HM) _ (Hin ly)) as Hc.
pose proof (rdword_cell_c8 ly (aview segs (w_H W) mem) (ATp 0) (AF 0)) as R. cbn [aeval] in R. rewrite !Z.add_0_r in R.
apply R; [apply (ly_F_range ly (am_layout _ _ _ _ HM)) | exact Hc].
Qed.
End tp.
