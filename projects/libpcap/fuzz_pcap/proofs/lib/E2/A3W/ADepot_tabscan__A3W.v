(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexZero.
From Stdlib Require Sorting.Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Exec Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit AFreeRep AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ADepot_tabscan.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanHexZero.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

#[using="Type"] Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation S3 := Asan_seg_bytes_003 (only parsing).

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Lemma zscanN_complete : forall s f base n,
  (n <= 2 ^ N.of_nat f)%N ->
  (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) ->
  zscanN s (S f) base n = true.
Proof.
  intros s f. induction f as [|f IH]; intros base n Hn H.
  - cbn [zscanN]. change (2 ^ N.of_nat 0)%N with 1%N in Hn.
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1]; [|lia].
    unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
  - assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
    remember (S f) as f1 eqn:Ef1. cbn [zscanN].
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1].
    + unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
    + rewrite N.div2_div. set (h := (n / 2)%N).
      assert (Hh : (2 * h <= n < 2 * h + 2)%N).
      { unfold h. pose proof (N.div_mod n 2 ltac:(lia)) as D. pose proof (N.mod_lt n 2 ltac:(lia)). lia. }
      subst f1. apply andb_true_intro. split.
      * apply IH; [lia|]. intros i Hi. apply H. lia.
      * apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply H. lia.
Qed.
#[using="Type"] Lemma tab_scan : zscanN Asan_seg_bytes_003 64 0xe94d8 4194304 = true.
Proof.
  assert (ZW : zwin Asan_seg_bytes_003 (Uint63.of_Z 1911216) (Uint63.of_Z 8388608) = true) by (vm_cast_no_check (eq_refl true)).
  apply zscanN_complete; [change (2 ^ N.of_nat 63)%N with 9223372036854775808%N; lia|].
  intros i Hi. apply (zwin_hex_byte_at _ _ _ _ ZW).
  - vm_compute. intros HX. discriminate HX.
  - change (Uint63.to_Z (Uint63.of_Z 1911216)) with 1911216%Z. lia.
  - change (Uint63.to_Z (Uint63.of_Z 1911216)) with 1911216%Z. change (Uint63.to_Z (Uint63.of_Z 8388608)) with 8388608%Z. lia.
Qed.

#[using="Type"] Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma tab_byte_at : forall off : N, (0xe94d8 <= off < 0xe94d8 + 4194304)%N ->
  segment_byte_at (seg_bytes Asan_segment_003) off = Some (Z_to_bv 8 0).
Proof.
  intros off Hoff. cbn [seg_bytes Asan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (off <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace off with (0xe94d8 + (off - 0xe94d8))%N by lia.
  apply (zscanN_sound _ 64 _ 4194304 tab_scan). lia.
Qed.

End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

#[using="Type"] Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation S3 := AsanUbsan_seg_bytes_003 (only parsing).

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Lemma zscanN_complete : forall s f base n,
  (n <= 2 ^ N.of_nat f)%N ->
  (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) ->
  zscanN s (S f) base n = true.
Proof.
  intros s f. induction f as [|f IH]; intros base n Hn H.
  - cbn [zscanN]. change (2 ^ N.of_nat 0)%N with 1%N in Hn.
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1]; [|lia].
    unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
  - assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
    remember (S f) as f1 eqn:Ef1. cbn [zscanN].
    destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
    destruct (N.eqb_spec n 1) as [E1|N1].
    + unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
    + rewrite N.div2_div. set (h := (n / 2)%N).
      assert (Hh : (2 * h <= n < 2 * h + 2)%N).
      { unfold h. pose proof (N.div_mod n 2 ltac:(lia)) as D. pose proof (N.mod_lt n 2 ltac:(lia)). lia. }
      subst f1. apply andb_true_intro. split.
      * apply IH; [lia|]. intros i Hi. apply H. lia.
      * apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply H. lia.
Qed.
#[using="Type"] Lemma tab_scan : zscanN AsanUbsan_seg_bytes_003 64 0xe98d8 4194304 = true.
Proof.
  assert (ZW : zwin AsanUbsan_seg_bytes_003 (Uint63.of_Z 1913264) (Uint63.of_Z 8388608) = true) by (vm_cast_no_check (eq_refl true)).
  apply zscanN_complete; [change (2 ^ N.of_nat 63)%N with 9223372036854775808%N; lia|].
  intros i Hi. apply (zwin_hex_byte_at _ _ _ _ ZW).
  - vm_compute. intros HX. discriminate HX.
  - change (Uint63.to_Z (Uint63.of_Z 1913264)) with 1913264%Z. lia.
  - change (Uint63.to_Z (Uint63.of_Z 1913264)) with 1913264%Z. change (Uint63.to_Z (Uint63.of_Z 8388608)) with 8388608%Z. lia.
Qed.

#[using="Type"] Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55d000%N.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma tab_byte_at : forall off : N, (0xe98d8 <= off < 0xe98d8 + 4194304)%N ->
  segment_byte_at (seg_bytes AsanUbsan_segment_003) off = Some (Z_to_bv 8 0).
Proof.
  intros off Hoff. cbn [seg_bytes AsanUbsan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (off <? 0x55d000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace off with (0xe98d8 + (off - 0xe98d8))%N by lia.
  apply (zscanN_sound _ 64 _ 4194304 tab_scan). lia.
Qed.

End CANSEC2.
End TwB.
End ADepot_tabscan.

(* [comment removed for export] *)
Module AFreeStoreK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit AFreeRep AQConst. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab308, 0xab330); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Kinds.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl : Z).
Definition kfactsF : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6303744 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6303744 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP)   (* [comment removed for export] *)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
  /\ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104)      (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsF.

Ltac kband H := lazymatch type of H with
  | sclr ?a _ => lazymatch goal with |- context [a] => band_int H; clear H | |- _ => clear H end
  | iclr ?a _ => lazymatch goal with |- context [a] => band_int H; clear H | |- _ => clear H end
  end.
Ltac kdisj H x := lazymatch goal with |- context [x] => idtac | |- _ => clear H end.
(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with lst => constr:(res) | eb => constr:(res) | gl => constr:(res) | UB => constr:(res) | AB => constr:(res) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.
Ltac kdrop := lazymatch goal with |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in kkeep2 X Y | |- _ => idtac end.
Ltac kind1 Ft1 Ft2 Fn1 Fs1 Fc1 F_lst F_gl :=
  first [ solve [ kband Ft1; kband Ft2; kband Fn1; kband Fs1; kband Fc1; kdisj F_lst lst; kdisj F_gl gl; kdrop; klia ]
        | solve [ kband Ft1; kband Ft2; kband Fn1; kband Fs1; kband Fc1; kdisj F_lst lst; kdisj F_gl gl; lia ]
        | band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1; lia ].
Ltac kind := pose proof KF as KF'; unfold kfactsF, AIMG_HI in *;
  sg_set; (nd_pre KF' 10%nat; intros F_lo sgk1 F_res F_slot F_sh sgk2 sgk3 F_lst F_eb F_gl; nd_post); (nd_pre sgk1 4%nat; intros Ft1 Ft2 Ft3 Ft4; nd_post); (nd_pre sgk2 6%nat; intros Fn1 Fn2 Fn3 Fs1 Fs2 Fs3; nd_post); (nd_pre sgk3 3%nat; intros Fc1 Fc2 Fc3; nd_post);
  (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1 Ft1 Ft2 Fn1 Fs1 Fc1 F_lst F_gl|]); first [kind1 Ft1 Ft2 Fn1 Fs1 Fc1 F_lst F_gl | exact I].

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xab308 \/ 0xab330 <= A) /\ (A + k <= 0xaf800 \/ 0x130830 <= A) /\ (A + k <= 0x13e088 \/ 0x13e08c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_low : forall A k, 2147450880 <= A -> A + k <= 2148238848 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S lo grz ssz KF"] Lemma KF_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S ctx lo grz ssz KF"] Lemma KF_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S ctx lo grz ssz KF"] Lemma KF_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= UB - 16 \/ UB + 8 <= A) ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="AB S ctx lo grz ssz KF"] Lemma KF_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="AB S ctx lo grz ssz KF"] Lemma KF_objL : forall A k, (4096 <= A /\ (A + k <= 65536 \/ 6303744 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

#[using="MU WM"] Lemma aslots_update_gen : forall st st' X X' c,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
          /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b))
    \/ match busy_of X' c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [(EB & D & WFB)|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk). destruct (busy_of X c k) as [b|].
    + (nd_pre (WFB b eq_refl) 3%nat; intros C1' K1 FIT1; nd_post).
      eapply aslot_busy_frame; [exact MU| exact WM| exact SL | exact FIT1 |]. unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

#[using="MU WM"] Lemma aslot_shadow_update_gen : forall st st' X X' c,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (slot_shadow_bytes (size_of_class c) (busy_of X' c k) = slot_shadow_bytes (size_of_class c) (busy_of X c k)
          /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c)))
    \/ rw_cells asegs m' (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k))]) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [[EB D]|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL| exact MU| exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_shadow_bbatch : forall S k24,
  2 <= shlen S -> slot_shadow_bytes S (Some (bbatch k24)) = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S)).
Proof.
  intros S k24 H. unfold slot_shadow_bytes, bbatch. cbn [xb_n xb_st].
  replace (rz_size 0) with 16 by reflexivity. replace (shlen 16) with 2 by reflexivity. replace (granules 0) with 0 by reflexivity.
  rewrite <- !repeat_app. f_equal. lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab708, 0xab730); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Kinds.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl : Z).
Definition kfactsF : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6307840 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6307840 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP)   (* [comment removed for export] *)
  /\ ((lst = 0 /\ qsz lst = 8) \/ (res + 4096 <= lst /\ lst + 8192 <= res + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
  /\ (res + 4096 <= eb /\ eb + 8192 <= res + 137439023104)      (* [comment removed for export] *)
  /\ (gl = 0 \/ (res + 4096 <= gl /\ gl + 8192 <= res + 137439023104)).
Hypothesis KF : kfactsF.

Ltac kband H := lazymatch type of H with
  | sclr ?a _ => lazymatch goal with |- context [a] => band_int H; clear H | |- _ => clear H end
  | iclr ?a _ => lazymatch goal with |- context [a] => band_int H; clear H | |- _ => clear H end
  end.
Ltac kdisj H x := lazymatch goal with |- context [x] => idtac | |- _ => clear H end.
(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with lst => constr:(res) | eb => constr:(res) | gl => constr:(res) | UB => constr:(res) | AB => constr:(res) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.
Ltac kdrop := lazymatch goal with |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in kkeep2 X Y | |- _ => idtac end.
Ltac kind1 Ft1 Ft2 Fn1 Fs1 Fc1 F_lst F_gl :=
  first [ solve [ kband Ft1; kband Ft2; kband Fn1; kband Fs1; kband Fc1; kdisj F_lst lst; kdisj F_gl gl; kdrop; klia ]
        | solve [ kband Ft1; kband Ft2; kband Fn1; kband Fs1; kband Fc1; kdisj F_lst lst; kdisj F_gl gl; lia ]
        | band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1; lia ].
Ltac kind := pose proof KF as KF'; unfold kfactsF, AIMG_HI in *;
  sg_set; (nd_pre KF' 10%nat; intros F_lo sgk1 F_res F_slot F_sh sgk2 sgk3 F_lst F_eb F_gl; nd_post); (nd_pre sgk1 4%nat; intros Ft1 Ft2 Ft3 Ft4; nd_post); (nd_pre sgk2 6%nat; intros Fn1 Fn2 Fn3 Fs1 Fs2 Fs3; nd_post); (nd_pre sgk3 3%nat; intros Fc1 Fc2 Fc3; nd_post);
  (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1 Ft1 Ft2 Fn1 Fs1 Fc1 F_lst F_gl|]); first [kind1 Ft1 Ft2 Fn1 Fs1 Fc1 F_lst F_gl | exact I].

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xab708 \/ 0xab730 <= A) /\ (A + k <= 0xafc00 \/ 0x130c30 <= A) /\ (A + k <= 0x13e488 \/ 0x13e48c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_low : forall A k, 2147450880 <= A -> A + k <= 2148239360 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KF_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S lo grz ssz KF"] Lemma KF_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S ctx lo grz ssz KF"] Lemma KF_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 80 \/ t + 112 <= A) -> (A + k <= t + 2128 \/ t + 2132 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="rc AB S ctx lo grz ssz KF"] Lemma KF_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= UB - 16 \/ UB + 8 <= A) ->
  (A + k <= lst \/ lst + 8192 <= A) -> (A + k <= eb \/ eb + 8192 <= A) -> (A + k <= gl \/ gl + 8 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.

#[using="AB S ctx lo grz ssz KF"] Lemma KF_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="AB S ctx lo grz ssz KF"] Lemma KF_objL : forall A k, (4096 <= A /\ (A + k <= 65536 \/ 6307840 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wf sp t UB gq nodes store lst eb gl) A k.
Proof. intros. kind. Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

#[using="MU WM"] Lemma aslots_update_gen : forall st st' X X' c,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
          /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b))
    \/ match busy_of X' c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [(EB & D & WFB)|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk). destruct (busy_of X c k) as [b|].
    + (nd_pre (WFB b eq_refl) 3%nat; intros C1' K1 FIT1; nd_post).
      eapply aslot_busy_frame; [exact MU| exact WM| exact SL | exact FIT1 |]. unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

#[using="MU WM"] Lemma aslot_shadow_update_gen : forall st st' X X' c,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c ->
       (slot_shadow_bytes (size_of_class c) (busy_of X' c k) = slot_shadow_bytes (size_of_class c) (busy_of X c k)
          /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c)))
    \/ rw_cells asegs m' (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k))]) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c [SL UND] E0 E1 E2 OTH DU POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (OTH k Hk) as [[EB D]|NEW]; [| exact NEW].
    rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL| exact MU| exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_shadow_bbatch : forall S k24,
  2 <= shlen S -> slot_shadow_bytes S (Some (bbatch k24)) = repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S)).
Proof.
  intros S k24 H. unfold slot_shadow_bytes, bbatch. cbn [xb_n xb_st].
  replace (rz_size 0) with 16 by reflexivity. replace (shlen 16) with 2 by reflexivity. replace (granules 0) with 0 by reflexivity.
  rewrite <- !repeat_app. f_equal. lia.
Qed.
End CANSEC1.
End TwB.
End AFreeStoreK.

(* [comment removed for export] *)
Module ARecRep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma firstn_skipn_perm_mid : forall {A} (f c : list A) (i : nat) (x : A) (b1 b2 : list A),
  Permutation ((f ++ skipn i c) ++ (firstn i c ++ [x]) ++ (b1 ++ b2)) (f ++ c ++ (b1 ++ [x] ++ b2)).
Proof.
  intros A f c i x b1 b2. rewrite <- !app_assoc. apply Permutation_app_head.
  transitivity (firstn i c ++ skipn i c ++ [x] ++ b1 ++ b2); [apply Permutation_app_swap_app|].
  rewrite (app_assoc (firstn i c) (skipn i c)), firstn_skipn. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

#[using="Type"] Lemma perm_mid_to_front : forall {A} (f c : list A) (x : A) (b1 b2 : list A),
  Permutation (f ++ (c ++ [x]) ++ (b1 ++ b2)) (f ++ c ++ (b1 ++ [x] ++ b2)).
Proof.
  intros A f c x b1 b2. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

#[using="Type"] Lemma length_skipn_Z : forall {A} (l : list A) i, (i <= length l)%nat -> Z.of_nat (length (skipn i l)) = Z.of_nat (length l) - Z.of_nat i.
Proof. intros A l i Hi. rewrite length_skipn. lia. Qed.
#[using="Type"] Lemma length_firstn_Z : forall {A} (l : list A) i, (i <= length l)%nat -> Z.of_nat (length (firstn i l)) = Z.of_nat i.
Proof. intros A l i Hi. rewrite length_firstn. lia. Qed.

#[using="Type"] Lemma max_cached_range : forall c, 2 <= max_cached c <= 16 /\ 1 <= max_cached c / 2 <= 8 /\ max_cached c = 2 * (max_cached c / 2).
Proof.
  intros c. unfold max_cached.
  set (q := Z.max 1 (Z.min 8 (1024 / size_of_class c))). assert (1 <= q <= 8) by lia.
  rewrite (Z.mul_comm 2 q), Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Recyc.
Variables (L : alayout) (st : astate) (X : aconc) (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Variable drained : bool.
Hypothesis XB : x_busy X = l1 ++ bany s0 c k n b1 ctx :: l2.
Hypothesis WF : awf L st X.
Hypothesis NL : forall p, s0 <> BLive p.

Definition rcnt : Z := c_count (get_cls st c).
Definition rhalf : Z := max_cached c / 2.
Definition rcut : nat := Z.to_nat (rcnt - rhalf).
(* [comment removed for export] *)
Definition rcache' : list Z :=
  if drained then firstn rcut (xc_cache (x_cls X c)) ++ [k] else xc_cache (x_cls X c) ++ [k].
Definition rfree' : list Z :=
  if drained then xc_free (x_cls X c) ++ skipn rcut (xc_cache (x_cls X c)) else xc_free (x_cls X c).
Definition xrec : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass rfree' rcache' else x_cls X c') (l1 ++ l2).

#[using="rc L st X s0 k n b1 ctx l1 l2 XB WF"] Lemma rec_class : 1 <= c < K_NUM_CLASSES.
Proof. exact (any_class L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

#[using="rc L X s0 n b1 ctx l1 l2 XB WF"] Lemma rec_range : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof. exact (any_range L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

#[using="Type"] Lemma In_xrec : forall y, In y (x_busy xrec) <-> In y (l1 ++ l2).
Proof. intros y. unfold xrec. cbn [x_busy]. tauto. Qed.

#[using="Type"] Lemma busy_slots_xrec : forall c',
  busy_slots xrec c' = busy_slots (mkAConc (x_cls X) l1) c' ++ busy_slots (mkAConc (x_cls X) l2) c'.
Proof. intros c'. unfold busy_slots, xrec. cbn [x_busy]. rewrite List.filter_app, map_app. reflexivity. Qed.

#[using="rc L s0 n b1 ctx XB WF"] Lemma busy_of_xrec : forall c' k',
  busy_of xrec c' k' = if (c =? c') && (k =? k') then None else busy_of X c' k'.
Proof.
  intros c' k'. rewrite (busy_of_X_g L st X s0 c k n b1 ctx l1 l2 XB WF).
  unfold xrec. rewrite (busy_of_x_cls _ (x_cls X) (l1 ++ l2)).
  destruct ((c =? c') && (k =? k')) eqn:E; [| reflexivity].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' k'.
  unfold busy_of. cbn [x_busy]. destruct (List.find _ (l1 ++ l2)) as [y|] eqn:F; [| reflexivity]. exfalso.
  apply List.find_some in F. destruct F as [Hy T]. apply andb_true_iff in T. destruct T as [T1 T2].
  apply Z.eqb_eq in T1. apply Z.eqb_eq in T2. exact (key_fresh_g L st X s0 c k n b1 ctx l1 l2 XB WF y Hy T1 T2).
Qed.

#[using="rc L s0 n b1 ctx XB WF"] Lemma busy_of_xrec_self : busy_of xrec c k = None.
Proof. rewrite busy_of_xrec, !Z.eqb_refl. reflexivity. Qed.
#[using="rc L s0 n b1 ctx XB WF"] Lemma busy_of_xrec_other : forall c' k', (c <> c' \/ k <> k') -> busy_of xrec c' k' = busy_of X c' k'.
Proof.
  intros c' k' H. rewrite busy_of_xrec. destruct (Z.eqb_spec c c'); destruct (Z.eqb_spec k k'); cbn [andb]; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition rnf' : Z := c_num_freed (get_cls st c) + (if drained then rhalf else 0).
Definition rcnt' : Z := if drained then rcnt - rhalf + 1 else rcnt + 1.

Hypothesis DRC : if drained then rcnt = max_cached c else rcnt < max_cached c.

#[using="rc L s0 k n b1 ctx l1 l2 XB WF DRC"] Lemma rcut_le : drained = true -> (rcut <= length (xc_cache (x_cls X c)))%nat /\ Z.of_nat rcut = rcnt - rhalf.
Proof.
  intros D. (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c rec_class) 11%nat; intros _ _ _ _ _ _ _ _ LENC CNT _; nd_post).
  pose proof (max_cached_range c) as MC. rewrite D in DRC. unfold rcut, rcnt, rhalf in *. split; lia.
Qed.

#[using="rc L s0 n b1 ctx l1 l2 XB WF DRC"] Lemma length_rcache' : Z.of_nat (length rcache') = rcnt'.
Proof.
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c rec_class) 11%nat; intros _ _ _ _ _ _ _ _ LENC CNT _; nd_post).
  pose proof rcut_le as RL. unfold rcache', rcnt'. destruct drained.
  - destruct (RL eq_refl) as [LE EQ]. rewrite length_app, length_firstn. cbn [length]. unfold rcnt in *. lia.
  - rewrite length_app. cbn [length]. unfold rcnt. lia.
Qed.

#[using="rc L s0 k n b1 ctx l1 l2 XB WF DRC"] Lemma length_rfree' : Z.of_nat (length rfree') = rnf'.
Proof.
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c rec_class) 11%nat; intros _ _ _ _ _ _ _ LENF LENC CNT _; nd_post).
  pose proof rcut_le as RL. unfold rfree', rnf'. destruct drained.
  - destruct (RL eq_refl) as [LE EQ]. rewrite length_app, length_skipn. unfold rcnt in *. lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="s0 n b1 ctx XB DRC"] Lemma rec_perm : Permutation (rfree' ++ rcache' ++ busy_slots xrec c)
                             (xc_free (x_cls X c) ++ xc_cache (x_cls X c) ++ busy_slots X c).
Proof.
  rewrite busy_slots_xrec, (busy_slots_split_g X s0 c k n b1 ctx l1 l2 XB), Z.eqb_refl.
  unfold rfree', rcache'. destruct drained.
  - apply firstn_skipn_perm_mid.
  - apply perm_mid_to_front.
Qed.

(* [comment removed for export] *)
#[using="s0 n b1 ctx XB WF NL DRC"] Lemma awf_xrec : forall s mfa',
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = true ->
  a_live s = a_live st -> a_next s = a_next st ->
  (forall c', c' <> c -> get_cls s c' = get_cls st c') ->
  get_cls s c = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) rnf' mfa' rcnt' ->
  4 * rnf' <= mfa' <= K_FREEARR_MAX -> mfa' mod K_FREEARR_MAP = 0 ->
  awf L s xrec.
Proof.
  intros s mfa' E1 E2 E3 E5 E6 GC GCC MFA MFAM.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  pose proof (max_cached_range c) as MCR.
  assert (MC : forall c', max_count s c' = max_cached c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (MCle : forall c', max_count st c' <= max_cached c').
  { intros c'. unfold max_count. pose proof (max_cached_range c'). destruct (a_cinit st); lia. }
  assert (NDc : ndist s c = ndist st c) by (unfold ndist; rewrite GCC; reflexivity).
  assert (NDo : forall c', c' <> c -> ndist s c' = ndist st c') by (intros c' NE; unfold ndist; rewrite (GC c' NE); reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { intros c' HC'. rewrite MC. unfold xrec. cbn [x_cls].
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite GCC, NDc. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count].
      (nd_pre (PERC c rec_class) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [unfold rnf', rhalf; destruct drained; lia|]. split; [exact MFA|]. split; [exact MFAM|].
      split; [exact length_rfree'|]. split; [exact length_rcache'|].
      split; [unfold rcnt', rcnt, rhalf in *; destruct drained; lia|].
      split.
      + eapply Permutation_NoDup'; [apply Permutation_sym; exact rec_perm| exact ND].
      + intros k0 Hk. apply RANGE. eapply Permutation_in; [exact rec_perm| exact Hk].
    - rewrite (GC c' NE), (NDo c' NE), busy_slots_xrec.
      (nd_pre (PERC c' HC') 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
      rewrite (busy_slots_split_g X s0 c k n b1 ctx l1 l2 XB) in ND, RANGE.
      destruct (Z.eqb_spec c c') as [E|_]; [congruence|]. cbn [app] in ND, RANGE.
      repeat (split; [assumption|]). split; [pose proof (MCle c'); lia|]. split; [exact ND| exact RANGE]. }
  split.
  { intros c' HC'. rewrite GC; [exact (OUTC c' HC')|]. intros ->. exact (HC' rec_class). }
  split.
  { intros y Hy. apply In_xrec in Hy. exact (BUSY y ltac:(rewrite XB; apply in_app_iff; apply in_app_iff in Hy; destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy])). }
  split.
  { intros p' c' n' H. (nd_pre (LIVE p' c' n' H) 4%nat; intros y Hy Sy R; nd_post). exists y. split; [| split; [exact Sy| exact R]].
    apply In_xrec. rewrite XB in Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|[E|Hy]]; [left; exact Hy| | right; exact Hy].
    exfalso. subst y. cbn in Sy. exact (NL p' Sy). }
  split; [exact FRESH|].
  intros y1 y2 H1 H2 EQ EX. apply In_xrec in H1. apply In_xrec in H2.
  apply UNIQ; [| | exact EQ| exact EX]; rewrite XB; apply in_app_iff; [apply in_app_iff in H1; destruct H1 as [H1|H1]| apply in_app_iff in H2; destruct H2 as [H2|H2]];
    [left; exact H1| right; right; exact H1| left; exact H2| right; right; exact H2].
Qed.

(* [comment removed for export] *)
#[using="XB"] Lemma xrec_keeps : forall y, In y (x_busy X) -> y <> bany s0 c k n b1 ctx -> In y (x_busy xrec).
Proof.
  intros y Hy NE. apply In_xrec. rewrite XB in Hy. apply in_app_iff in Hy. apply in_app_iff.
  destruct Hy as [Hy|[E|Hy]]; [left; exact Hy| congruence| right; exact Hy].
Qed.
#[using="s0 n b1 ctx XB"] Lemma xrec_sub : forall y, In y (x_busy xrec) -> In y (x_busy X).
Proof.
  intros y Hy. apply In_xrec in Hy. rewrite XB. apply in_app_iff in Hy. apply in_app_iff.
  destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy].
Qed.
#[using="s0 n b1 ctx XB NL"] Lemma xrec_live : forall y p, In y (x_busy X) -> xb_st y = BLive p -> In y (x_busy xrec).
Proof. intros y p Hy Sy. apply xrec_keeps; [exact Hy|]. intros ->. cbn in Sy. exact (NL p Sy). Qed.

#[using="Type"] Lemma xrec_cls_other : forall c', c' <> c -> x_cls xrec c' = x_cls X c'.
Proof. intros c' NE. unfold xrec. cbn [x_cls]. destruct (Z.eqb_spec c' c); [congruence| reflexivity]. Qed.
#[using="Type"] Lemma xrec_cls_self : x_cls xrec c = mkXClass rfree' rcache'.
Proof. unfold xrec. cbn [x_cls]. rewrite Z.eqb_refl. reflexivity. Qed.
End Recyc.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma firstn_skipn_perm_mid : forall {A} (f c : list A) (i : nat) (x : A) (b1 b2 : list A),
  Permutation ((f ++ skipn i c) ++ (firstn i c ++ [x]) ++ (b1 ++ b2)) (f ++ c ++ (b1 ++ [x] ++ b2)).
Proof.
  intros A f c i x b1 b2. rewrite <- !app_assoc. apply Permutation_app_head.
  transitivity (firstn i c ++ skipn i c ++ [x] ++ b1 ++ b2); [apply Permutation_app_swap_app|].
  rewrite (app_assoc (firstn i c) (skipn i c)), firstn_skipn. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

#[using="Type"] Lemma perm_mid_to_front : forall {A} (f c : list A) (x : A) (b1 b2 : list A),
  Permutation (f ++ (c ++ [x]) ++ (b1 ++ b2)) (f ++ c ++ (b1 ++ [x] ++ b2)).
Proof.
  intros A f c x b1 b2. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
Qed.

#[using="Type"] Lemma length_skipn_Z : forall {A} (l : list A) i, (i <= length l)%nat -> Z.of_nat (length (skipn i l)) = Z.of_nat (length l) - Z.of_nat i.
Proof. intros A l i Hi. rewrite length_skipn. lia. Qed.
#[using="Type"] Lemma length_firstn_Z : forall {A} (l : list A) i, (i <= length l)%nat -> Z.of_nat (length (firstn i l)) = Z.of_nat i.
Proof. intros A l i Hi. rewrite length_firstn. lia. Qed.

#[using="Type"] Lemma max_cached_range : forall c, 2 <= max_cached c <= 16 /\ 1 <= max_cached c / 2 <= 8 /\ max_cached c = 2 * (max_cached c / 2).
Proof.
  intros c. unfold max_cached.
  set (q := Z.max 1 (Z.min 8 (1024 / size_of_class c))). assert (1 <= q <= 8) by lia.
  rewrite (Z.mul_comm 2 q), Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Recyc.
Variables (L : alayout) (st : astate) (X : aconc) (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Variable drained : bool.
Hypothesis XB : x_busy X = l1 ++ bany s0 c k n b1 ctx :: l2.
Hypothesis WF : awf L st X.
Hypothesis NL : forall p, s0 <> BLive p.

Definition rcnt : Z := c_count (get_cls st c).
Definition rhalf : Z := max_cached c / 2.
Definition rcut : nat := Z.to_nat (rcnt - rhalf).
(* [comment removed for export] *)
Definition rcache' : list Z :=
  if drained then firstn rcut (xc_cache (x_cls X c)) ++ [k] else xc_cache (x_cls X c) ++ [k].
Definition rfree' : list Z :=
  if drained then xc_free (x_cls X c) ++ skipn rcut (xc_cache (x_cls X c)) else xc_free (x_cls X c).
Definition xrec : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass rfree' rcache' else x_cls X c') (l1 ++ l2).

#[using="rc L st X s0 k n b1 ctx l1 l2 XB WF"] Lemma rec_class : 1 <= c < K_NUM_CLASSES.
Proof. exact (any_class L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

#[using="rc L X s0 n b1 ctx l1 l2 XB WF"] Lemma rec_range : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof. exact (any_range L st X s0 c k n b1 ctx l1 l2 XB WF). Qed.

#[using="Type"] Lemma In_xrec : forall y, In y (x_busy xrec) <-> In y (l1 ++ l2).
Proof. intros y. unfold xrec. cbn [x_busy]. tauto. Qed.

#[using="Type"] Lemma busy_slots_xrec : forall c',
  busy_slots xrec c' = busy_slots (mkAConc (x_cls X) l1) c' ++ busy_slots (mkAConc (x_cls X) l2) c'.
Proof. intros c'. unfold busy_slots, xrec. cbn [x_busy]. rewrite List.filter_app, map_app. reflexivity. Qed.

#[using="rc L s0 n b1 ctx XB WF"] Lemma busy_of_xrec : forall c' k',
  busy_of xrec c' k' = if (c =? c') && (k =? k') then None else busy_of X c' k'.
Proof.
  intros c' k'. rewrite (busy_of_X_g L st X s0 c k n b1 ctx l1 l2 XB WF).
  unfold xrec. rewrite (busy_of_x_cls _ (x_cls X) (l1 ++ l2)).
  destruct ((c =? c') && (k =? k')) eqn:E; [| reflexivity].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' k'.
  unfold busy_of. cbn [x_busy]. destruct (List.find _ (l1 ++ l2)) as [y|] eqn:F; [| reflexivity]. exfalso.
  apply List.find_some in F. destruct F as [Hy T]. apply andb_true_iff in T. destruct T as [T1 T2].
  apply Z.eqb_eq in T1. apply Z.eqb_eq in T2. exact (key_fresh_g L st X s0 c k n b1 ctx l1 l2 XB WF y Hy T1 T2).
Qed.

#[using="rc L s0 n b1 ctx XB WF"] Lemma busy_of_xrec_self : busy_of xrec c k = None.
Proof. rewrite busy_of_xrec, !Z.eqb_refl. reflexivity. Qed.
#[using="rc L s0 n b1 ctx XB WF"] Lemma busy_of_xrec_other : forall c' k', (c <> c' \/ k <> k') -> busy_of xrec c' k' = busy_of X c' k'.
Proof.
  intros c' k' H. rewrite busy_of_xrec. destruct (Z.eqb_spec c c'); destruct (Z.eqb_spec k k'); cbn [andb]; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition rnf' : Z := c_num_freed (get_cls st c) + (if drained then rhalf else 0).
Definition rcnt' : Z := if drained then rcnt - rhalf + 1 else rcnt + 1.

Hypothesis DRC : if drained then rcnt = max_cached c else rcnt < max_cached c.

#[using="rc L s0 k n b1 ctx l1 l2 XB WF DRC"] Lemma rcut_le : drained = true -> (rcut <= length (xc_cache (x_cls X c)))%nat /\ Z.of_nat rcut = rcnt - rhalf.
Proof.
  intros D. (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c rec_class) 11%nat; intros _ _ _ _ _ _ _ _ LENC CNT _; nd_post).
  pose proof (max_cached_range c) as MC. rewrite D in DRC. unfold rcut, rcnt, rhalf in *. split; lia.
Qed.

#[using="rc L s0 n b1 ctx l1 l2 XB WF DRC"] Lemma length_rcache' : Z.of_nat (length rcache') = rcnt'.
Proof.
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c rec_class) 11%nat; intros _ _ _ _ _ _ _ _ LENC CNT _; nd_post).
  pose proof rcut_le as RL. unfold rcache', rcnt'. destruct drained.
  - destruct (RL eq_refl) as [LE EQ]. rewrite length_app, length_firstn. cbn [length]. unfold rcnt in *. lia.
  - rewrite length_app. cbn [length]. unfold rcnt. lia.
Qed.

#[using="rc L s0 k n b1 ctx l1 l2 XB WF DRC"] Lemma length_rfree' : Z.of_nat (length rfree') = rnf'.
Proof.
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c rec_class) 11%nat; intros _ _ _ _ _ _ _ LENF LENC CNT _; nd_post).
  pose proof rcut_le as RL. unfold rfree', rnf'. destruct drained.
  - destruct (RL eq_refl) as [LE EQ]. rewrite length_app, length_skipn. unfold rcnt in *. lia.
  - lia.
Qed.

(* [comment removed for export] *)
#[using="s0 n b1 ctx XB DRC"] Lemma rec_perm : Permutation (rfree' ++ rcache' ++ busy_slots xrec c)
                             (xc_free (x_cls X c) ++ xc_cache (x_cls X c) ++ busy_slots X c).
Proof.
  rewrite busy_slots_xrec, (busy_slots_split_g X s0 c k n b1 ctx l1 l2 XB), Z.eqb_refl.
  unfold rfree', rcache'. destruct drained.
  - apply firstn_skipn_perm_mid.
  - apply perm_mid_to_front.
Qed.

(* [comment removed for export] *)
#[using="s0 n b1 ctx XB WF NL DRC"] Lemma awf_xrec : forall s mfa',
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = true ->
  a_live s = a_live st -> a_next s = a_next st ->
  (forall c', c' <> c -> get_cls s c' = get_cls st c') ->
  get_cls s c = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) rnf' mfa' rcnt' ->
  4 * rnf' <= mfa' <= K_FREEARR_MAX -> mfa' mod K_FREEARR_MAP = 0 ->
  awf L s xrec.
Proof.
  intros s mfa' E1 E2 E3 E5 E6 GC GCC MFA MFAM.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  pose proof (max_cached_range c) as MCR.
  assert (MC : forall c', max_count s c' = max_cached c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (MCle : forall c', max_count st c' <= max_cached c').
  { intros c'. unfold max_count. pose proof (max_cached_range c'). destruct (a_cinit st); lia. }
  assert (NDc : ndist s c = ndist st c) by (unfold ndist; rewrite GCC; reflexivity).
  assert (NDo : forall c', c' <> c -> ndist s c' = ndist st c') by (intros c' NE; unfold ndist; rewrite (GC c' NE); reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { intros c' HC'. rewrite MC. unfold xrec. cbn [x_cls].
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite GCC, NDc. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count].
      (nd_pre (PERC c rec_class) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
      split; [unfold rnf', rhalf; destruct drained; lia|]. split; [exact MFA|]. split; [exact MFAM|].
      split; [exact length_rfree'|]. split; [exact length_rcache'|].
      split; [unfold rcnt', rcnt, rhalf in *; destruct drained; lia|].
      split.
      + eapply Permutation_NoDup'; [apply Permutation_sym; exact rec_perm| exact ND].
      + intros k0 Hk. apply RANGE. eapply Permutation_in; [exact rec_perm| exact Hk].
    - rewrite (GC c' NE), (NDo c' NE), busy_slots_xrec.
      (nd_pre (PERC c' HC') 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
      rewrite (busy_slots_split_g X s0 c k n b1 ctx l1 l2 XB) in ND, RANGE.
      destruct (Z.eqb_spec c c') as [E|_]; [congruence|]. cbn [app] in ND, RANGE.
      repeat (split; [assumption|]). split; [pose proof (MCle c'); lia|]. split; [exact ND| exact RANGE]. }
  split.
  { intros c' HC'. rewrite GC; [exact (OUTC c' HC')|]. intros ->. exact (HC' rec_class). }
  split.
  { intros y Hy. apply In_xrec in Hy. exact (BUSY y ltac:(rewrite XB; apply in_app_iff; apply in_app_iff in Hy; destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy])). }
  split.
  { intros p' c' n' H. (nd_pre (LIVE p' c' n' H) 4%nat; intros y Hy Sy R; nd_post). exists y. split; [| split; [exact Sy| exact R]].
    apply In_xrec. rewrite XB in Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|[E|Hy]]; [left; exact Hy| | right; exact Hy].
    exfalso. subst y. cbn in Sy. exact (NL p' Sy). }
  split; [exact FRESH|].
  intros y1 y2 H1 H2 EQ EX. apply In_xrec in H1. apply In_xrec in H2.
  apply UNIQ; [| | exact EQ| exact EX]; rewrite XB; apply in_app_iff; [apply in_app_iff in H1; destruct H1 as [H1|H1]| apply in_app_iff in H2; destruct H2 as [H2|H2]];
    [left; exact H1| right; right; exact H1| left; exact H2| right; right; exact H2].
Qed.

(* [comment removed for export] *)
#[using="XB"] Lemma xrec_keeps : forall y, In y (x_busy X) -> y <> bany s0 c k n b1 ctx -> In y (x_busy xrec).
Proof.
  intros y Hy NE. apply In_xrec. rewrite XB in Hy. apply in_app_iff in Hy. apply in_app_iff.
  destruct Hy as [Hy|[E|Hy]]; [left; exact Hy| congruence| right; exact Hy].
Qed.
#[using="s0 n b1 ctx XB"] Lemma xrec_sub : forall y, In y (x_busy xrec) -> In y (x_busy X).
Proof.
  intros y Hy. apply In_xrec in Hy. rewrite XB. apply in_app_iff in Hy. apply in_app_iff.
  destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy].
Qed.
#[using="s0 n b1 ctx XB NL"] Lemma xrec_live : forall y p, In y (x_busy X) -> xb_st y = BLive p -> In y (x_busy xrec).
Proof. intros y p Hy Sy. apply xrec_keeps; [exact Hy|]. intros ->. cbn in Sy. exact (NL p Sy). Qed.

#[using="Type"] Lemma xrec_cls_other : forall c', c' <> c -> x_cls xrec c' = x_cls X c'.
Proof. intros c' NE. unfold xrec. cbn [x_cls]. destruct (Z.eqb_spec c' c); [congruence| reflexivity]. Qed.
#[using="Type"] Lemma xrec_cls_self : x_cls xrec c = mkXClass rfree' rcache'.
Proof. unfold xrec. cbn [x_cls]. rewrite Z.eqb_refl. reflexivity. Qed.
End Recyc.
End CANSEC1.
End TwB.
End ARecRep.

(* [comment removed for export] *)
Module ARepQD.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition qnumR (st : astate) : Prop :=
     a_qloc_bytes st = batches_bytes (a_qloc st) /\ a_qglob_bytes st = batches_bytes (a_qglob st)
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st ++ a_qglob st).

#[using="Type"] Lemma qnumR_of_qnum : forall st, qnum st -> qnumR st.
Proof. intros st (A & B & C & _). exact (conj A (conj B C)). Qed.

Definition AQdr (R : qrconc) (mc mr : Z) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ abatches L m (map fst (qr_tmp R)) (map snd (qr_tmp R))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnumR st /\ qnum_tmp (map fst (qr_tmp R)).

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_bslot_busy : forall L st X R kk,
  qcoupled_rec L st X R -> In kk (qr_bslots R) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = kk.
Proof. intros L st X R kk (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS kk)). exact Hin. Qed.

#[using="Type"] Lemma In_qr_bslots : forall R q,
  In q (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) -> In (qb_slot q) (qr_bslots R).
Proof. intros R q H. unfold qr_bslots. apply in_app_iff. left. apply in_map. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FrameD0.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
(* [comment removed for export] *)
#[using="MU"] Lemma qd_abatch_cells_frameD : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frameD; [exact H1 | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frameD; [exact H2 | exact MU |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frameD; [exact H3 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.
#[using="MU"] Lemma qd_abatches_to_frameD : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply qd_abatch_cells_frameD; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
#[using="MU"] Lemma qd_abatches_frameD : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply qd_abatches_to_frameD; eassumption. Qed.
#[using="MU"] Lemma qd_aqcache_frameD : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frameD; [exact QC | exact MU | exact D].
  - eapply qd_abatches_frameD; [exact AB | exact DB].
Qed.
#[using="MU"] Lemma qd_aintal_frameD : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frameD; [exact F | exact MU | exact DF].
  - eapply stk_transportD; [exact S | exact MU |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.
End FrameD0.

Section FrameD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem) (X : aconc).
Hypothesis MU : munch W m m'.
Hypothesis UT : quar_untouched L X W.

#[using="X UT"] Lemma qut_tcache : disjoint_from W (aq_tcache L) 32.
Proof. apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. Qed.
#[using="L X UT"] Lemma qut_glob : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32.
Proof.
  unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
  repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia.
Qed.
#[using="L X UT"] Lemma qut_ia : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE.
Proof.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
  split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia.
Qed.
#[using="UT"] Lemma qut_bslot : forall st R q, qcoupled_rec L st X R ->
  In q (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES.
Proof.
  intros st R q CP Hq. (nd_pre (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP (In_qr_bslots R q Hq)) 5%nat; intros b Hb Sb Cb Kb; nd_post).
  apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
  specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
  unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A.
Qed.

#[using="L W X MU UT"] Lemma aquar_consts_frameD : aquar_consts m -> aquar_consts m'.
Proof. intros A. destruct qut_glob as (D1 & _). eapply cells_frameD; [exact A | exact MU | exact D1]. Qed.
#[using="L W X MU UT"] Lemma aquar_mutex_frameD : forall mc mr, aquar_mutex m mc mr -> aquar_mutex m' mc mr.
Proof. intros mc mr A. (nd_pre qut_glob 3%nat; intros _ D2 _; nd_post). eapply cells_frameD; [exact A | exact MU | exact D2]. Qed.
End FrameD.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_same : forall L st st' X X' R,
  qcoupled_rec L st X R -> quar_same st st' X X' -> qcoupled_rec L st' X' R.
Proof.
  intros L st st' X X' R (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold qcoupled_rec, qr_entries in *. cbv zeta. rewrite E1, E3.
  split; [exact LN1|]. split; [exact LN2|]. split.
  { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c n | mb ms n]; [| exact I]. (nd_pre HOK 3%nat; intros b1 ctx Hin; nd_post). exists b1, ctx.
    specialize (FW _ Hin). cbn in FW. exact FW. }
  split; [exact ND1|]. split; [exact ND2|]. split.
  { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R'); exists b; (split; [| split; [exact Sb| exact R']]).
    - specialize (FW b Hb). rewrite Sb in FW. exact FW.
    - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
  split; [| exact NN].
  intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R'); exists b; (split; [| split; [exact Sb| exact R']]).
  + specialize (FW b Hb). rewrite Sb in FW. exact FW.
  + specialize (BW b Hb). rewrite Sb in BW. exact BW.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem AQdr_frameD : forall R mc mr L st st' X X' m m' W,
  AQdr R mc mr L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQdr R mc mr L st' X' m'.
Proof.
  intros R mc mr L st st' X X' m m' W (QC & MX & TC & GL & TB & IA & CP & NUM & NT) MU UT QS.
  (pose proof QS as ndP__; nd_pre ndP__ 5%nat; intros E1 E2 E3 E4 _; nd_post).
  unfold AQdr. rewrite E1, E2, E3, E4.
  (nd_pre (qut_glob L W X UT) 3%nat; intros DG1 DG2 DG3; nd_post). destruct (qut_ia L W X UT) as [DF DB].
  split; [eapply aquar_consts_frameD; eassumption|]. split; [eapply aquar_mutex_frameD; eassumption|].
  split. { eapply qd_aqcache_frameD; [exact MU | exact TC | exact (qut_tcache L W X UT) |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. left. exact Hq. }
  split. { eapply qd_aqcache_frameD; [exact MU | exact GL | exact DG3 |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. right. apply in_app_iff. left. exact Hq. }
  split. { eapply qd_abatches_frameD; [exact MU | exact TB |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. right. apply in_app_iff. right. exact Hq. }
  split; [eapply qd_aintal_frameD; eassumption|].
  split; [eapply qcoupled_rec_same; eassumption|].
  split; [| exact NT]. unfold qnumR in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem AQdr_frame : forall R mc mr L st st' X X' m m' W,
  AQdr R mc mr L st X m -> munch W m m' -> wmono asegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQdr R mc mr L st' X' m'.
Proof. intros. eapply AQdr_frameD; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma qprim_ids_app' : forall es1 es2, qprim_ids (es1 ++ es2) = qprim_ids es1 ++ qprim_ids es2.
Proof. intros. unfold qprim_ids. rewrite flat_map_app. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_perm : forall L st st' X R R',
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  Permutation (qr_entries st' R') (qr_entries st R) ->
  Permutation (qr_bslots R') (qr_bslots R) ->
  qr_qpend R' = qr_qpend R ->
  qcoupled_rec L st' X R'.
Proof.
  intros L st st' X R R' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB EQP.
  unfold qcoupled_rec. cbv zeta. rewrite EQP.
  assert (PE' : Permutation (qprim_ids (qr_entries st' R') ++ qr_qpend R) (qprim_ids (qr_entries st R) ++ qr_qpend R)).
  { apply Permutation_app_tail. apply qprim_ids_perm. exact PE. }
  split; [exact L1|]. split; [exact L2|].
  split; [eapply Permutation_Forall; [apply Permutation_sym; exact PE| exact OK]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PE'| exact ND1]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PB| exact ND2]|].
  split.
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PB| apply Permutation_sym; exact PB]. }
  split.
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PE'| apply Permutation_sym; exact PE']. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB| exact NN].
Qed.

(* [comment removed for export] *)
Definition qr_pop (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (combine (b_chunks b) (qb_ks q)) (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_pop : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_pop R b q T).
Proof.
  intros L st X R b q T CP ET EB EP. (pose proof CP as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_perm; [exact CP| exact LN1| exact LN2| | | reflexivity].
  - unfold qr_entries, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite ET, EP. cbn [map fst snd qentries]. rewrite app_nil_r.
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
  - unfold qr_bslots, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map snd qb_slot]. rewrite app_nil_r.
    rewrite !map_app. cbn [map]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
Definition qr_drop (R : qrconc) (pend' : list (achunk * Z)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) (qr_tmp R) (qr_pendb R) pend' (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_drop_sec : forall L st X R mb ms n kk pend',
  qcoupled_rec L st X R -> qr_pend R = (CSec mb ms n, kk) :: pend' ->
  qcoupled_rec L st X (qr_drop R pend').
Proof.
  intros L st X R mb ms n kk pend' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) EP.
  unfold qcoupled_rec, qr_entries, qr_bslots, qr_drop in *. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend] in *.
  rewrite EP in OK, ND1, PS.
  assert (EQ : forall es, qprim_ids (es ++ (CSec mb ms n, kk) :: pend') = qprim_ids (es ++ pend')).
  { intros es. rewrite !qprim_ids_app'. cbn [qprim_ids flat_map fst app]. reflexivity. }
  rewrite !app_assoc in OK, ND1, PS |- *. rewrite EQ in ND1, PS.
  split; [exact LN1|]. split; [exact LN2|]. split.
  { apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) OK). revert He. rewrite !in_app_iff. cbn [In]. tauto. }
  split; [exact ND1|]. split; [exact ND2|]. split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_remove_entry : forall L st st' X R R' c k n b1 ctx l1 l2 drained,
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  Permutation (qr_entries st R) ((CPrim c n, k) :: qr_entries st' R') ->
  qr_bslots R' = qr_bslots R -> qr_qpend R' = qr_qpend R ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  qcoupled_rec L st' (xrec st X c k l1 l2 drained) R'.
Proof.
  intros L st st' X R R' c k n b1 ctx l1 l2 drained (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE EB EQP XB WF.
  unfold qcoupled_rec in *. cbv zeta in *. rewrite EB, EQP.
  set (es := qr_entries st R) in *. set (es' := qr_entries st' R') in *. set (qp := qr_qpend R) in *.
  assert (OK' : Forall (qentry_ok X) ((CPrim c n, k) :: es')) by (eapply Permutation_Forall; [exact PE| exact OK]).
  assert (PP : Permutation (qprim_ids es ++ qp) ((c, k) :: qprim_ids es' ++ qp)).
  { pose proof (Permutation_app_tail qp (qprim_ids_perm _ _ PE)) as H. cbn [qprim_ids flat_map fst snd app] in H. exact H. }
  assert (ND1c : List.NoDup ((c, k) :: qprim_ids es' ++ qp)) by exact (Permutation_NoDup' _ _ PP ND1).
  apply List.NoDup_cons_iff in ND1c. destruct ND1c as [NI ND1'].
  assert (PSc : forall c0 k0, In (c0, k0) ((c, k) :: qprim_ids es' ++ qp) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c0 /\ xb_slot b = k0).
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact PP| exact PP]. }
  assert (XIN : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany BQuar c k n b1 ctx).
  { intros y. rewrite XB, !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. }
  split; [exact L1|]. split; [exact L2|]. split.
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) OK' e (or_intror He)) as HOK.
    unfold qentry_ok in *. destruct e as [ch kk]. cbn [fst snd] in *. destruct ch as [c' n'| mb ms n']; [| exact I].
    (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'. apply In_xrec. destruct (proj1 (XIN _) Hin) as [H|E]; [exact H|]. exfalso.
    unfold bany in E. injection E as Ec Ek En Eb Ex. subst c' kk. apply NI. apply in_app_iff. left. apply (proj2 (qprim_ids_In _ c k)). exists n'. exact He. }
  split; [exact ND1'|]. split; [exact ND2|]. split.
  { intros k0. rewrite (BS k0). split; intros (b & Hb & Sb & Cb & Kb); exists b; (split; [| auto]).
    - apply In_xrec. destruct (proj1 (XIN _) Hb) as [H| ->]; [exact H| cbn in Sb; discriminate].
    - apply (proj2 (XIN _)). left. apply In_xrec in Hb. exact Hb. }
  split; [| exact NN].
  intros c0 k0. split.
  - intros H. (nd_pre (proj1 (PSc c0 k0) (or_intror H)) 5%nat; intros b Hb Sb Cb Kb; nd_post). exists b. split; [| auto].
    apply In_xrec. destruct (proj1 (XIN _) Hb) as [Hl| ->]; [exact Hl|]. exfalso. cbn in Cb, Kb. rewrite <- Cb, <- Kb in H. exact (NI H).
  - intros (b & Hb & Sb & Cb & Kb). apply In_xrec in Hb.
    destruct (proj2 (PSc c0 k0) (ex_intro _ b (conj (proj2 (XIN _) (or_introl Hb)) (conj Sb (conj Cb Kb))))) as [E|H]; [| exact H].
    exfalso. injection E as Ec Ek. rewrite <- Ec in Cb. rewrite <- Ek in Kb. exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb Cb Kb).
Qed.

#[using="Type"] Lemma qcoupled_rec_drop_prim : forall L st st' X R c k n b1 ctx l1 l2 drained pend',
  qcoupled_rec L st X R -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  qcoupled_rec L st' (xrec st X c k l1 l2 drained) (qr_drop R pend').
Proof.
  intros L st st' X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF EL EG. (pose proof CP as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_remove_entry; [exact CP| rewrite EL; exact LN1| rewrite EG; exact LN2| | reflexivity| reflexivity| exact XB| exact WF].
  unfold qr_entries, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite EL, EG, EP.
  rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_remove_bslot : forall L st st' X R R' kb nb b1 ctx l1 l2 drained,
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  qr_entries st' R' = qr_entries st R ->
  Permutation (qr_bslots R) (kb :: qr_bslots R') -> qr_qpend R' = qr_qpend R ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  qcoupled_rec L st' (xrec st X K_BATCH_CLASS kb l1 l2 drained) R'.
Proof.
  intros L st st' X R R' kb nb b1 ctx l1 l2 drained (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 EE PB EQP XB WF.
  unfold qcoupled_rec in *. cbv zeta in *. rewrite EE, EQP.
  set (es := qr_entries st R) in *.
  pose proof (Permutation_NoDup' _ _ PB ND2) as ND2c. apply List.NoDup_cons_iff in ND2c. destruct ND2c as [NI ND2'].
  assert (BSc : forall k0, In k0 (kb :: qr_bslots R') <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k0).
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact PB| exact PB]. }
  assert (XIN : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany BBatch K_BATCH_CLASS kb nb b1 ctx).
  { intros y. rewrite XB, !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. }
  split; [exact L1|]. split; [exact L2|]. split.
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) OK e He) as HOK.
    unfold qentry_ok in *. destruct e as [ch kk]. cbn [fst snd] in *. destruct ch as [c' n'| mb ms n']; [| exact I].
    (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'. apply In_xrec. destruct (proj1 (XIN _) Hin) as [H|E]; [exact H| discriminate]. }
  split; [exact ND1|]. split; [exact ND2'|]. split.
  { intros k0. split.
    - intros H. (nd_pre (proj1 (BSc k0) (or_intror H)) 5%nat; intros b Hb Sb Cb Kb; nd_post). exists b. split; [| auto].
      apply In_xrec. destruct (proj1 (XIN _) Hb) as [Hl| ->]; [exact Hl|]. exfalso. cbn in Kb. rewrite <- Kb in H. exact (NI H).
    - intros (b & Hb & Sb & Cb & Kb). apply In_xrec in Hb.
      destruct (proj2 (BSc k0) (ex_intro _ b (conj (proj2 (XIN _) (or_introl Hb)) (conj Sb (conj Cb Kb))))) as [E|H]; [| exact H].
      exfalso. rewrite <- E in Kb. exact (key_fresh_g L st X BBatch K_BATCH_CLASS kb nb b1 ctx l1 l2 XB WF b Hb Cb Kb). }
  split.
  { intros c0 k0. rewrite (PS c0 k0). split; intros (b & Hb & Sb & Cb & Kb); exists b; (split; [| auto]).
    - apply In_xrec. destruct (proj1 (XIN _) Hb) as [H| ->]; [exact H| cbn in Sb; discriminate].
    - apply (proj2 (XIN _)). left. apply In_xrec in Hb. exact Hb. }
  exact (Forall_inv_tail (Permutation_Forall PB NN)).
Qed.

(* [comment removed for export] *)
Definition qr_unbatch (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) (qr_tmp R) [] [] (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_unbatch : forall L st st' X R kb nb b1 ctx l1 l2 drained,
  qcoupled_rec L st X R -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  qcoupled_rec L st' (xrec st X K_BATCH_CLASS kb l1 l2 drained) (qr_unbatch R).
Proof.
  intros L st st' X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF EL EG. (pose proof CP as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_remove_bslot; [exact CP| rewrite EL; exact LN1| rewrite EG; exact LN2| | | reflexivity| exact XB| exact WF].
  - unfold qr_entries, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite EL, EG, EP. reflexivity.
  - unfold qr_bslots, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite EB, app_nil_r. apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_at_of_dr : forall L st X R m,
  AQdr R 0 0 L st X m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3 B1 B2.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split.
  - (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
    unfold qcoupled. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
  - (nd_pre NUM 3%nat; intros N1 N2 N3; nd_post). exact (conj N1 (conj N2 (conj N3 (conj B1 B2)))).
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition qnumR (st : astate) : Prop :=
     a_qloc_bytes st = batches_bytes (a_qloc st) /\ a_qglob_bytes st = batches_bytes (a_qglob st)
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st ++ a_qglob st).

#[using="Type"] Lemma qnumR_of_qnum : forall st, qnum st -> qnumR st.
Proof. intros st (A & B & C & _). exact (conj A (conj B C)). Qed.

Definition AQdr (R : qrconc) (mc mr : Z) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ abatches L m (map fst (qr_tmp R)) (map snd (qr_tmp R))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnumR st /\ qnum_tmp (map fst (qr_tmp R)).

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_bslot_busy : forall L st X R kk,
  qcoupled_rec L st X R -> In kk (qr_bslots R) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = kk.
Proof. intros L st X R kk (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS kk)). exact Hin. Qed.

#[using="Type"] Lemma In_qr_bslots : forall R q,
  In q (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) -> In (qb_slot q) (qr_bslots R).
Proof. intros R q H. unfold qr_bslots. apply in_app_iff. left. apply in_map. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FrameD0.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
(* [comment removed for export] *)
#[using="MU"] Lemma qd_abatch_cells_frameD : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frameD; [exact H1 | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frameD; [exact H2 | exact MU |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frameD; [exact H3 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.
#[using="MU"] Lemma qd_abatches_to_frameD : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply qd_abatch_cells_frameD; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
#[using="MU"] Lemma qd_abatches_frameD : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply qd_abatches_to_frameD; eassumption. Qed.
#[using="MU"] Lemma qd_aqcache_frameD : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frameD; [exact QC | exact MU | exact D].
  - eapply qd_abatches_frameD; [exact AB | exact DB].
Qed.
#[using="MU"] Lemma qd_aintal_frameD : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frameD; [exact F | exact MU | exact DF].
  - eapply stk_transportD; [exact S | exact MU |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.
End FrameD0.

Section FrameD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem) (X : aconc).
Hypothesis MU : munch W m m'.
Hypothesis UT : quar_untouched L X W.

#[using="X UT"] Lemma qut_tcache : disjoint_from W (aq_tcache L) 32.
Proof. apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. Qed.
#[using="L X UT"] Lemma qut_glob : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32.
Proof.
  unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
  repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia.
Qed.
#[using="L X UT"] Lemma qut_ia : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE.
Proof.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
  split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia.
Qed.
#[using="UT"] Lemma qut_bslot : forall st R q, qcoupled_rec L st X R ->
  In q (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES.
Proof.
  intros st R q CP Hq. (nd_pre (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP (In_qr_bslots R q Hq)) 5%nat; intros b Hb Sb Cb Kb; nd_post).
  apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
  specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
  unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A.
Qed.

#[using="L W X MU UT"] Lemma aquar_consts_frameD : aquar_consts m -> aquar_consts m'.
Proof. intros A. destruct qut_glob as (D1 & _). eapply cells_frameD; [exact A | exact MU | exact D1]. Qed.
#[using="L W X MU UT"] Lemma aquar_mutex_frameD : forall mc mr, aquar_mutex m mc mr -> aquar_mutex m' mc mr.
Proof. intros mc mr A. (nd_pre qut_glob 3%nat; intros _ D2 _; nd_post). eapply cells_frameD; [exact A | exact MU | exact D2]. Qed.
End FrameD.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_same : forall L st st' X X' R,
  qcoupled_rec L st X R -> quar_same st st' X X' -> qcoupled_rec L st' X' R.
Proof.
  intros L st st' X X' R (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold qcoupled_rec, qr_entries in *. cbv zeta. rewrite E1, E3.
  split; [exact LN1|]. split; [exact LN2|]. split.
  { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c n | mb ms n]; [| exact I]. (nd_pre HOK 3%nat; intros b1 ctx Hin; nd_post). exists b1, ctx.
    specialize (FW _ Hin). cbn in FW. exact FW. }
  split; [exact ND1|]. split; [exact ND2|]. split.
  { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R'); exists b; (split; [| split; [exact Sb| exact R']]).
    - specialize (FW b Hb). rewrite Sb in FW. exact FW.
    - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
  split; [| exact NN].
  intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R'); exists b; (split; [| split; [exact Sb| exact R']]).
  + specialize (FW b Hb). rewrite Sb in FW. exact FW.
  + specialize (BW b Hb). rewrite Sb in BW. exact BW.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem AQdr_frameD : forall R mc mr L st st' X X' m m' W,
  AQdr R mc mr L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQdr R mc mr L st' X' m'.
Proof.
  intros R mc mr L st st' X X' m m' W (QC & MX & TC & GL & TB & IA & CP & NUM & NT) MU UT QS.
  (pose proof QS as ndP__; nd_pre ndP__ 5%nat; intros E1 E2 E3 E4 _; nd_post).
  unfold AQdr. rewrite E1, E2, E3, E4.
  (nd_pre (qut_glob L W X UT) 3%nat; intros DG1 DG2 DG3; nd_post). destruct (qut_ia L W X UT) as [DF DB].
  split; [eapply aquar_consts_frameD; eassumption|]. split; [eapply aquar_mutex_frameD; eassumption|].
  split. { eapply qd_aqcache_frameD; [exact MU | exact TC | exact (qut_tcache L W X UT) |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. left. exact Hq. }
  split. { eapply qd_aqcache_frameD; [exact MU | exact GL | exact DG3 |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. right. apply in_app_iff. left. exact Hq. }
  split. { eapply qd_abatches_frameD; [exact MU | exact TB |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. right. apply in_app_iff. right. exact Hq. }
  split; [eapply qd_aintal_frameD; eassumption|].
  split; [eapply qcoupled_rec_same; eassumption|].
  split; [| exact NT]. unfold qnumR in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem AQdr_frame : forall R mc mr L st st' X X' m m' W,
  AQdr R mc mr L st X m -> munch W m m' -> wmono asegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQdr R mc mr L st' X' m'.
Proof. intros. eapply AQdr_frameD; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma qprim_ids_app' : forall es1 es2, qprim_ids (es1 ++ es2) = qprim_ids es1 ++ qprim_ids es2.
Proof. intros. unfold qprim_ids. rewrite flat_map_app. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_perm : forall L st st' X R R',
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  Permutation (qr_entries st' R') (qr_entries st R) ->
  Permutation (qr_bslots R') (qr_bslots R) ->
  qr_qpend R' = qr_qpend R ->
  qcoupled_rec L st' X R'.
Proof.
  intros L st st' X R R' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB EQP.
  unfold qcoupled_rec. cbv zeta. rewrite EQP.
  assert (PE' : Permutation (qprim_ids (qr_entries st' R') ++ qr_qpend R) (qprim_ids (qr_entries st R) ++ qr_qpend R)).
  { apply Permutation_app_tail. apply qprim_ids_perm. exact PE. }
  split; [exact L1|]. split; [exact L2|].
  split; [eapply Permutation_Forall; [apply Permutation_sym; exact PE| exact OK]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PE'| exact ND1]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PB| exact ND2]|].
  split.
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PB| apply Permutation_sym; exact PB]. }
  split.
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PE'| apply Permutation_sym; exact PE']. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB| exact NN].
Qed.

(* [comment removed for export] *)
Definition qr_pop (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (combine (b_chunks b) (qb_ks q)) (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_pop : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_pop R b q T).
Proof.
  intros L st X R b q T CP ET EB EP. (pose proof CP as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_perm; [exact CP| exact LN1| exact LN2| | | reflexivity].
  - unfold qr_entries, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite ET, EP. cbn [map fst snd qentries]. rewrite app_nil_r.
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
  - unfold qr_bslots, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map snd qb_slot]. rewrite app_nil_r.
    rewrite !map_app. cbn [map]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
Definition qr_drop (R : qrconc) (pend' : list (achunk * Z)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) (qr_tmp R) (qr_pendb R) pend' (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_drop_sec : forall L st X R mb ms n kk pend',
  qcoupled_rec L st X R -> qr_pend R = (CSec mb ms n, kk) :: pend' ->
  qcoupled_rec L st X (qr_drop R pend').
Proof.
  intros L st X R mb ms n kk pend' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) EP.
  unfold qcoupled_rec, qr_entries, qr_bslots, qr_drop in *. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend] in *.
  rewrite EP in OK, ND1, PS.
  assert (EQ : forall es, qprim_ids (es ++ (CSec mb ms n, kk) :: pend') = qprim_ids (es ++ pend')).
  { intros es. rewrite !qprim_ids_app'. cbn [qprim_ids flat_map fst app]. reflexivity. }
  rewrite !app_assoc in OK, ND1, PS |- *. rewrite EQ in ND1, PS.
  split; [exact LN1|]. split; [exact LN2|]. split.
  { apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) OK). revert He. rewrite !in_app_iff. cbn [In]. tauto. }
  split; [exact ND1|]. split; [exact ND2|]. split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_remove_entry : forall L st st' X R R' c k n b1 ctx l1 l2 drained,
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  Permutation (qr_entries st R) ((CPrim c n, k) :: qr_entries st' R') ->
  qr_bslots R' = qr_bslots R -> qr_qpend R' = qr_qpend R ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  qcoupled_rec L st' (xrec st X c k l1 l2 drained) R'.
Proof.
  intros L st st' X R R' c k n b1 ctx l1 l2 drained (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE EB EQP XB WF.
  unfold qcoupled_rec in *. cbv zeta in *. rewrite EB, EQP.
  set (es := qr_entries st R) in *. set (es' := qr_entries st' R') in *. set (qp := qr_qpend R) in *.
  assert (OK' : Forall (qentry_ok X) ((CPrim c n, k) :: es')) by (eapply Permutation_Forall; [exact PE| exact OK]).
  assert (PP : Permutation (qprim_ids es ++ qp) ((c, k) :: qprim_ids es' ++ qp)).
  { pose proof (Permutation_app_tail qp (qprim_ids_perm _ _ PE)) as H. cbn [qprim_ids flat_map fst snd app] in H. exact H. }
  assert (ND1c : List.NoDup ((c, k) :: qprim_ids es' ++ qp)) by exact (Permutation_NoDup' _ _ PP ND1).
  apply List.NoDup_cons_iff in ND1c. destruct ND1c as [NI ND1'].
  assert (PSc : forall c0 k0, In (c0, k0) ((c, k) :: qprim_ids es' ++ qp) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c0 /\ xb_slot b = k0).
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact PP| exact PP]. }
  assert (XIN : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany BQuar c k n b1 ctx).
  { intros y. rewrite XB, !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. }
  split; [exact L1|]. split; [exact L2|]. split.
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) OK' e (or_intror He)) as HOK.
    unfold qentry_ok in *. destruct e as [ch kk]. cbn [fst snd] in *. destruct ch as [c' n'| mb ms n']; [| exact I].
    (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'. apply In_xrec. destruct (proj1 (XIN _) Hin) as [H|E]; [exact H|]. exfalso.
    unfold bany in E. injection E as Ec Ek En Eb Ex. subst c' kk. apply NI. apply in_app_iff. left. apply (proj2 (qprim_ids_In _ c k)). exists n'. exact He. }
  split; [exact ND1'|]. split; [exact ND2|]. split.
  { intros k0. rewrite (BS k0). split; intros (b & Hb & Sb & Cb & Kb); exists b; (split; [| auto]).
    - apply In_xrec. destruct (proj1 (XIN _) Hb) as [H| ->]; [exact H| cbn in Sb; discriminate].
    - apply (proj2 (XIN _)). left. apply In_xrec in Hb. exact Hb. }
  split; [| exact NN].
  intros c0 k0. split.
  - intros H. (nd_pre (proj1 (PSc c0 k0) (or_intror H)) 5%nat; intros b Hb Sb Cb Kb; nd_post). exists b. split; [| auto].
    apply In_xrec. destruct (proj1 (XIN _) Hb) as [Hl| ->]; [exact Hl|]. exfalso. cbn in Cb, Kb. rewrite <- Cb, <- Kb in H. exact (NI H).
  - intros (b & Hb & Sb & Cb & Kb). apply In_xrec in Hb.
    destruct (proj2 (PSc c0 k0) (ex_intro _ b (conj (proj2 (XIN _) (or_introl Hb)) (conj Sb (conj Cb Kb))))) as [E|H]; [| exact H].
    exfalso. injection E as Ec Ek. rewrite <- Ec in Cb. rewrite <- Ek in Kb. exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb Cb Kb).
Qed.

#[using="Type"] Lemma qcoupled_rec_drop_prim : forall L st st' X R c k n b1 ctx l1 l2 drained pend',
  qcoupled_rec L st X R -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  qcoupled_rec L st' (xrec st X c k l1 l2 drained) (qr_drop R pend').
Proof.
  intros L st st' X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF EL EG. (pose proof CP as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_remove_entry; [exact CP| rewrite EL; exact LN1| rewrite EG; exact LN2| | reflexivity| reflexivity| exact XB| exact WF].
  unfold qr_entries, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite EL, EG, EP.
  rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_rec_remove_bslot : forall L st st' X R R' kb nb b1 ctx l1 l2 drained,
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  qr_entries st' R' = qr_entries st R ->
  Permutation (qr_bslots R) (kb :: qr_bslots R') -> qr_qpend R' = qr_qpend R ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  qcoupled_rec L st' (xrec st X K_BATCH_CLASS kb l1 l2 drained) R'.
Proof.
  intros L st st' X R R' kb nb b1 ctx l1 l2 drained (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 EE PB EQP XB WF.
  unfold qcoupled_rec in *. cbv zeta in *. rewrite EE, EQP.
  set (es := qr_entries st R) in *.
  pose proof (Permutation_NoDup' _ _ PB ND2) as ND2c. apply List.NoDup_cons_iff in ND2c. destruct ND2c as [NI ND2'].
  assert (BSc : forall k0, In k0 (kb :: qr_bslots R') <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k0).
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact PB| exact PB]. }
  assert (XIN : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany BBatch K_BATCH_CLASS kb nb b1 ctx).
  { intros y. rewrite XB, !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. }
  split; [exact L1|]. split; [exact L2|]. split.
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) OK e He) as HOK.
    unfold qentry_ok in *. destruct e as [ch kk]. cbn [fst snd] in *. destruct ch as [c' n'| mb ms n']; [| exact I].
    (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'. apply In_xrec. destruct (proj1 (XIN _) Hin) as [H|E]; [exact H| discriminate]. }
  split; [exact ND1|]. split; [exact ND2'|]. split.
  { intros k0. split.
    - intros H. (nd_pre (proj1 (BSc k0) (or_intror H)) 5%nat; intros b Hb Sb Cb Kb; nd_post). exists b. split; [| auto].
      apply In_xrec. destruct (proj1 (XIN _) Hb) as [Hl| ->]; [exact Hl|]. exfalso. cbn in Kb. rewrite <- Kb in H. exact (NI H).
    - intros (b & Hb & Sb & Cb & Kb). apply In_xrec in Hb.
      destruct (proj2 (BSc k0) (ex_intro _ b (conj (proj2 (XIN _) (or_introl Hb)) (conj Sb (conj Cb Kb))))) as [E|H]; [| exact H].
      exfalso. rewrite <- E in Kb. exact (key_fresh_g L st X BBatch K_BATCH_CLASS kb nb b1 ctx l1 l2 XB WF b Hb Cb Kb). }
  split.
  { intros c0 k0. rewrite (PS c0 k0). split; intros (b & Hb & Sb & Cb & Kb); exists b; (split; [| auto]).
    - apply In_xrec. destruct (proj1 (XIN _) Hb) as [H| ->]; [exact H| cbn in Sb; discriminate].
    - apply (proj2 (XIN _)). left. apply In_xrec in Hb. exact Hb. }
  exact (Forall_inv_tail (Permutation_Forall PB NN)).
Qed.

(* [comment removed for export] *)
Definition qr_unbatch (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) (qr_tmp R) [] [] (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_unbatch : forall L st st' X R kb nb b1 ctx l1 l2 drained,
  qcoupled_rec L st X R -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  qcoupled_rec L st' (xrec st X K_BATCH_CLASS kb l1 l2 drained) (qr_unbatch R).
Proof.
  intros L st st' X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF EL EG. (pose proof CP as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_remove_bslot; [exact CP| rewrite EL; exact LN1| rewrite EG; exact LN2| | | reflexivity| exact XB| exact WF].
  - unfold qr_entries, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite EL, EG, EP. reflexivity.
  - unfold qr_bslots, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite EB, app_nil_r. apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_at_of_dr : forall L st X R m,
  AQdr R 0 0 L st X m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3 B1 B2.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split.
  - (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
    unfold qcoupled. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
  - (nd_pre NUM 3%nat; intros N1 N2 N3; nd_post). exact (conj N1 (conj N2 (conj N3 (conj B1 B2)))).
Qed.
End CANSEC1.
End TwB.
End ARepQD.

(* [comment removed for export] *)
Module F_adepot1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.ADepotKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
(* [comment removed for export] *) From Ltac2 Require Ltac2.
#[local] Ltac2 Set StepFast.sf_fold_goal := Ltac2.Init.false.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition imemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (length src) src].

Section Memcpy.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (src rest junk : list byte).
  Notation D := (bv_unsigned a0).
  Notation n := (Z.of_nat (length src)).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SRC : bytes_at asegs m S (src ++ rest).
  Hypothesis DST : rw_cells asegs m D [CB (length src) junk].
  Hypothesis A1 : a1 = Z_to_bv 64 S.
  Hypothesis A2 : a2 = Z_to_bv 64 n.
  Hypothesis SEP : (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z.
  Hypothesis DSMALL : (D + n < 2^63)%Z.
  Hypothesis SSMALL : (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z.
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Notation POST := (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D src m).

  (* [comment removed for export] *)
  #[using="rest junk SRC DST SEP DSMALL RS RD"] Lemma imemcpy_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte) x14,
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr asegs mc D bs -> length bs = length src -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = nth_error src j) ->
    munch [(D, D + n)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (S + i)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) x14 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67a28) fc None mc (seg_rom asegs)).
  Proof.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    induction k as [|k IH]; intros i mc bs x14 Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (SRC1 : bytes_at asegs mc S (src ++ rest)).
    { eapply bytes_at_transport; [exact SRC | exact MU |]. cbn [disjoint_from]. clear - SEP Hi SB DB. lia. }
    pose proof (u8ro_read asegs mc S (src ++ rest) i b (wa (S + i)) SRC1 ltac:(rewrite nth_error_app1 by lia; exact NB) ltac:(lia) eq_refl) as RDb.
    zstep. cbv beta.
    pose proof (u8arr_store_ok asegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write asegs mc D bs i b ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    store_done.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite Arr.upd_length; exact LBS | | assumption | assumption | assumption].
      + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
    - zstep.
      assert (E : upd bs (Z.to_nat i) b = src).
      { apply nth_error_ext. intros j. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. destruct (Nat.lt_ge_cases j (Z.to_nat i)); [apply DONE; lia|].
          rewrite (proj2 (nth_error_None _ _)) by (rewrite LBS; lia). rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity. }
      rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. finish.
  Qed.

  #[using="S rest junk MI SRC DST A1 A2 SEP DSMALL RS RD"] Lemma imemcpy_body : (1 <= n < 2^64)%Z ->
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x67a1c) fc None m (seg_rom asegs)).
  Proof.
    intros N1. pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. subst a1 a2.
    zstep. if_cases K; zify_cond K. { exfalso. revert K N1 DB. clear. intros K N1 DB. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 3 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    eapply (imemcpy_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
    - eapply u8arr_of_rw_cells. exact DST.
    - pose proof DST as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF.
  Qed.
End Memcpy.

#[using="Type"] Lemma imemcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (src rest junk : list byte),
  mem_inv asegs m -> bytes_at asegs m S (src ++ rest) -> rw_cells asegs m (bv_unsigned a0) [CB (length src) junk] ->
  (S + Z.of_nat (length (src ++ rest)) <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length src) <= S)%Z ->
  (bv_unsigned a0 + Z.of_nat (length src) < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z ->
  (1 <= Z.of_nat (length src) < 2^64)%Z ->
  rng RNG S (Z.of_nat (length src)) -> rng RNG (bv_unsigned a0) (Z.of_nat (length src)) ->
  evtF asegs RNG (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a1c) fc None m (seg_rom asegs)).
Proof. intros. eapply imemcpy_body; try eassumption; reflexivity. Qed.

(* [comment removed for export] *)
Definition imemcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (length src) src].

#[using="Type"] Lemma imemcpy_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src rest junk : list byte),
  mem_inv asegs m -> bytes_at asegs m S (src ++ rest) -> rw_cells asegs m D [CB (length src) junk] ->
  n = Z.of_nat (length src) ->
  (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z ->
  (D + n < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z -> (1 <= n)%Z ->
  rng RNG S n -> rng RNG D n ->
  evtF asegs RNG (imemcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 D src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a1c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI SRC DST -> SEP DS SS N1 RS RD.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemcpy_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S src rest junk);
      rewrite ?U; try eassumption; try reflexivity; lia. }
  intros ms' P. unfold imemcpy_post in P. rewrite !U in P. exact P.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amo_add_w_le4 : forall tf cnt, (0 <= tf)%Z -> (0 <= cnt)%Z -> (tf + cnt < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) (low32 (Z_to_bv 64 cnt))))
  = le4 (Z_to_bv 64 (tf + cnt)).
Proof.
  intros tf cnt H0 H1 H2. unfold le4 at 2. rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  assert (E2 : bv_unsigned (low32 (Z_to_bv 64 cnt)) = cnt).
  { unfold low32. rewrite bv_extract_unsigned. rewrite unsigned_lit by lia. rewrite Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E1, E2. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac amo_stepW4 :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; rewrite amo_add_w_le4 by lia; mem_after_store_opt ]
    end end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Lock.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo B v : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
  Hypothesis ALO : (AIMG_HI <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 B.
  Hypothesis CELL : rw_cells asegs m B [C4 (Z_to_bv 64 v)].
  Hypothesis BV : (0 <= v < 2^31)%Z.
  Hypothesis BA : (B mod 4 = 0 /\ TAB <= B /\ B + 4 <= NUNIQ)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG B 4.

  Definition lock_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' lw,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' B [C4 lw].

  #[using="MI ST LO ALO A0 CELL BV BA RSTK RB"] Lemma lock_body : evtF asegs RNG lock_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x76d74) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (B, B + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, TAB, NUNIQ in *.
    assert (RSTK' : rng RNG (bv_unsigned sp + -48) 48) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0. carve_frame 48%nat ST.
    do 10 zstep. zstep. rewrite sx32_lit by lia.
    zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - BV K1. lia. }
    zstep.
    assert (AMO : amo_aligned AW (Z_to_bv 64 B) = true) by (apply amo_alignedW_intro; [lia| lia]).
    amo_stepA AMO. rewrite sx32_lit by lia.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    amo_stepA AMO.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. }
    zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. lia. }
    do 7 zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold lock_post.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. all: match goal with H : rw_cells asegs _ B ?c |- _ => idtac c; exact H end.
  Qed.
End Lock.

(* [comment removed for export] *)
End CANSEC2.
Ltac shr0 :=
  repeat match goal with |- context [Z.shiftr ?x ?k] =>
    replace (Z.shiftr x k) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia) end.


Section CANSEC3. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NStoreFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NStore.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (lo NDp AR T sz tf STORE : Z) (HW : word) (tb : list word) (jn jl js jh jf : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 112)%Z.
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 NDp.
  Hypothesis A2 : a2 = Z_to_bv 64 AR.
  Hypothesis A3 : a3 = HW.
  Hypothesis ARGS : rw_cells asegs m AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].
  Hypothesis ARB : (bv_unsigned sp <= AR /\ AR + 16 <= 2^47)%Z.
  Hypothesis NODE : rw_cells asegs m NDp [CB 8 jn; CB 4 jl; CB 4 js].
  Hypothesis CTF : rw_cells asegs m SSTF [C8 (Z_to_bv 64 tf)].
  Hypothesis CPTR : rw_cells asegs m SSPTR [C8 (Z_to_bv 64 STORE)].
  Hypothesis CST : rw_cells asegs m SSST [C4 (Z_to_bv 64 tf)].
  Hypothesis FRAMES : rw_cells asegs m (STORE + 8 * tf) [CB 8 jh; CB (Z.to_nat (8 * sz)) jf].
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TF : (0 <= tf /\ tf + sz + 1 < 1048576)%Z.
  Hypothesis TBB : (bv_unsigned sp <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis NDB : (AIMG_HI <= NDp /\ NDp + 16 <= ATOP /\ NDp mod 16 = 0)%Z.
  Hypothesis STOB : (AIMG_HI <= STORE /\ STORE + 8388608 <= ATOP /\ STORE mod 4096 = 0)%Z.
  Hypothesis SEPNS : (NDp + 16 <= STORE + 8 * tf \/ STORE + 8 * (tf + sz + 1) <= NDp)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RAR : rng RNG AR 16.
  Hypothesis RND : rng RNG NDp 16.
  Hypothesis RFR : rng RNG (STORE + 8 * tf) (8 * (sz + 1)).
  Hypothesis RT : rng RNG T 2040.

  Definition nstore_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' NDp [C8 HW; CB 4 jl; C4 (Z_to_bv 64 (tf + 1))]
      /\ rw_cells asegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells asegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells asegs m' (STORE + 8 * tf) [C8 (Z_to_bv 64 sz); CB (Z.to_nat (8 * sz)) (firstn (Z.to_nat (8 * sz)) (u64s tb))]
      /\ rw_cells asegs m' AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].

  #[using="rc jn js jh jf MI ST LO ALO A0 A2 A3 ARGS ARB NODE CTF CPTR CST FRAMES TB LTB SZ TF TBB NDB STOB SEPNS RI RSTK RAR RND RFR RT"] Lemma nstore_body : evtF asegs RNG nstore_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x762f8) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, SSTF, SSPTR, SSST in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -112) 112) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0 a2 a3.
    change (?P) with (sf_hide P) in SEPNS.
    pose proof FRAMES as FRM. change (?P) with (sf_hide P) in FRAMES. pose proof NODE as NDC. change (?P) with (sf_hide P) in NODE.
    pose proof ARGS as ARGC. change (?P) with (sf_hide P) in ARGS.
    carve_frame 32%nat ST.
    do 10 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 9 zstep. zstep. rewrite sx32_lit by lia. zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. fold_lits.
    rewrite Z.lor_0_r. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1 SZ. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    zstep. zstep.
    (* [comment removed for export] *)
    let x1 := reg_val 1%Z in let x2 := reg_val 2%Z in let x5 := reg_val 5%Z in let x6 := reg_val 6%Z in let x7 := reg_val 7%Z in
    let x8 := reg_val 8%Z in let x9 := reg_val 9%Z in let x11 := reg_val 11%Z in let x12 := reg_val 12%Z in let x13 := reg_val 13%Z in
    let x14 := reg_val 14%Z in let x15 := reg_val 15%Z in let x16 := reg_val 16%Z in let x17 := reg_val 17%Z in let x18 := reg_val 18%Z in
    let x19 := reg_val 19%Z in let x20 := reg_val 20%Z in let x21 := reg_val 21%Z in let x28 := reg_val 28%Z in let x29 := reg_val 29%Z in
    let x30 := reg_val 30%Z in let x31 := reg_val 31%Z in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (REST : forall x10, evtF asegs RNG nstore_post (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x7403c) fc None mc (seg_rom asegs)))
    end.
    2:{ zstep. if_cases K3; zify_cond K3; [apply REST|]. zstep. replace (Z_to_bv 64 255) with (Z_to_bv 64 sz) by (f_equal; clear -K3 SZ; lia). apply REST. }
    intros x10.
    zstep. zstep. zstep. do 4 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 5 zstep. amo_step.
    zstep. zstep. shr0. zstep. zstep. shr0.
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. lia. }
    zstep. shr0.
    zstep. if_cases K5; zify_cond K5. 2:{ exfalso. clear -K5. lia. }
    zstep. zstep. zstep. zstep. zstep. if_cases K6; zify_cond K6. { exfalso. clear -K6 STOB. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with |- context [Z.shiftr ?e 41] =>
      replace (Z.shiftr e 41) with (8 * tf)%Z
        by (rewrite Z.shiftl_mul_pow2 by lia;
            first [ change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia
                  | change 18446744073709551616%Z with (2^64)%Z ];
            rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia;
            change (2^44)%Z with (8 * 2^41)%Z; rewrite Z.mul_assoc, Z.div_mul by lia; lia)
    end.
    do 3 zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K7; zify_cond K7. { exfalso. clear -K7 STOB TF. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep. rewrite Z.lor_0_l.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRM. destruct FRM as [FRM FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (SRC := firstn (Z.to_nat (8 * sz)) (u64s tb)).
    assert (LSRC : length SRC = Z.to_nat (8 * sz)) by (subst SRC; rewrite firstn_length, u64s_length, LTB; lia).
    replace (Z.shiftl sz 3) with (Z.of_nat (length SRC)) by (rewrite LSRC, Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TBc : bytes_at asegs mc T (SRC ++ skipn (Z.to_nat (8 * sz)) (u64s tb)))
        by (subst SRC; rewrite firstn_skipn; match goal with H : u64arr asegs mc T tb |- _ => exact (proj1 H) end);
      assert (DSTc : rw_cells asegs mc (FA + 8) [CB (length SRC) jf]) by (rewrite LSRC; assumption)
    end.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (imemcpy_specZ RNG) with (src := SRC) (rest := skipn (Z.to_nat (8 * sz)) (u64s tb)) (junk := jf);
        [ eassumption | exact TBc | exact DSTc | reflexivity
        | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; unfold sf_hide in *; lia
        | rewrite LSRC; lia | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; lia | rewrite LSRC; lia
        | rewrite LSRC; eapply rng_sub'; [exact RT | lia] | rewrite LSRC; eapply rng_sub'; [exact RFR | lia] ]
      | (post_call asegs mc) ]
    end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z.land (Z.shiftr tf 16) 18446744073709551600) with 0%Z.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by (shr0; try lia; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
        rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
    zstep. zstep. fold_lits. amo_stepW4. rewrite sx32_lit by lia.
    zstep. zstep. zstep. shr0.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : rw_cells asegs _ (bv_unsigned sp + -96) (C8 (Z_to_bv 64 tf) :: ?rest) |- _ =>
      apply (rw_cells_C8_C4C4 asegs _ _ [] rest tf) in H; [cbn [app] in H | lia] end.
    zstep. rewrite sx32_lit by lia. zstep.
    (* [comment removed for export] *)
    setreg 10%Z (Z_to_bv 64 0)
      ltac:(f_equal; symmetry;
            match goal with |- Z.b2z (Z.lxor ?y 1048576 <? 1)%Z = 0%Z =>
              replace y with (sz + 1 + tf)%Z
                by (try change 4294967295%Z with (Z.ones 32); try change 18446744073709551615%Z with (Z.ones 64);
                    rewrite ?Z.land_ones by lia; try change (2^32)%Z with 4294967296%Z; try change (2^64)%Z with 18446744073709551616%Z;
                    symmetry; Z.div_mod_to_equations; lia) end;
            change 1048576%Z with (2^20)%Z; rewrite zb_lxor_pow2_small by lia;
            replace (_ <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    zstep. zstep. zstep. try rewrite sx32_lit by lia.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K8; zify_cond K8. { exfalso. clear -K8. lia. }
    do 4 zstep.
    match goal with FR1 : rw_cells asegs _ (bv_unsigned sp + -112) _, ST : stk asegs _ lo _ |- _ => release_frame FR1 ST (bv_unsigned sp + -96)%Z end.
    match goal with FR0 : rw_cells asegs _ (bv_unsigned sp + -96) _, ST : stk asegs _ lo _ |- _ => release_frame FR0 ST (bv_unsigned sp + -32)%Z end.
    match goal with FR : rw_cells asegs _ (bv_unsigned sp + -32) _, ST : stk asegs _ lo _ |- _ => release_frame FR ST (bv_unsigned sp) end.
    match goal with CTF : rw_cells asegs _ 1574088 _ |- _ => cbn [amo_val] in CTF; rewrite lit_add_lit in CTF end.
    apply evtF_done. unfold nstore_post. subst FA. unfold sf_hide in *.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (tf + (sz + 1))%Z with (tf + sz + 1)%Z in * by lia.
    do 16 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - match goal with H : rw_cells asegs _ NDp _ |- _ =>
        rewrite bv_swrap_small in H by (change (bv_half_modulus 32) with 2147483648%Z; lia); exact H end.
    - fold SRC. apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [assumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- LSRC. assumption.
  Qed.
End NStore.
End NStoreFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HashLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T sz : Z) (tb : list word).
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TBB : (0 <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis RT : rng RNG T 2040.

  #[using="TB LTB SZ TBB RT"] Lemma hash_loop : forall (k : nat) (i h : Z) x15 x16 (Q : machine_state -> Prop),
    Z.to_nat (sz - i) = k -> (0 <= i < sz)%Z -> (0 <= h < 2^64)%Z ->
    (forall x15' x16',
       evtF asegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * sz))
                  (Z_to_bv 64 (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))))
                  a3 (Z_to_bv 64 (T + 8 * sz)) x15' x16' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x766b4) fc None m (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * i)) (Z_to_bv 64 h)
               a3 (Z_to_bv 64 (T + 8 * sz)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x76690) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros i h x15 x16 Q Hk Hi Hh K; [exfalso; lia|].
    destruct (nth_error tb (Z.to_nat i)) as [w|] eqn:NTH. 2:{ exfalso. apply nth_error_None in NTH. rewrite LTB in NTH. lia. }
    pose proof (u64arr_read asegs m T tb i w (wa (T + 8 * i)) TB NTH ltac:(lia) eq_refl) as RD.
    do 8 zstep.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?a h * ?M)%Z] =>
      replace (Z_to_bv 64 (Z.lxor a h * M)%Z) with (Z_to_bv 64 (mz_add h (bv_unsigned w)))
        by (unfold mz_add, mz_mix; apply Z_to_bv_mod64) end.
    pose proof (mz_add_range h (bv_unsigned w)) as Hh'.
    assert (SK : skipn (Z.to_nat i) tb = w :: skipn (Z.to_nat (i + 1)) tb).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      clear - NTH. revert NTH. generalize (Z.to_nat i) as n. intros n NTH.
      revert tb NTH. induction n as [|n IHn]; intros [|x l] NTH; cbn in *; try discriminate.
      - injection NTH as ->. reflexivity.
      - apply IHn. exact NTH. }
    zstep. if_cases KB; zify_cond KB.
    - replace (T + 8 * i + 8)%Z with (T + 8 * (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact Hh' |].
      intros x15' x16'.
      replace (mz_adds (mz_add h (bv_unsigned w)) (map bv_unsigned (firstn (Z.to_nat (sz - (i + 1))) (skipn (Z.to_nat (i + 1)) tb))))
        with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with (S (Z.to_nat (sz - (i + 1)))) by lia. cbn [firstn map mz_adds fold_left]. reflexivity.
    - replace (T + 8 * i + 8)%Z with (T + 8 * sz)%Z by lia.
      replace (mz_add h (bv_unsigned w)) with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with 1%nat by lia. cbn. reflexivity.
  Qed.
End HashLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FindFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Section FindLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hsh NODES N : Z) (hs lk sid : Z -> Z).
  Hypothesis Hh : (0 <= hsh < 2^64)%Z.
  Hypothesis HN : (1 <= N < 65536)%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis CMAP : rw_cells asegs m MAP1 [C8 (Z_to_bv 64 NODES)].
  Hypothesis CN : forall i, (1 <= i <= N)%Z ->
    rw_cells asegs m (NODES + 16 * i) [C8 (Z_to_bv 64 (hs i)); C4 (Z_to_bv 64 (lk i)); C4 (Z_to_bv 64 (sid i))].
  Hypothesis NB : (AIMG_HI <= NODES /\ NODES + 1048576 <= ATOP /\ NODES mod 4096 = 0)%Z.
  Hypothesis LK : lk_ok lk N.
  Hypothesis HS : forall i, (1 <= i <= N)%Z -> (0 <= hs i < 2^64)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RNODES : rng RNG NODES 1048576.

  #[warnings="-notation-for-abbreviation"] Notation ST_AT pc x10 x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 hsh) s4 s5 (Z_to_bv 64 0xffff) s7 (Z_to_bv 64 MAP1) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  #[using="rc NODES sid Hh HN CMAP CN NB LK HS RI RNODES"] Lemma find_loop : forall (k : nat) (j : Z) x10 x12 (Q : machine_state -> Prop),
    (Z.to_nat j <= k)%nat -> (0 <= j <= N)%Z ->
    (forall j' x11 x12', (1 <= j' <= N)%Z -> hs j' = hsh -> In j' (chain lk j) ->
       evtF asegs RNG Q (ST_AT 0x76824 (Z_to_bv 64 j') x11 x12')) ->
    (forall x10' x12', Forall (fun j' => hs j' <> hsh) (chain lk j) ->
       evtF asegs RNG Q (ST_AT 0x76778 x10' (Z_to_bv 64 0) x12')) ->
    evtF asegs RNG Q (ST_AT 0x76720 x10 (Z_to_bv 64 j) x12).
  Proof.
    unfold AIMG_HI, MAP1 in *.
    induction k as [|k IH]; intros j x10 x12 Q Hk Hj FOUND ABSENT.
    - assert (j = 0%Z) by lia. subst j.
      zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. }
      apply ABSENT. rewrite chain_0. constructor.
    - destruct (Z.eq_dec j 0) as [->|NZ].
      { zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. } apply ABSENT. rewrite chain_0. constructor. }
      pose proof (CN j ltac:(lia)) as NODE. pose proof (LK j ltac:(lia)) as LKj. pose proof (HS j ltac:(lia)) as HSj.
      pose proof (chain_cons lk N j LK ltac:(lia)) as CC.
      zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. zstep.
      replace (bv_swrap 32 (Z.shiftr (bv_wrap 32 j) 16)) with 0%Z
        by (rewrite bv_wrap_small by (change (bv_modulus 32) with 4294967296%Z; lia); rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
      do 3 zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      do 5 zstep.
      setreg 11%Z (Z_to_bv 64 (NODES + 16 * j))
        ltac:(f_equal; rewrite Z.mod_small by lia; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia;
              rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      remember (NODES + 16 * j)%Z as NA eqn:ENA.
      zstep. zstep. rewrite sx32_lit by lia.
      subst NA.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply (IH (lk j)); [lia | lia | |].
        * intros j' x11 x12' H1 H2 H3. apply FOUND; [exact H1 | exact H2 |]. rewrite CC. right. exact H3.
        * intros x10' x12' FA. apply ABSENT. rewrite CC. constructor; [| exact FA]. clear -K2. intros E. apply K2. rewrite E. reflexivity.
      + (* [comment removed for export] *)
        zstep. apply FOUND; [lia | | rewrite CC; left; reflexivity]. clear -K2 Hh HSj. first [exact K2 | symmetry; exact K2 | lia].
  Qed.
End FindLoop.
End FindFile.
End CANSEC3.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.ADepotKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition imemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (length src) src].

Section Memcpy.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (src rest junk : list byte).
  Notation D := (bv_unsigned a0).
  Notation n := (Z.of_nat (length src)).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SRC : bytes_at asegs m S (src ++ rest).
  Hypothesis DST : rw_cells asegs m D [CB (length src) junk].
  Hypothesis A1 : a1 = Z_to_bv 64 S.
  Hypothesis A2 : a2 = Z_to_bv 64 n.
  Hypothesis SEP : (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z.
  Hypothesis DSMALL : (D + n < 2^63)%Z.
  Hypothesis SSMALL : (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z.
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Notation POST := (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 D src m).

  (* [comment removed for export] *)
  #[using="rest junk SRC DST SEP DSMALL RS RD"] Lemma imemcpy_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte) x14,
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr asegs mc D bs -> length bs = length src -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = nth_error src j) ->
    munch [(D, D + n)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (S + i)) (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) x14 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67a90) fc None mc (seg_rom asegs)).
  Proof.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    induction k as [|k IH]; intros i mc bs x14 Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    destruct (nth_error src (Z.to_nat i)) as [b|] eqn:NB. 2:{ exfalso. apply nth_error_None in NB. lia. }
    assert (SRC1 : bytes_at asegs mc S (src ++ rest)).
    { eapply bytes_at_transport; [exact SRC | exact MU |]. cbn [disjoint_from]. clear - SEP Hi SB DB. lia. }
    pose proof (u8ro_read asegs mc S (src ++ rest) i b (wa (S + i)) SRC1 ltac:(rewrite nth_error_app1 by lia; exact NB) ltac:(lia) eq_refl) as RDb.
    zstep. cbv beta.
    pose proof (u8arr_store_ok asegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write asegs mc D bs i b ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    store_done.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia. replace (S + i + 1)%Z with (S + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite Arr.upd_length; exact LBS | | assumption | assumption | assumption].
      + intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. apply DONE. lia.
    - zstep.
      assert (E : upd bs (Z.to_nat i) b = src).
      { apply nth_error_ext. intros j. destruct (Nat.eq_dec j (Z.to_nat i)).
        * subst j. rewrite Arr.nth_error_upd_same by (rewrite LBS; lia). symmetry; exact NB.
        * rewrite Arr.nth_error_upd_other by lia. destruct (Nat.lt_ge_cases j (Z.to_nat i)); [apply DONE; lia|].
          rewrite (proj2 (nth_error_None _ _)) by (rewrite LBS; lia). rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity. }
      rewrite E in ARR'. apply rw_cells_of_u8arr in ARR'. finish.
  Qed.

  #[using="S rest junk MI SRC DST A1 A2 SEP DSMALL RS RD"] Lemma imemcpy_body : (1 <= n < 2^64)%Z ->
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x67a84) fc None m (seg_rom asegs)).
  Proof.
    intros N1. pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. subst a1 a2.
    zstep. if_cases K; zify_cond K. { exfalso. revert K N1 DB. clear. intros K N1 DB. Z.div_mod_to_equations. lia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 3 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
    eapply (imemcpy_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
    - eapply u8arr_of_rw_cells. exact DST.
    - pose proof DST as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF.
  Qed.
End Memcpy.

#[using="Type"] Lemma imemcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (src rest junk : list byte),
  mem_inv asegs m -> bytes_at asegs m S (src ++ rest) -> rw_cells asegs m (bv_unsigned a0) [CB (length src) junk] ->
  (S + Z.of_nat (length (src ++ rest)) <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length src) <= S)%Z ->
  (bv_unsigned a0 + Z.of_nat (length src) < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z ->
  (1 <= Z.of_nat (length src) < 2^64)%Z ->
  rng RNG S (Z.of_nat (length src)) -> rng RNG (bv_unsigned a0) (Z.of_nat (length src)) ->
  evtF asegs RNG (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a84) fc None m (seg_rom asegs)).
Proof. intros. eapply imemcpy_body; try eassumption; reflexivity. Qed.

(* [comment removed for export] *)
Definition imemcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (D : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + Z.of_nat (length src))]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' D [CB (length src) src].

#[using="Type"] Lemma imemcpy_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src rest junk : list byte),
  mem_inv asegs m -> bytes_at asegs m S (src ++ rest) -> rw_cells asegs m D [CB (length src) junk] ->
  n = Z.of_nat (length src) ->
  (S + Z.of_nat (length (src ++ rest)) <= D \/ D + n <= S)%Z ->
  (D + n < 2^63)%Z -> (S + Z.of_nat (length (src ++ rest)) < 2^63)%Z -> (1 <= n)%Z ->
  rng RNG S n -> rng RNG D n ->
  evtF asegs RNG (imemcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 D src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a84) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI SRC DST -> SEP DS SS N1 RS RD.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemcpy_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S src rest junk);
      rewrite ?U; try eassumption; try reflexivity; lia. }
  intros ms' P. unfold imemcpy_post in P. rewrite !U in P. exact P.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amo_add_w_le4 : forall tf cnt, (0 <= tf)%Z -> (0 <= cnt)%Z -> (tf + cnt < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) (low32 (Z_to_bv 64 cnt))))
  = le4 (Z_to_bv 64 (tf + cnt)).
Proof.
  intros tf cnt H0 H1 H2. unfold le4 at 2. rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  assert (E2 : bv_unsigned (low32 (Z_to_bv 64 cnt)) = cnt).
  { unfold low32. rewrite bv_extract_unsigned. rewrite unsigned_lit by lia. rewrite Z.shiftr_0_r.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E1, E2. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac amo_stepW4 :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; rewrite amo_add_w_le4 by lia; mem_after_store_opt ]
    end end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Lock.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo B v : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
  Hypothesis ALO : (AIMG_HI <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 B.
  Hypothesis CELL : rw_cells asegs m B [C4 (Z_to_bv 64 v)].
  Hypothesis BV : (0 <= v < 2^31)%Z.
  Hypothesis BA : (B mod 4 = 0 /\ TAB <= B /\ B + 4 <= NUNIQ)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG B 4.

  Definition lock_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' lw,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (B, B + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' B [C4 lw].

  #[using="MI ST LO ALO A0 CELL BV BA RSTK RB"] Lemma lock_body : evtF asegs RNG lock_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x76ddc) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (B, B + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, TAB, NUNIQ in *.
    assert (RSTK' : rng RNG (bv_unsigned sp + -48) 48) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0. carve_frame 48%nat ST.
    do 10 zstep. zstep. rewrite sx32_lit by lia.
    zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - BV K1. lia. }
    zstep.
    assert (AMO : amo_aligned AW (Z_to_bv 64 B) = true) by (apply amo_alignedW_intro; [lia| lia]).
    amo_stepA AMO. rewrite sx32_lit by lia.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    amo_stepA AMO.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. }
    zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. lia. }
    do 7 zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold lock_post.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. all: match goal with H : rw_cells asegs _ B ?c |- _ => idtac c; exact H end.
  Qed.
End Lock.

(* [comment removed for export] *)
End CANSEC2.
Ltac shr0 :=
  repeat match goal with |- context [Z.shiftr ?x ?k] =>
    replace (Z.shiftr x k) with 0%Z by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia) end.


Section CANSEC3. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NStoreFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NStore.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (lo NDp AR T sz tf STORE : Z) (HW : word) (tb : list word) (jn jl js jh jf : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 112)%Z.
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis A0 : a0 = Z_to_bv 64 NDp.
  Hypothesis A2 : a2 = Z_to_bv 64 AR.
  Hypothesis A3 : a3 = HW.
  Hypothesis ARGS : rw_cells asegs m AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].
  Hypothesis ARB : (bv_unsigned sp <= AR /\ AR + 16 <= 2^47)%Z.
  Hypothesis NODE : rw_cells asegs m NDp [CB 8 jn; CB 4 jl; CB 4 js].
  Hypothesis CTF : rw_cells asegs m SSTF [C8 (Z_to_bv 64 tf)].
  Hypothesis CPTR : rw_cells asegs m SSPTR [C8 (Z_to_bv 64 STORE)].
  Hypothesis CST : rw_cells asegs m SSST [C4 (Z_to_bv 64 tf)].
  Hypothesis FRAMES : rw_cells asegs m (STORE + 8 * tf) [CB 8 jh; CB (Z.to_nat (8 * sz)) jf].
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TF : (0 <= tf /\ tf + sz + 1 < 1048576)%Z.
  Hypothesis TBB : (bv_unsigned sp <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis NDB : (AIMG_HI <= NDp /\ NDp + 16 <= ATOP /\ NDp mod 16 = 0)%Z.
  Hypothesis STOB : (AIMG_HI <= STORE /\ STORE + 8388608 <= ATOP /\ STORE mod 4096 = 0)%Z.
  Hypothesis SEPNS : (NDp + 16 <= STORE + 8 * tf \/ STORE + 8 * (tf + sz + 1) <= NDp)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RAR : rng RNG AR 16.
  Hypothesis RND : rng RNG NDp 16.
  Hypothesis RFR : rng RNG (STORE + 8 * tf) (8 * (sz + 1)).
  Hypothesis RT : rng RNG T 2040.

  Definition nstore_post : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' NDp [C8 HW; CB 4 jl; C4 (Z_to_bv 64 (tf + 1))]
      /\ rw_cells asegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells asegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))]
      /\ rw_cells asegs m' (STORE + 8 * tf) [C8 (Z_to_bv 64 sz); CB (Z.to_nat (8 * sz)) (firstn (Z.to_nat (8 * sz)) (u64s tb))]
      /\ rw_cells asegs m' AR [C8 (Z_to_bv 64 T); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)].

  #[using="rc jn js jh jf MI ST LO ALO A0 A2 A3 ARGS ARB NODE CTF CPTR CST FRAMES TB LTB SZ TF TBB NDB STOB SEPNS RI RSTK RAR RND RFR RT"] Lemma nstore_body : evtF asegs RNG nstore_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x76360) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (NDp, NDp + 16); (SSTF, SSTF + 8); (SSST, SSST + 4); (STORE + 8 * tf, STORE + 8 * tf + 8 * (sz + 1))]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold AIMG_HI, SSTF, SSPTR, SSST in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -112) 112) by (eapply rng_sub'; [exact RSTK| lia]).
    subst a0 a2 a3.
    change (?P) with (sf_hide P) in SEPNS.
    pose proof FRAMES as FRM. change (?P) with (sf_hide P) in FRAMES. pose proof NODE as NDC. change (?P) with (sf_hide P) in NODE.
    pose proof ARGS as ARGC. change (?P) with (sf_hide P) in ARGS.
    carve_frame 32%nat ST.
    do 10 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 9 zstep. zstep. rewrite sx32_lit by lia. zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. fold_lits.
    rewrite Z.lor_0_r. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear -K1 SZ. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
    zstep. zstep.
    (* [comment removed for export] *)
    let x1 := reg_val 1%Z in let x2 := reg_val 2%Z in let x5 := reg_val 5%Z in let x6 := reg_val 6%Z in let x7 := reg_val 7%Z in
    let x8 := reg_val 8%Z in let x9 := reg_val 9%Z in let x11 := reg_val 11%Z in let x12 := reg_val 12%Z in let x13 := reg_val 13%Z in
    let x14 := reg_val 14%Z in let x15 := reg_val 15%Z in let x16 := reg_val 16%Z in let x17 := reg_val 17%Z in let x18 := reg_val 18%Z in
    let x19 := reg_val 19%Z in let x20 := reg_val 20%Z in let x21 := reg_val 21%Z in let x28 := reg_val 28%Z in let x29 := reg_val 29%Z in
    let x30 := reg_val 30%Z in let x31 := reg_val 31%Z in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (REST : forall x10, evtF asegs RNG nstore_post (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x740a4) fc None mc (seg_rom asegs)))
    end.
    2:{ zstep. if_cases K3; zify_cond K3; [apply REST|]. zstep. replace (Z_to_bv 64 255) with (Z_to_bv 64 sz) by (f_equal; clear -K3 SZ; lia). apply REST. }
    intros x10.
    zstep. zstep. zstep. do 4 zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 5 zstep. amo_step.
    zstep. zstep. shr0. zstep. zstep. shr0.
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. lia. }
    zstep. shr0.
    zstep. if_cases K5; zify_cond K5. 2:{ exfalso. clear -K5. lia. }
    zstep. zstep. zstep. zstep. zstep. if_cases K6; zify_cond K6. { exfalso. clear -K6 STOB. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with |- context [Z.shiftr ?e 41] =>
      replace (Z.shiftr e 41) with (8 * tf)%Z
        by (rewrite Z.shiftl_mul_pow2 by lia;
            first [ change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia
                  | change 18446744073709551616%Z with (2^64)%Z ];
            rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia;
            change (2^44)%Z with (8 * 2^41)%Z; rewrite Z.mul_assoc, Z.div_mul by lia; lia)
    end.
    do 3 zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K7; zify_cond K7. { exfalso. clear -K7 STOB TF. unfold AIMG_HI in STOB. lia. }
    zstep. zstep. zstep. rewrite Z.lor_0_l.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRM. destruct FRM as [FRM FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (SRC := firstn (Z.to_nat (8 * sz)) (u64s tb)).
    assert (LSRC : length SRC = Z.to_nat (8 * sz)) by (subst SRC; rewrite firstn_length, u64s_length, LTB; lia).
    replace (Z.shiftl sz 3) with (Z.of_nat (length SRC)) by (rewrite LSRC, Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TBc : bytes_at asegs mc T (SRC ++ skipn (Z.to_nat (8 * sz)) (u64s tb)))
        by (subst SRC; rewrite firstn_skipn; match goal with H : u64arr asegs mc T tb |- _ => exact (proj1 H) end);
      assert (DSTc : rw_cells asegs mc (FA + 8) [CB (length SRC) jf]) by (rewrite LSRC; assumption)
    end.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (imemcpy_specZ RNG) with (src := SRC) (rest := skipn (Z.to_nat (8 * sz)) (u64s tb)) (junk := jf);
        [ eassumption | exact TBc | exact DSTc | reflexivity
        | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; unfold sf_hide in *; lia
        | rewrite LSRC; lia | rewrite length_app, skipn_length, u64s_length, LTB, LSRC; lia | rewrite LSRC; lia
        | rewrite LSRC; eapply rng_sub'; [exact RT | lia] | rewrite LSRC; eapply rng_sub'; [exact RFR | lia] ]
      | (post_call asegs mc) ]
    end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z.land (Z.shiftr tf 16) 18446744073709551600) with 0%Z.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by (shr0; try lia; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
        rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
    zstep. zstep. fold_lits. amo_stepW4. rewrite sx32_lit by lia.
    zstep. zstep. zstep. shr0.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : rw_cells asegs _ (bv_unsigned sp + -96) (C8 (Z_to_bv 64 tf) :: ?rest) |- _ =>
      apply (rw_cells_C8_C4C4 asegs _ _ [] rest tf) in H; [cbn [app] in H | lia] end.
    zstep. rewrite sx32_lit by lia. zstep.
    (* [comment removed for export] *)
    setreg 10%Z (Z_to_bv 64 0)
      ltac:(f_equal; symmetry;
            match goal with |- Z.b2z (Z.lxor ?y 1048576 <? 1)%Z = 0%Z =>
              replace y with (sz + 1 + tf)%Z
                by (try change 4294967295%Z with (Z.ones 32); try change 18446744073709551615%Z with (Z.ones 64);
                    rewrite ?Z.land_ones by lia; try change (2^32)%Z with 4294967296%Z; try change (2^64)%Z with 18446744073709551616%Z;
                    symmetry; Z.div_mod_to_equations; lia) end;
            change 1048576%Z with (2^20)%Z; rewrite zb_lxor_pow2_small by lia;
            replace (_ <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    zstep. zstep. zstep. try rewrite sx32_lit by lia.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K8; zify_cond K8. { exfalso. clear -K8. lia. }
    do 4 zstep.
    match goal with FR1 : rw_cells asegs _ (bv_unsigned sp + -112) _, ST : stk asegs _ lo _ |- _ => release_frame FR1 ST (bv_unsigned sp + -96)%Z end.
    match goal with FR0 : rw_cells asegs _ (bv_unsigned sp + -96) _, ST : stk asegs _ lo _ |- _ => release_frame FR0 ST (bv_unsigned sp + -32)%Z end.
    match goal with FR : rw_cells asegs _ (bv_unsigned sp + -32) _, ST : stk asegs _ lo _ |- _ => release_frame FR ST (bv_unsigned sp) end.
    match goal with CTF : rw_cells asegs _ 1575112 _ |- _ => cbn [amo_val] in CTF; rewrite lit_add_lit in CTF end.
    apply evtF_done. unfold nstore_post. subst FA. unfold sf_hide in *.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (tf + (sz + 1))%Z with (tf + sz + 1)%Z in * by lia.
    do 16 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - match goal with H : rw_cells asegs _ NDp _ |- _ =>
        rewrite bv_swrap_small in H by (change (bv_half_modulus 32) with 2147483648%Z; lia); exact H end.
    - fold SRC. apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [assumption|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- LSRC. assumption.
  Qed.
End NStore.
End NStoreFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HashLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T sz : Z) (tb : list word).
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis SZ : (1 <= sz <= 255)%Z.
  Hypothesis TBB : (0 <= T /\ T + 2040 <= 2^47)%Z.
  Hypothesis RT : rng RNG T 2040.

  #[using="TB LTB SZ TBB RT"] Lemma hash_loop : forall (k : nat) (i h : Z) x15 x16 (Q : machine_state -> Prop),
    Z.to_nat (sz - i) = k -> (0 <= i < sz)%Z -> (0 <= h < 2^64)%Z ->
    (forall x15' x16',
       evtF asegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * sz))
                  (Z_to_bv 64 (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))))
                  a3 (Z_to_bv 64 (T + 8 * sz)) x15' x16' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x7671c) fc None m (seg_rom asegs))) ->
    evtF asegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14313749767032793493) (Z_to_bv 64 (T + 8 * i)) (Z_to_bv 64 h)
               a3 (Z_to_bv 64 (T + 8 * sz)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x766f8) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros i h x15 x16 Q Hk Hi Hh K; [exfalso; lia|].
    destruct (nth_error tb (Z.to_nat i)) as [w|] eqn:NTH. 2:{ exfalso. apply nth_error_None in NTH. rewrite LTB in NTH. lia. }
    pose proof (u64arr_read asegs m T tb i w (wa (T + 8 * i)) TB NTH ltac:(lia) eq_refl) as RD.
    do 8 zstep.
    lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?a h * ?M)%Z] =>
      replace (Z_to_bv 64 (Z.lxor a h * M)%Z) with (Z_to_bv 64 (mz_add h (bv_unsigned w)))
        by (unfold mz_add, mz_mix; apply Z_to_bv_mod64) end.
    pose proof (mz_add_range h (bv_unsigned w)) as Hh'.
    assert (SK : skipn (Z.to_nat i) tb = w :: skipn (Z.to_nat (i + 1)) tb).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      clear - NTH. revert NTH. generalize (Z.to_nat i) as n. intros n NTH.
      revert tb NTH. induction n as [|n IHn]; intros [|x l] NTH; cbn in *; try discriminate.
      - injection NTH as ->. reflexivity.
      - apply IHn. exact NTH. }
    zstep. if_cases KB; zify_cond KB.
    - replace (T + 8 * i + 8)%Z with (T + 8 * (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact Hh' |].
      intros x15' x16'.
      replace (mz_adds (mz_add h (bv_unsigned w)) (map bv_unsigned (firstn (Z.to_nat (sz - (i + 1))) (skipn (Z.to_nat (i + 1)) tb))))
        with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with (S (Z.to_nat (sz - (i + 1)))) by lia. cbn [firstn map mz_adds fold_left]. reflexivity.
    - replace (T + 8 * i + 8)%Z with (T + 8 * sz)%Z by lia.
      replace (mz_add h (bv_unsigned w)) with (mz_adds h (map bv_unsigned (firstn (Z.to_nat (sz - i)) (skipn (Z.to_nat i) tb)))); [apply K|].
      rewrite SK. replace (Z.to_nat (sz - i)) with 1%nat by lia. cbn. reflexivity.
  Qed.
End HashLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FindFile.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Section FindLoop.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hsh NODES N : Z) (hs lk sid : Z -> Z).
  Hypothesis Hh : (0 <= hsh < 2^64)%Z.
  Hypothesis HN : (1 <= N < 65536)%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis CMAP : rw_cells asegs m MAP1 [C8 (Z_to_bv 64 NODES)].
  Hypothesis CN : forall i, (1 <= i <= N)%Z ->
    rw_cells asegs m (NODES + 16 * i) [C8 (Z_to_bv 64 (hs i)); C4 (Z_to_bv 64 (lk i)); C4 (Z_to_bv 64 (sid i))].
  Hypothesis NB : (AIMG_HI <= NODES /\ NODES + 1048576 <= ATOP /\ NODES mod 4096 = 0)%Z.
  Hypothesis LK : lk_ok lk N.
  Hypothesis HS : forall i, (1 <= i <= N)%Z -> (0 <= hs i < 2^64)%Z.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RNODES : rng RNG NODES 1048576.

  #[warnings="-notation-for-abbreviation"] Notation ST_AT pc x10 x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 hsh) s4 s5 (Z_to_bv 64 0xffff) s7 (Z_to_bv 64 MAP1) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  #[using="rc NODES sid Hh HN CMAP CN NB LK HS RI RNODES"] Lemma find_loop : forall (k : nat) (j : Z) x10 x12 (Q : machine_state -> Prop),
    (Z.to_nat j <= k)%nat -> (0 <= j <= N)%Z ->
    (forall j' x11 x12', (1 <= j' <= N)%Z -> hs j' = hsh -> In j' (chain lk j) ->
       evtF asegs RNG Q (ST_AT 0x7688c (Z_to_bv 64 j') x11 x12')) ->
    (forall x10' x12', Forall (fun j' => hs j' <> hsh) (chain lk j) ->
       evtF asegs RNG Q (ST_AT 0x767e0 x10' (Z_to_bv 64 0) x12')) ->
    evtF asegs RNG Q (ST_AT 0x76788 x10 (Z_to_bv 64 j) x12).
  Proof.
    unfold AIMG_HI, MAP1 in *.
    induction k as [|k IH]; intros j x10 x12 Q Hk Hj FOUND ABSENT.
    - assert (j = 0%Z) by lia. subst j.
      zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. }
      apply ABSENT. rewrite chain_0. constructor.
    - destruct (Z.eq_dec j 0) as [->|NZ].
      { zstep. if_cases K0; zify_cond K0. 2:{ exfalso. clear -K0. lia. } apply ABSENT. rewrite chain_0. constructor. }
      pose proof (CN j ltac:(lia)) as NODE. pose proof (LK j ltac:(lia)) as LKj. pose proof (HS j ltac:(lia)) as HSj.
      pose proof (chain_cons lk N j LK ltac:(lia)) as CC.
      zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. zstep.
      replace (bv_swrap 32 (Z.shiftr (bv_wrap 32 j) 16)) with 0%Z
        by (rewrite bv_wrap_small by (change (bv_modulus 32) with 4294967296%Z; lia); rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
      do 3 zstep.
      zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
      do 5 zstep.
      setreg 11%Z (Z_to_bv 64 (NODES + 16 * j))
        ltac:(f_equal; rewrite Z.mod_small by lia; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia;
              rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      remember (NODES + 16 * j)%Z as NA eqn:ENA.
      zstep. zstep. rewrite sx32_lit by lia.
      subst NA.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply (IH (lk j)); [lia | lia | |].
        * intros j' x11 x12' H1 H2 H3. apply FOUND; [exact H1 | exact H2 |]. rewrite CC. right. exact H3.
        * intros x10' x12' FA. apply ABSENT. rewrite CC. constructor; [| exact FA]. clear -K2. intros E. apply K2. rewrite E. reflexivity.
      + (* [comment removed for export] *)
        zstep. apply FOUND; [lia | | rewrite CC; left; reflexivity]. clear -K2 Hh HSj. first [exact K2 | symmetry; exact K2 | lia].
  Qed.
End FindLoop.
End FindFile.
End CANSEC3.
End TwB.
End F_adepot1.

(* [comment removed for export] *)
Module F_adepot.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepotKit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.ADepotKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma bkt_offset : forall h, (0 <= h)%Z ->
  Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. unfold bkt. rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616%Z with (2^20 * 2^44)%Z.
  rewrite Zmult_mod_distr_r. rewrite Z.shiftr_div_pow2 by lia.
  change (2^44)%Z with (4 * 2^42)%Z. rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
#[using="Type"] Lemma bkt_offset_land : forall h, (0 <= h)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 44) 18446744073709551615) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2^64)%Z with 18446744073709551616%Z. apply bkt_offset. exact Hh.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amo_add_w_le4_gen : forall tf (c : bv 32), (0 <= tf)%Z -> (tf + bv_unsigned c < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) c))
  = le4 (Z_to_bv 64 (tf + bv_unsigned c)).
Proof.
  intros tf c H0 H2. pose proof (bv_unsigned_in_range 32 c) as HC. unfold bv_modulus in HC. change (2 ^ Z.of_N 32)%Z with (2^32)%Z in HC.
  unfold le4 at 2. rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite E1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

End CANSEC1.
Ltac amo_stepW4c :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i;
        erewrite amo_add_w_le4_gen;
        [ match goal with |- context [le4 (Z_to_bv 64 (_ + bv_unsigned ?c))] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end;
          mem_after_store_opt
        | lia
        | match goal with |- context [bv_unsigned ?c] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end; lia ] ]
    end end
  end.

(* [comment removed for export] *)
Notation WFINE sp BA NDp FA sz :=
  ([(sp + -1024, sp); (BA, BA + 4); (5833944, 5833944 + 4); (NDp, NDp + 16);
    (1574088, 1574088 + 8); (1574112, 1574112 + 4); (FA, FA + 8 * (sz + 1))]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma dcells_ins : forall L D m m' (sp h v sid : Z) (u : list Z) csF,
  let N := dN D in let tf := dtf D in let b0 := bkt h in
  let BA := (TAB + 4 * b0)%Z in let NDp := (al_nodes L + 16 * (N + 1))%Z in let FA := (al_store L + 8 * tf)%Z in
  let sz := Z.of_nat (length u) in
  dcells L D m -> dlayout L -> (ATOP <= sp - 1024)%Z -> (sp <= 2^64)%Z -> (0 <= h)%Z ->
  (1 <= N)%Z -> (16 * (N + 2) <= 1048576)%Z -> (0 <= tf)%Z -> (8 * (tf + sz + 1) <= 8388608)%Z ->
  munch (WFINE sp BA NDp FA sz) m m' -> wmono asegs m m' ->
  rw_cells asegs m' BA [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NUNIQ [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NDp [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 sid)] ->
  rw_cells asegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSPTR [C8 (Z_to_bv 64 (al_store L))] ->
  rw_cells asegs m' MAP1 [C8 (Z_to_bv 64 (al_nodes L))] ->
  rw_cells asegs m' FA csF -> Z.of_nat (cells_size csF) = (8 * (sz + 1))%Z ->
  dcells L (dins D b0 h v sid sz) m'.
Proof.
  intros L D m m' sp h v sid u csF N tf b0 BA NDp FA sz DC LY SPL SPH Hh N1 NR TF0 TFR MU WM CBA CNU CND CTF CST CPTR CMAP CFA SF.
  assert (HB : (0 <= b0 < 1048576)%Z) by (subst b0; unfold bkt; apply Z.mod_pos_bound; lia).
  (nd_pre DC 9%nat; intros _ _ _ _ _ CT CN SKN SKS; nd_post).
  (pose proof LY as ndP__; nd_pre ndP__ 7%nat; intros _ _ LN0 LN1 LS0 LS1 DISJ; nd_post). unfold AIMG_HI, TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
  subst N tf BA NDp FA.
  (* [comment removed for export] *)
  assert (OUT : forall x,
    ((1639640 <= x < 1639640 + 4 * 1048576 /\ ~ (1639640 + 4 * b0 <= x < 1639640 + 4 * b0 + 4))
     \/ (al_nodes L + 16 <= x < al_nodes L + 1048576 /\ ~ (al_nodes L + 16 * (dN D + 1) <= x < al_nodes L + 16 * (dN D + 1) + 16))
     \/ (al_store L <= x < al_store L + 8388608 /\ ~ (al_store L + 8 * dtf D <= x < al_store L + 8 * dtf D + 8 * (sz + 1))))%Z ->
    m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point _ m m' x MU); [lia|]. cbn [outside]. lia. }
  clear MU.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. cbn [dhd dins]. destruct (Z.eqb_spec b b0) as [->|NE]; [exact CBA|].
    eapply rw_cells_agree; [exact (CT b Hb) | | exact WM]. intros x Hx. apply OUT. unfold TAB in Hx. cbn in Hx. left. lia. }
  split.
  { intros i Hi. cbn [dN dhs dlk dsid dins] in Hi |- *. destruct (Z.eqb_spec i (dN D + 1)) as [->|NE]; [exact CND|].
    eapply rw_cells_agree; [exact (CN i ltac:(lia)) | | exact WM]. intros x Hx. apply OUT. cbn in Hx. right; left. lia. }
  split.
  { cbn [dN dins]. destruct (stk_split asegs m _ (al_nodes L + 16 * (dN D + 1 + 1)) _ SKN ltac:(lia)) as [_ SK2].
    eapply stk_agree; [exact SK2 | | exact WM]. intros x Hx. apply OUT. right; left. lia. }
  { destruct (stk_split asegs m _ (al_store L + 8 * dtf D) _ SKS ltac:(lia)) as [SK1 SK23].
    destruct (stk_split asegs m _ (al_store L + 8 * dtf D + 8 * (sz + 1)) _ SK23 ltac:(lia)) as [_ SK3].
    apply (stk_merge asegs m' _ (al_store L + 8 * dtf D)); [| | lia].
    - eapply stk_agree; [exact SK1 | | exact WM]. intros x Hx. apply OUT. right; right. lia.
    - apply (stk_merge asegs m' _ (al_store L + 8 * dtf D + 8 * (sz + 1))); [| | lia].
      + pose proof (stk_of_rw_cells asegs m' _ _ CFA) as SKF. rewrite SF in SKF. exact SKF.
      + eapply stk_agree; [exact SK3 | | exact WM]. intros x Hx. apply OUT. right; right. lia. }
Qed.

Section PUT.
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo T sz pc : Z) (tb : list word) (tr : list Z).
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 1024)%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis A0 : a0 = Z_to_bv 64 T.
  Hypothesis A1 : a1 = Z_to_bv 64 sz.
  Hypothesis SZ1 : sz = (1 + Z.of_nat (length tr))%Z.
  Hypothesis SZ2 : (sz <= 255)%Z.
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis TR : map bv_unsigned (firstn (S (length tr)) tb) = pc :: tr.
  Hypothesis INU : In (pc :: tr) (al_U L).
  Hypothesis SPT : (bv_unsigned sp <= T)%Z.
  Hypothesis T47 : (T + 2040 <= 2^47)%Z.
  Hypothesis AD : ADEPOTi L m.
  Hypothesis LN0 : (AIMG_HI <= al_nodes L)%Z.
  Hypothesis LN1 : (al_nodes L + 1048576 <= ATOP)%Z.
  Hypothesis LS0 : (AIMG_HI <= al_store L)%Z.
  Hypothesis LS1 : (al_store L + 8388608 <= ATOP)%Z.
  Hypothesis RI : rng RNG 0x10000 0x5f3000.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RT : rng RNG T 2040.
  Hypothesis RNODES : rng RNG (al_nodes L) 1048576.
  Hypothesis RSTORE : rng RNG (al_store L) 8388608.

  Notation POST := (depot_put_post L ADEPOTi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="T sz pc tb tr ST ALO LO MI A0 A1 SZ1 SZ2 TB LTB TR INU SPT T47 AD LN0 LN1 LS0 LS1 RI RSTK RT RNODES RSTORE"] Lemma put_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x765e0) fc None m (seg_rom asegs)).
  Proof.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    unfold AIMG_HI in *.
    assert (RSTK' : rng RNG (bv_unsigned sp + -1024) 1024) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SZ : (1 <= sz <= 255)%Z) by lia.
    assert (LU : Z.of_nat (length (pc :: tr)) = sz) by (cbn [length]; lia).
    (* [comment removed for export] *)
    destruct AD as (D & WF & DC & LY). pose proof DC as DC0. pose proof LY as LY0.
    (pose proof WF as ndP__; nd_pre ndP__ 8%nat; intros N1 LK HD ND CMP TF0 TFB NB; nd_post).
    (nd_pre DC 9%nat; intros CTF CPTR CST CNU CMAP CT CN SKN SKS; nd_post).
    unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
    remember (al_nodes L) as NODES eqn:ENODES. remember (al_store L) as STORE eqn:ESTORE.
    pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CNT0.
    pose proof (BUD_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as BUD0.
    remember (dN D) as N eqn:EN. remember (dtf D) as tf eqn:ETF.
    assert (BN : (1 <= N < 65536 /\ 0 <= tf < 1048576)%Z) by lia.
    clear TFB NB CNT0 BUD0.
    (nd_pre LY 7%nat; intros AN AS _ _ _ _ DISJ; nd_post). rewrite <- ENODES in AN. rewrite <- ESTORE in AS, DISJ. box DISJ.
    (* [comment removed for export] *)
    pose proof (mz_init_range sz) as HR0.
    remember (mz_adds (mz_init sz) (pc :: tr)) as HA eqn:EHA.
    pose proof (mz_adds_range (pc :: tr) (mz_init sz) HR0) as HRA. rewrite <- EHA in HRA.
    pose proof (mz_fin_range HA) as HRH. remember (mz_fin HA) as HSH eqn:EHSH.
    assert (HU : hashU (pc :: tr) = HSH).
    { rewrite EHSH, EHA. unfold hashU. rewrite LU. reflexivity. }
    assert (HB : (0 <= bkt HSH < 1048576)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
    remember (bkt HSH) as b0 eqn:EB0.
    pose proof (CT b0 HB) as CB0. destruct (HD b0 HB) as [VR VB]. remember (dhd D b0) as v eqn:EV.
    remember (1639640 + 4 * b0)%Z as BA eqn:EBA.
    remember (NODES + 16 * (N + 1))%Z as NDp eqn:ENDp.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    pose proof (munch_refl [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m) as MU1.
    pose proof (munch_refl (WFINE (bv_unsigned sp) BA NDp FA sz) m) as MU2.
    pose proof (wmono_refl asegs m) as WM.
    subst a0 a1.
    (* [comment removed for export] *)
    do 8 zstep.
    carve_frame 112%nat ST.
    do 16 zstep. zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { exfalso. clear -K1 SZ. rewrite Z.add_0_r in K1. rewrite bv_swrap_small in K1 by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 SPT LO LO0. lia. }
    do 14 zstep.
    (* [comment removed for export] *)
    setreg 12%Z (Z_to_bv 64 (mz_init sz))
      ltac:(f_equal; unfold mz_init;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            reflexivity).
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    setreg 14%Z (Z_to_bv 64 (T + 8 * sz))
      ltac:(f_equal;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 11%Z (Z_to_bv 64 (T + 8 * 0)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (hash_loop RNG) with (m := mc) (tb := tb) (k := Z.to_nat sz) (i := 0%Z);
      [ eassumption | exact LTB | exact SZ | lia | exact RT | lia | lia | exact HR0 | ]
    end.
    intros x15' x16'.
    replace (map bv_unsigned (firstn (Z.to_nat (sz - 0)) (skipn (Z.to_nat 0) tb))) with (pc :: tr)
      by (rewrite <- TR, Z.sub_0_r; replace (Z.to_nat sz) with (S (length tr)) by lia; reflexivity).
    rewrite <- EHA.
    do 16 zstep.
    setreg 19%Z (Z_to_bv 64 (mz_fin HA)) ltac:(reflexivity). rewrite <- EHSH.
    do 3 zstep.
    match goal with |- context [Z.shiftr ?e 42] =>
      replace (Z.shiftr e 42) with (4 * bkt HSH)%Z by (symmetry; first [apply bkt_offset | apply bkt_offset_land]; lia) end.
    rewrite <- EB0. rewrite <- EBA.
    (* [comment removed for export] *)
    zstep. rewrite sx32_lit by lia.
    zstep. zstep. fold_lits. zstep.
    zstep. setreg 25%Z (Z_to_bv 64 v) ltac:(f_equal; change 2147483647%Z with (Z.ones 31); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. fold_lits. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CN1 : forall i, (1 <= i <= N)%Z ->
        rw_cells asegs mc (NODES + 16 * i) [C8 (Z_to_bv 64 (dhs D i)); C4 (Z_to_bv 64 (dlk D i)); C4 (Z_to_bv 64 (dsid D i))])
        by (intros i Hi; apply (rw_cells_transport asegs [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m mc);
            [apply CN; exact Hi | exact MU1 | exact WM | cbn [disjoint_from fst snd cells_size csize Nat.add]; lia])
    end.
    eapply (find_loop RNG) with (N := N) (hs := dhs D) (lk := dlk D) (sid := dsid D) (k := Z.to_nat v) (j := v);
      [ exact HRH | lia | exact CMAP | exact CN1 | unfold AIMG_HI; lia | exact LK
      | intros i Hi; exact (proj1 (ND i Hi)) | exact RI | exact RNODES | lia | lia | |].
    { (* [comment removed for export] *)
      intros j' x11 x12' Hj' Hhs Hin.
      do 13 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold depot_put_post. exists j'. do 15 eexists. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      eapply (adepot_frame L m _ [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z); [exact AD | exact MU1 | assumption |].
      constructor; [| constructor]. cbn [fst snd]. intros a Ha. subst NODES STORE. lia. }
    (* [comment removed for export] *)
    intros x10' x12' FA0. cbv delta [MAP1].
    assert (FA1 : Forall (fun j => dhs D j <> HSH) (chain (dlk D) (dhd D (bkt HSH)))) by (rewrite <- EB0, <- EV; exact FA0).
    pose proof (dwf_absent_budget (al_U L) D (pc :: tr) HSH WF INU HU FA1) as BUDG.
    rewrite LU, <- ETF, <- EN in BUDG. destruct BUDG as [BTF BNN].
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      destruct (stk_split asegs mc _ (NDp + 16) _ SKN ltac:(lia)) as [SKa SKN'];
      destruct (stk_carve asegs mc _ _ 16 SKa ltac:(lia)) as [_ [jn NODEC]];
      replace (NDp + 16 - Z.of_nat 16)%Z with NDp in NODEC by lia;
      apply (rw_cells_split_CB asegs mc NDp [] 16 jn [] [8;4;4]%nat) in NODEC; [| reflexivity]; cbn [mk_CB_cells app] in NODEC;
      destruct (stk_split asegs mc _ FA _ SKS ltac:(lia)) as [SKS1 SKS23];
      destruct (stk_split asegs mc _ (FA + 8 * (sz + 1)) _ SKS23 ltac:(lia)) as [SKSm SKS3];
      destruct (stk_carve asegs mc _ _ (Z.to_nat (8 * (sz + 1))) SKSm ltac:(lia)) as [_ [jf FRC]];
      replace (FA + 8 * (sz + 1) - Z.of_nat (Z.to_nat (8 * (sz + 1))))%Z with FA in FRC by lia;
      apply (rw_cells_split_CB asegs mc FA [] _ jf [] [8; Z.to_nat (8 * sz)]%nat) in FRC; [| cbn [sum_nat]; lia]; cbn [mk_CB_cells app] in FRC
    end.
    clear SKa SKSm MU1 CN1.
    (* [comment removed for export] *)
    zstep. zstep.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (lock_body RNG) with (lo := lo) (B := BA) (v := v);
        [ eassumption | rewrite Hsp; exact ST | rewrite Hsp; lia | unfold AIMG_HI; lia | reflexivity | exact CB0 | lia
        | unfold TAB, NUNIQ; lia | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RI | lia] ]
      | post_call asegs mc ]
    end.
    unname_sp.
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3. lia. }
    (* [comment removed for export] *)
    zstep. zstep. fold_lits. zstep.
    amo_stepW4c. rewrite sx32_lit by lia.
    zstep. rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    zstep. zstep.
    setreg 9%Z (Z_to_bv 64 (N + 1))
      ltac:(f_equal; first [ rewrite Z.mod_small by lia; reflexivity
                           | change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity ]).
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BN. lia. }
    zstep. zstep. shr0.
    zstep. zstep. fold_lits. zstep. zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5 LN0. lia. }
    zstep. setreg 11%Z (Z_to_bv 64 (N + 1)) ltac:(f_equal; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. setreg 9%Z (Z_to_bv 64 NDp) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [FRa FRbc].
    cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 8) with 8%Z in FRbc.
    replace (bv_unsigned sp + -112 + 8)%Z with (bv_unsigned sp + -104)%Z in FRbc by lia.
    apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FRbc. destruct FRbc as [FRb FRc].
    cbn [cells_size csize Nat.add] in FRc. change (Z.of_nat 16) with 16%Z in FRc.
    replace (bv_unsigned sp + -104 + 16)%Z with (bv_unsigned sp + -88)%Z in FRc by lia.
    apply (rw_cells_C8_C4C4 asegs _ _ [_] [] sz) in FRb; [cbn [app] in FRb | lia].
    unbox DISJ.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (nstore_body RNG) with (lo := lo) (NDp := NDp) (AR := (bv_unsigned sp + -104)%Z) (T := T) (sz := sz) (tf := tf)
                                      (STORE := STORE) (HW := Z_to_bv 64 HSH) (tb := tb);
        [ eassumption | rewrite Hsp; eassumption | rewrite Hsp; lia | atop_facts; lia | reflexivity | reflexivity | reflexivity
        | exact FRb | rewrite Hsp; lia | exact NODEC | exact CTF | exact CPTR | exact CST | rewrite EFA in FRC; exact FRC | eassumption | exact LTB | exact SZ
        | lia | lia | unfold AIMG_HI; lia | unfold AIMG_HI; lia | lia
        | exact RI | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK' | lia]
        | eapply rng_sub'; [exact RNODES | lia] | eapply rng_sub'; [exact RSTORE | lia] | exact RT ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; cbv beta delta [nstore_post SSTF SSST] in PO; revert ms' PO; post_call asegs mc ]
    end.
    unname_sp.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    do 13 zstep.
    match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
    release_frame FRa STK (bv_unsigned sp + -104)%Z.
    release_frame FRb STK (bv_unsigned sp + -88)%Z.
    release_frame FRc STK (bv_unsigned sp).
    apply evtF_done. unfold depot_put_post. exists (N + 1)%Z. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros ax Hax. subst NODES STORE. lia. }
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
    exists (dins D b0 HSH v (tf + 1) (Z.of_nat (length (pc :: tr)))). split; [| split; [| exact LY0]].
    - rewrite EB0, EV, EB0. eapply dwf_insert; [exact WF | exact INU | exact HU | reflexivity | rewrite <- EB0, <- EV; exact FA0 | lia].
    - rewrite EB0.
      lazymatch goal with |- dcells _ _ ?mf => eapply (dcells_ins L D m mf (bv_unsigned sp) HSH v (tf + 1)%Z (pc :: tr)) end.
      all: cbv zeta; unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST.
      all: rewrite <- ?ENODES, <- ?ESTORE, <- ?EN, <- ?ETF, ?LU, <- ?EB0.
      all: rewrite <- ?EBA, <- ?ENDp, <- ?EFA.
      all: try assumption. all: try lia.
      { rewrite EFA. eassumption. }
      cbn [cells_size csize Nat.add]. lia.
  Qed.
End PUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem adepot_put : depot_put_stmt ADEPOTi.
Proof. unfold depot_put_stmt. intros. eapply put_body; eassumption. Qed.

Definition adepot_iface : ADepotIface := mkADepotIface ADEPOTi adepot_put adepot_frame.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepotKit__A3W.ADepotKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot1.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma bkt_offset : forall h, (0 <= h)%Z ->
  Z.shiftr ((Z.shiftl h 44) mod 18446744073709551616) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. unfold bkt. rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616%Z with (2^20 * 2^44)%Z.
  rewrite Zmult_mod_distr_r. rewrite Z.shiftr_div_pow2 by lia.
  change (2^44)%Z with (4 * 2^42)%Z. rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
#[using="Type"] Lemma bkt_offset_land : forall h, (0 <= h)%Z ->
  Z.shiftr (Z.land (Z.shiftl h 44) 18446744073709551615) 42 = (4 * bkt h)%Z.
Proof.
  intros h Hh. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2^64)%Z with 18446744073709551616%Z. apply bkt_offset. exact Hh.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amo_add_w_le4_gen : forall tf (c : bv 32), (0 <= tf)%Z -> (tf + bv_unsigned c < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) c))
  = le4 (Z_to_bv 64 (tf + bv_unsigned c)).
Proof.
  intros tf c H0 H2. pose proof (bv_unsigned_in_range 32 c) as HC. unfold bv_modulus in HC. change (2 ^ Z.of_N 32)%Z with (2^32)%Z in HC.
  unfold le4 at 2. rewrite unsigned_lit by lia. f_equal.
  cbn [amo_val]. rewrite bv_add_unsigned.
  assert (E1 : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 tf)))) = tf).
  { rewrite bv_extract_unsigned. rewrite le_bytes_to_word_le4. rewrite unsigned_lit by lia.
    rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite E1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. rewrite Z.mod_small by lia. reflexivity.
Qed.

End CANSEC1.
Ltac amo_stepW4c :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i;
        erewrite amo_add_w_le4_gen;
        [ match goal with |- context [le4 (Z_to_bv 64 (_ + bv_unsigned ?c))] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end;
          mem_after_store_opt
        | lia
        | match goal with |- context [bv_unsigned ?c] =>
            let v := eval vm_compute in (bv_unsigned c) in change (bv_unsigned c) with v end; lia ] ]
    end end
  end.

(* [comment removed for export] *)
Notation WFINE sp BA NDp FA sz :=
  ([(sp + -1024, sp); (BA, BA + 4); (5834968, 5834968 + 4); (NDp, NDp + 16);
    (1575112, 1575112 + 8); (1575136, 1575136 + 4); (FA, FA + 8 * (sz + 1))]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma dcells_ins : forall L D m m' (sp h v sid : Z) (u : list Z) csF,
  let N := dN D in let tf := dtf D in let b0 := bkt h in
  let BA := (TAB + 4 * b0)%Z in let NDp := (al_nodes L + 16 * (N + 1))%Z in let FA := (al_store L + 8 * tf)%Z in
  let sz := Z.of_nat (length u) in
  dcells L D m -> dlayout L -> (ATOP <= sp - 1024)%Z -> (sp <= 2^64)%Z -> (0 <= h)%Z ->
  (1 <= N)%Z -> (16 * (N + 2) <= 1048576)%Z -> (0 <= tf)%Z -> (8 * (tf + sz + 1) <= 8388608)%Z ->
  munch (WFINE sp BA NDp FA sz) m m' -> wmono asegs m m' ->
  rw_cells asegs m' BA [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NUNIQ [C4 (Z_to_bv 64 (N + 1))] ->
  rw_cells asegs m' NDp [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 sid)] ->
  rw_cells asegs m' SSTF [C8 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSST [C4 (Z_to_bv 64 (tf + sz + 1))] ->
  rw_cells asegs m' SSPTR [C8 (Z_to_bv 64 (al_store L))] ->
  rw_cells asegs m' MAP1 [C8 (Z_to_bv 64 (al_nodes L))] ->
  rw_cells asegs m' FA csF -> Z.of_nat (cells_size csF) = (8 * (sz + 1))%Z ->
  dcells L (dins D b0 h v sid sz) m'.
Proof.
  intros L D m m' sp h v sid u csF N tf b0 BA NDp FA sz DC LY SPL SPH Hh N1 NR TF0 TFR MU WM CBA CNU CND CTF CST CPTR CMAP CFA SF.
  assert (HB : (0 <= b0 < 1048576)%Z) by (subst b0; unfold bkt; apply Z.mod_pos_bound; lia).
  (nd_pre DC 9%nat; intros _ _ _ _ _ CT CN SKN SKS; nd_post).
  (pose proof LY as ndP__; nd_pre ndP__ 7%nat; intros _ _ LN0 LN1 LS0 LS1 DISJ; nd_post). unfold AIMG_HI, TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
  subst N tf BA NDp FA.
  (* [comment removed for export] *)
  assert (OUT : forall x,
    ((1640664 <= x < 1640664 + 4 * 1048576 /\ ~ (1640664 + 4 * b0 <= x < 1640664 + 4 * b0 + 4))
     \/ (al_nodes L + 16 <= x < al_nodes L + 1048576 /\ ~ (al_nodes L + 16 * (dN D + 1) <= x < al_nodes L + 16 * (dN D + 1) + 16))
     \/ (al_store L <= x < al_store L + 8388608 /\ ~ (al_store L + 8 * dtf D <= x < al_store L + 8 * dtf D + 8 * (sz + 1))))%Z ->
    m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point _ m m' x MU); [lia|]. cbn [outside]. lia. }
  clear MU.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. cbn [dhd dins]. destruct (Z.eqb_spec b b0) as [->|NE]; [exact CBA|].
    eapply rw_cells_agree; [exact (CT b Hb) | | exact WM]. intros x Hx. apply OUT. unfold TAB in Hx. cbn in Hx. left. lia. }
  split.
  { intros i Hi. cbn [dN dhs dlk dsid dins] in Hi |- *. destruct (Z.eqb_spec i (dN D + 1)) as [->|NE]; [exact CND|].
    eapply rw_cells_agree; [exact (CN i ltac:(lia)) | | exact WM]. intros x Hx. apply OUT. cbn in Hx. right; left. lia. }
  split.
  { cbn [dN dins]. destruct (stk_split asegs m _ (al_nodes L + 16 * (dN D + 1 + 1)) _ SKN ltac:(lia)) as [_ SK2].
    eapply stk_agree; [exact SK2 | | exact WM]. intros x Hx. apply OUT. right; left. lia. }
  { destruct (stk_split asegs m _ (al_store L + 8 * dtf D) _ SKS ltac:(lia)) as [SK1 SK23].
    destruct (stk_split asegs m _ (al_store L + 8 * dtf D + 8 * (sz + 1)) _ SK23 ltac:(lia)) as [_ SK3].
    apply (stk_merge asegs m' _ (al_store L + 8 * dtf D)); [| | lia].
    - eapply stk_agree; [exact SK1 | | exact WM]. intros x Hx. apply OUT. right; right. lia.
    - apply (stk_merge asegs m' _ (al_store L + 8 * dtf D + 8 * (sz + 1))); [| | lia].
      + pose proof (stk_of_rw_cells asegs m' _ _ CFA) as SKF. rewrite SF in SKF. exact SKF.
      + eapply stk_agree; [exact SK3 | | exact WM]. intros x Hx. apply OUT. right; right. lia. }
Qed.

Section PUT.
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo T sz pc : Z) (tb : list word) (tr : list Z).
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ALO : (ATOP <= lo)%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 1024)%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis A0 : a0 = Z_to_bv 64 T.
  Hypothesis A1 : a1 = Z_to_bv 64 sz.
  Hypothesis SZ1 : sz = (1 + Z.of_nat (length tr))%Z.
  Hypothesis SZ2 : (sz <= 255)%Z.
  Hypothesis TB : u64arr asegs m T tb.
  Hypothesis LTB : length tb = 255%nat.
  Hypothesis TR : map bv_unsigned (firstn (S (length tr)) tb) = pc :: tr.
  Hypothesis INU : In (pc :: tr) (al_U L).
  Hypothesis SPT : (bv_unsigned sp <= T)%Z.
  Hypothesis T47 : (T + 2040 <= 2^47)%Z.
  Hypothesis AD : ADEPOTi L m.
  Hypothesis LN0 : (AIMG_HI <= al_nodes L)%Z.
  Hypothesis LN1 : (al_nodes L + 1048576 <= ATOP)%Z.
  Hypothesis LS0 : (AIMG_HI <= al_store L)%Z.
  Hypothesis LS1 : (al_store L + 8388608 <= ATOP)%Z.
  Hypothesis RI : rng RNG 0x10000 0x5f4000.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RT : rng RNG T 2040.
  Hypothesis RNODES : rng RNG (al_nodes L) 1048576.
  Hypothesis RSTORE : rng RNG (al_store L) 8388608.

  Notation POST := (depot_put_post L ADEPOTi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="T sz pc tb tr ST ALO LO MI A0 A1 SZ1 SZ2 TB LTB TR INU SPT T47 AD LN0 LN1 LS0 LS1 RI RSTK RT RNODES RSTORE"] Lemma put_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x76648) fc None m (seg_rom asegs)).
  Proof.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    unfold AIMG_HI in *.
    assert (RSTK' : rng RNG (bv_unsigned sp + -1024) 1024) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SZ : (1 <= sz <= 255)%Z) by lia.
    assert (LU : Z.of_nat (length (pc :: tr)) = sz) by (cbn [length]; lia).
    (* [comment removed for export] *)
    destruct AD as (D & WF & DC & LY). pose proof DC as DC0. pose proof LY as LY0.
    (pose proof WF as ndP__; nd_pre ndP__ 8%nat; intros N1 LK HD ND CMP TF0 TFB NB; nd_post).
    (nd_pre DC 9%nat; intros CTF CPTR CST CNU CMAP CT CN SKN SKS; nd_post).
    unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST in *.
    remember (al_nodes L) as NODES eqn:ENODES. remember (al_store L) as STORE eqn:ESTORE.
    pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CNT0.
    pose proof (BUD_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as BUD0.
    remember (dN D) as N eqn:EN. remember (dtf D) as tf eqn:ETF.
    assert (BN : (1 <= N < 65536 /\ 0 <= tf < 1048576)%Z) by lia.
    clear TFB NB CNT0 BUD0.
    (nd_pre LY 7%nat; intros AN AS _ _ _ _ DISJ; nd_post). rewrite <- ENODES in AN. rewrite <- ESTORE in AS, DISJ. box DISJ.
    (* [comment removed for export] *)
    pose proof (mz_init_range sz) as HR0.
    remember (mz_adds (mz_init sz) (pc :: tr)) as HA eqn:EHA.
    pose proof (mz_adds_range (pc :: tr) (mz_init sz) HR0) as HRA. rewrite <- EHA in HRA.
    pose proof (mz_fin_range HA) as HRH. remember (mz_fin HA) as HSH eqn:EHSH.
    assert (HU : hashU (pc :: tr) = HSH).
    { rewrite EHSH, EHA. unfold hashU. rewrite LU. reflexivity. }
    assert (HB : (0 <= bkt HSH < 1048576)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
    remember (bkt HSH) as b0 eqn:EB0.
    pose proof (CT b0 HB) as CB0. destruct (HD b0 HB) as [VR VB]. remember (dhd D b0) as v eqn:EV.
    remember (1640664 + 4 * b0)%Z as BA eqn:EBA.
    remember (NODES + 16 * (N + 1))%Z as NDp eqn:ENDp.
    remember (STORE + 8 * tf)%Z as FA eqn:EFA.
    pose proof (munch_refl [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m) as MU1.
    pose proof (munch_refl (WFINE (bv_unsigned sp) BA NDp FA sz) m) as MU2.
    pose proof (wmono_refl asegs m) as WM.
    subst a0 a1.
    (* [comment removed for export] *)
    do 8 zstep.
    carve_frame 112%nat ST.
    do 16 zstep. zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { exfalso. clear -K1 SZ. rewrite Z.add_0_r in K1. rewrite bv_swrap_small in K1 by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      rewrite Z.mod_small in K1 by lia. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 SPT LO LO0. lia. }
    do 14 zstep.
    (* [comment removed for export] *)
    setreg 12%Z (Z_to_bv 64 (mz_init sz))
      ltac:(f_equal; unfold mz_init;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            reflexivity).
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    setreg 14%Z (Z_to_bv 64 (T + 8 * sz))
      ltac:(f_equal;
            first [ replace (Z.land sz 4294967295) with sz by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity)
                  | rewrite (Z.mod_small sz 4294967296) by lia
                  | idtac ];
            rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 11%Z (Z_to_bv 64 (T + 8 * 0)) ltac:(f_equal; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply (hash_loop RNG) with (m := mc) (tb := tb) (k := Z.to_nat sz) (i := 0%Z);
      [ eassumption | exact LTB | exact SZ | lia | exact RT | lia | lia | exact HR0 | ]
    end.
    intros x15' x16'.
    replace (map bv_unsigned (firstn (Z.to_nat (sz - 0)) (skipn (Z.to_nat 0) tb))) with (pc :: tr)
      by (rewrite <- TR, Z.sub_0_r; replace (Z.to_nat sz) with (S (length tr)) by lia; reflexivity).
    rewrite <- EHA.
    do 16 zstep.
    setreg 19%Z (Z_to_bv 64 (mz_fin HA)) ltac:(reflexivity). rewrite <- EHSH.
    do 3 zstep.
    match goal with |- context [Z.shiftr ?e 42] =>
      replace (Z.shiftr e 42) with (4 * bkt HSH)%Z by (symmetry; first [apply bkt_offset | apply bkt_offset_land]; lia) end.
    rewrite <- EB0. rewrite <- EBA.
    (* [comment removed for export] *)
    zstep. rewrite sx32_lit by lia.
    zstep. zstep. fold_lits. zstep.
    zstep. setreg 25%Z (Z_to_bv 64 v) ltac:(f_equal; change 2147483647%Z with (Z.ones 31); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. fold_lits. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (CN1 : forall i, (1 <= i <= N)%Z ->
        rw_cells asegs mc (NODES + 16 * i) [C8 (Z_to_bv 64 (dhs D i)); C4 (Z_to_bv 64 (dlk D i)); C4 (Z_to_bv 64 (dsid D i))])
        by (intros i Hi; apply (rw_cells_transport asegs [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z m mc);
            [apply CN; exact Hi | exact MU1 | exact WM | cbn [disjoint_from fst snd cells_size csize Nat.add]; lia])
    end.
    eapply (find_loop RNG) with (N := N) (hs := dhs D) (lk := dlk D) (sid := dsid D) (k := Z.to_nat v) (j := v);
      [ exact HRH | lia | exact CMAP | exact CN1 | unfold AIMG_HI; lia | exact LK
      | intros i Hi; exact (proj1 (ND i Hi)) | exact RI | exact RNODES | lia | lia | |].
    { (* [comment removed for export] *)
      intros j' x11 x12' Hj' Hhs Hin.
      do 13 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold depot_put_post. exists j'. do 15 eexists. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
      eapply (adepot_frame L m _ [(bv_unsigned sp + -1024, bv_unsigned sp)]%Z); [exact AD | exact MU1 | assumption |].
      constructor; [| constructor]. cbn [fst snd]. intros a Ha. subst NODES STORE. lia. }
    (* [comment removed for export] *)
    intros x10' x12' FA0. cbv delta [MAP1].
    assert (FA1 : Forall (fun j => dhs D j <> HSH) (chain (dlk D) (dhd D (bkt HSH)))) by (rewrite <- EB0, <- EV; exact FA0).
    pose proof (dwf_absent_budget (al_U L) D (pc :: tr) HSH WF INU HU FA1) as BUDG.
    rewrite LU, <- ETF, <- EN in BUDG. destruct BUDG as [BTF BNN].
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      destruct (stk_split asegs mc _ (NDp + 16) _ SKN ltac:(lia)) as [SKa SKN'];
      destruct (stk_carve asegs mc _ _ 16 SKa ltac:(lia)) as [_ [jn NODEC]];
      replace (NDp + 16 - Z.of_nat 16)%Z with NDp in NODEC by lia;
      apply (rw_cells_split_CB asegs mc NDp [] 16 jn [] [8;4;4]%nat) in NODEC; [| reflexivity]; cbn [mk_CB_cells app] in NODEC;
      destruct (stk_split asegs mc _ FA _ SKS ltac:(lia)) as [SKS1 SKS23];
      destruct (stk_split asegs mc _ (FA + 8 * (sz + 1)) _ SKS23 ltac:(lia)) as [SKSm SKS3];
      destruct (stk_carve asegs mc _ _ (Z.to_nat (8 * (sz + 1))) SKSm ltac:(lia)) as [_ [jf FRC]];
      replace (FA + 8 * (sz + 1) - Z.of_nat (Z.to_nat (8 * (sz + 1))))%Z with FA in FRC by lia;
      apply (rw_cells_split_CB asegs mc FA [] _ jf [] [8; Z.to_nat (8 * sz)]%nat) in FRC; [| cbn [sum_nat]; lia]; cbn [mk_CB_cells app] in FRC
    end.
    clear SKa SKSm MU1 CN1.
    (* [comment removed for export] *)
    zstep. zstep.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (lock_body RNG) with (lo := lo) (B := BA) (v := v);
        [ eassumption | rewrite Hsp; exact ST | rewrite Hsp; lia | unfold AIMG_HI; lia | reflexivity | exact CB0 | lia
        | unfold TAB, NUNIQ; lia | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RI | lia] ]
      | post_call asegs mc ]
    end.
    unname_sp.
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3. lia. }
    (* [comment removed for export] *)
    zstep. zstep. fold_lits. zstep.
    amo_stepW4c. rewrite sx32_lit by lia.
    zstep. rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    zstep. zstep.
    setreg 9%Z (Z_to_bv 64 (N + 1))
      ltac:(f_equal; first [ rewrite Z.mod_small by lia; reflexivity
                           | change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity ]).
    zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4 BN. lia. }
    zstep. zstep. shr0.
    zstep. zstep. fold_lits. zstep. zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5 LN0. lia. }
    zstep. setreg 11%Z (Z_to_bv 64 (N + 1)) ltac:(f_equal; change 65535%Z with (Z.ones 16); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zstep. zstep. setreg 9%Z (Z_to_bv 64 NDp) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [FRa FRbc].
    cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 8) with 8%Z in FRbc.
    replace (bv_unsigned sp + -112 + 8)%Z with (bv_unsigned sp + -104)%Z in FRbc by lia.
    apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FRbc. destruct FRbc as [FRb FRc].
    cbn [cells_size csize Nat.add] in FRc. change (Z.of_nat 16) with 16%Z in FRc.
    replace (bv_unsigned sp + -104 + 16)%Z with (bv_unsigned sp + -88)%Z in FRc by lia.
    apply (rw_cells_C8_C4C4 asegs _ _ [_] [] sz) in FRb; [cbn [app] in FRb | lia].
    unbox DISJ.
    name_sp sp (-112)%Z.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evtF_cut;
      [ eapply (nstore_body RNG) with (lo := lo) (NDp := NDp) (AR := (bv_unsigned sp + -104)%Z) (T := T) (sz := sz) (tf := tf)
                                      (STORE := STORE) (HW := Z_to_bv 64 HSH) (tb := tb);
        [ eassumption | rewrite Hsp; eassumption | rewrite Hsp; lia | atop_facts; lia | reflexivity | reflexivity | reflexivity
        | exact FRb | rewrite Hsp; lia | exact NODEC | exact CTF | exact CPTR | exact CST | rewrite EFA in FRC; exact FRC | eassumption | exact LTB | exact SZ
        | lia | lia | unfold AIMG_HI; lia | unfold AIMG_HI; lia | lia
        | exact RI | rewrite Hsp; eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RSTK' | lia]
        | eapply rng_sub'; [exact RNODES | lia] | eapply rng_sub'; [exact RSTORE | lia] | exact RT ]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; cbv beta delta [nstore_post SSTF SSST] in PO; revert ms' PO; post_call asegs mc ]
    end.
    unname_sp.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true; cbv iota.
    do 13 zstep.
    match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
    release_frame FRa STK (bv_unsigned sp + -104)%Z.
    release_frame FRb STK (bv_unsigned sp + -88)%Z.
    release_frame FRc STK (bv_unsigned sp).
    apply evtF_done. unfold depot_put_post. exists (N + 1)%Z. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros ax Hax. subst NODES STORE. lia. }
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [lia|].
    exists (dins D b0 HSH v (tf + 1) (Z.of_nat (length (pc :: tr)))). split; [| split; [| exact LY0]].
    - rewrite EB0, EV, EB0. eapply dwf_insert; [exact WF | exact INU | exact HU | reflexivity | rewrite <- EB0, <- EV; exact FA0 | lia].
    - rewrite EB0.
      lazymatch goal with |- dcells _ _ ?mf => eapply (dcells_ins L D m mf (bv_unsigned sp) HSH v (tf + 1)%Z (pc :: tr)) end.
      all: cbv zeta; unfold TAB, NUNIQ, MAP1, SSTF, SSPTR, SSST.
      all: rewrite <- ?ENODES, <- ?ESTORE, <- ?EN, <- ?ETF, ?LU, <- ?EB0.
      all: rewrite <- ?EBA, <- ?ENDp, <- ?EFA.
      all: try assumption. all: try lia.
      { rewrite EFA. eassumption. }
      cbn [cells_size csize Nat.add]. lia.
  Qed.
End PUT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem adepot_put : depot_put_stmt ADEPOTi.
Proof. unfold depot_put_stmt. intros. eapply put_body; eassumption. Qed.

Definition adepot_iface : ADepotIface := mkADepotIface ADEPOTi adepot_put adepot_frame.
End CANSEC2.
End TwB.
End F_adepot.
