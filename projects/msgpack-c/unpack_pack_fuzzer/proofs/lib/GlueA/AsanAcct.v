(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ATsafeCore ATsafeOps.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require AsanInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Actr.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Definition NMAX : nat := Z.to_nat 60000000.
Definition KSH : Z := 69700.
Lemma NMAX_Z : Z.of_nat NMAX = 60000000.
Proof. unfold NMAX. apply Z2Nat.id. lia. Qed.
Lemma KSH0 : 0 <= KSH.
Proof. unfold KSH. lia. Qed.
Lemma HNMAX : 59854610 + KSH <= Z.of_nat NMAX.
Proof. rewrite NMAX_Z. unfold KSH. lia. Qed.
Lemma HLIM : NLK0 + Z.of_nat NMAX * 4096 <= AsanInv.LIMIT.
Proof. rewrite NMAX_Z. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma NoDup_map_on {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  intros INJ ND. induction ND as [|a l Hn ND IH]; cbn [map]; [constructor|].
  constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Ey & Hy). apply Hn.
    rewrite (INJ a y (or_introl eq_refl) (or_intror Hy) (eq_sym Ey)). exact Hy.
  - apply IH. intros x y Hx Hy. apply INJ; right; assumption.
Qed.

Section Acct.
Context {rc : runConstT}.

Definition SHFIX (p : word) : Prop := exists z, sh_cov z /\ p = page_base_of z.
Lemma SHFIX_cov : forall z, sh_cov z -> SHFIX (page_base_of z).
Proof. intros z Hz. exists z. split; [exact Hz| reflexivity]. Qed.

Definition LITPG : list Z := [0x7fffa000; 0x7fffb000; 0x7fffc000; 0x800b7000; 0x800b8000; 0x800b9000; 0x800ba000; 0x800bb000; 0x800bc000; 0x800bd000].

Definition P0 : Z := shad ATOP / 4096 * 4096.
Definition NSTK : nat := Z.to_nat ((Shadow.KHIGH - P0) / 4096).
Definition stkpg (i : nat) : word := Z_to_bv 64 (P0 + 4096 * Z.of_nat i).
Definition SHL : list word := map (Z_to_bv 64) LITPG ++ map stkpg (seq 0 NSTK).

Lemma shad_atop_val : shad ATOP = 2147450880 + ATOP / 8.
Proof. pose proof atop_range as ATR. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by (clear - ATR; lia). reflexivity. Qed.
Lemma P0_range : 0x10006fef8000 <= P0 <= shad ATOP /\ shad ATOP < P0 + 4096 /\ P0 mod 4096 = 0 /\ P0 + 4096 * Z.of_nat NSTK = Shadow.KHIGH /\ Z.of_nat NSTK <= 69633.
Proof.
  pose proof atop_range as ATR. pose proof shad_atop_val as SV. unfold NSTK, P0, Shadow.KHIGH. rewrite SV.
  rewrite Z2Nat.id by (clear - ATR; Z.div_mod_to_equations; lia).
  clear - ATR. Z.div_mod_to_equations. lia.
Qed.

Lemma page_base_of_val : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
Proof.
  intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  Z.div_mod_to_equations. lia.
Qed.

Lemma SHFIX_in : forall p, SHFIX p -> In p SHL.
Proof.
  intros p (z & Hz & ->). pose proof atop_range as ATR. pose proof P0_range as (P1 & P2 & P3 & P4 & P5).
  unfold SHL. apply in_or_app. destruct Hz as [(a' & Ha' & ->)|(v & Hv & Rz)].
  -
    right. assert (SA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof shad_atop_val as SV.
    assert (R : shad ATOP <= shad a' < Shadow.KHIGH) by (rewrite SA, SV; unfold Shadow.KHIGH; clear - Ha' ATR; Z.div_mod_to_equations; lia).
    set (q := shad a' / 4096 * 4096).
    assert (Q : P0 <= q <= shad a' /\ shad a' < q + 4096 /\ q mod 4096 = 0) by (unfold q; clear - R P1 P2 P3; Z.div_mod_to_equations; lia).
    assert (I : 0 <= (q - P0) / 4096 < Z.of_nat NSTK) by (clear - Q R P3 P4; Z.div_mod_to_equations; nia).
    apply in_map_iff. exists (Z.to_nat ((q - P0) / 4096)). split.
    + unfold stkpg. rewrite Z2Nat.id by lia. apply bv_eq. rewrite (page_base_of_val (shad a')) by (unfold Shadow.KHIGH in R; lia).
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, Shadow.KHIGH in *; clear - Q I P1 P4 R; Z.div_mod_to_equations; lia).
      fold q. clear - Q P3. Z.div_mod_to_equations. lia.
    + apply in_seq. lia.
  -
    left. unfold SHLIT, Actr.ActrA.IMGSH, STGSH, PUBSH in Hv. cbn [app In] in Hv.
    assert (R : (0x7fffa000 <= z < 0x7fffc66c) \/ (0x800b7820 <= z < 0x800bdca8)).
    { destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Rz; lia. }
    assert (E : forall c, bv_unsigned (page_base_of z) = c -> In c LITPG -> In (page_base_of z) (map (Z_to_bv 64) LITPG)).
    { intros c Hc Hin. apply in_map_iff. exists c. split; [| exact Hin]. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [symmetry; exact Hc|].
      unfold bv_modulus. unfold LITPG in Hin. cbn [In] in Hin. lia. }
    pose proof (page_base_of_val z ltac:(lia)) as PB.
    destruct R as [R|R].
    + destruct (Z_lt_le_dec z 0x7fffb000); [apply (E 0x7fffa000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x7fffc000); [apply (E 0x7fffb000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      apply (E 0x7fffc000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto].
    + destruct (Z_lt_le_dec z 0x800b8000); [apply (E 0x800b7000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800b9000); [apply (E 0x800b8000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800ba000); [apply (E 0x800b9000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800bb000); [apply (E 0x800ba000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800bc000); [apply (E 0x800bb000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800bd000); [apply (E 0x800bc000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      apply (E 0x800bd000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto].
Qed.

Lemma SHL_nodup : List.NoDup SHL.
Proof.
  pose proof P0_range as (P1 & P2 & P3 & P4 & P5). unfold SHL. apply NoDup_app.
  - apply NoDup_map_on; [| repeat (constructor; [cbn; lia|]); constructor].
    intros x y Hx Hy E. unfold LITPG in Hx, Hy. cbn [In] in Hx, Hy.
    apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; lia). exact E.
  - apply NoDup_map_on; [| apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx. apply in_seq in Hy. unfold stkpg in E.
    apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus, Shadow.KHIGH in *; lia). lia.
  - intros a Ha Hb. apply in_map_iff in Ha as (c & <- & Hc). apply in_map_iff in Hb as (i & Ei & Hi). apply in_seq in Hi.
    unfold LITPG in Hc. cbn [In] in Hc. unfold stkpg in Ei.
    apply (f_equal bv_unsigned) in Ei. rewrite !Z_to_bv_unsigned, !bv_wrap_small in Ei by (unfold bv_modulus, Shadow.KHIGH in *; lia). lia.
Qed.

Theorem SHFIX_fin : abud SHFIX KSH.
Proof.
  pose proof P0_range as (_ & _ & _ & _ & P5).
  exists SHL. split; [exact SHL_nodup|]. split; [| exact SHFIX_in].
  unfold SHL, KSH. rewrite length_app, !length_map, length_seq. cbn [length LITPG]. lia.
Qed.
End Acct.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB ATsafeCore.TwinB ATsafeOps.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Op.TwinB.

Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Definition NMAX : nat := Z.to_nat 60000000.
Definition KSH : Z := 69700.
Lemma NMAX_Z : Z.of_nat NMAX = 60000000.
Proof. unfold NMAX. apply Z2Nat.id. lia. Qed.
Lemma KSH0 : 0 <= KSH.
Proof. unfold KSH. lia. Qed.
Lemma HNMAX : 59854612 + KSH <= Z.of_nat NMAX.
Proof. rewrite NMAX_Z. unfold KSH. lia. Qed.
Lemma HLIM : NLK0 + Z.of_nat NMAX * 4096 <= AsanInv.LIMIT.
Proof. rewrite NMAX_Z. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma NoDup_map_on {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  intros INJ ND. induction ND as [|a l Hn ND IH]; cbn [map]; [constructor|].
  constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Ey & Hy). apply Hn.
    rewrite (INJ a y (or_introl eq_refl) (or_intror Hy) (eq_sym Ey)). exact Hy.
  - apply IH. intros x y Hx Hy. apply INJ; right; assumption.
Qed.

Section Acct.
Context {rc : runConstT}.

Definition SHFIX (p : word) : Prop := exists z, sh_cov z /\ p = page_base_of z.
Lemma SHFIX_cov : forall z, sh_cov z -> SHFIX (page_base_of z).
Proof. intros z Hz. exists z. split; [exact Hz| reflexivity]. Qed.

Definition LITPG : list Z := [0x7fffa000; 0x7fffb000; 0x7fffc000; 0x800b7000; 0x800b8000; 0x800b9000; 0x800ba000; 0x800bb000; 0x800bc000; 0x800bd000; 0x800be000].

Definition P0 : Z := shad ATOP / 4096 * 4096.
Definition NSTK : nat := Z.to_nat ((Shadow.KHIGH - P0) / 4096).
Definition stkpg (i : nat) : word := Z_to_bv 64 (P0 + 4096 * Z.of_nat i).
Definition SHL : list word := map (Z_to_bv 64) LITPG ++ map stkpg (seq 0 NSTK).

Lemma shad_atop_val : shad ATOP = 2147450880 + ATOP / 8.
Proof. pose proof atop_range as ATR. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by (clear - ATR; lia). reflexivity. Qed.
Lemma P0_range : 0x10006fef8000 <= P0 <= shad ATOP /\ shad ATOP < P0 + 4096 /\ P0 mod 4096 = 0 /\ P0 + 4096 * Z.of_nat NSTK = Shadow.KHIGH /\ Z.of_nat NSTK <= 69633.
Proof.
  pose proof atop_range as ATR. pose proof shad_atop_val as SV. unfold NSTK, P0, Shadow.KHIGH. rewrite SV.
  rewrite Z2Nat.id by (clear - ATR; Z.div_mod_to_equations; lia).
  clear - ATR. Z.div_mod_to_equations. lia.
Qed.

Lemma page_base_of_val : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
Proof.
  intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  Z.div_mod_to_equations. lia.
Qed.

Lemma SHFIX_in : forall p, SHFIX p -> In p SHL.
Proof.
  intros p (z & Hz & ->). pose proof atop_range as ATR. pose proof P0_range as (P1 & P2 & P3 & P4 & P5).
  unfold SHL. apply in_or_app. destruct Hz as [(a' & Ha' & ->)|(v & Hv & Rz)].
  -
    right. assert (SA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof shad_atop_val as SV.
    assert (R : shad ATOP <= shad a' < Shadow.KHIGH) by (rewrite SA, SV; unfold Shadow.KHIGH; clear - Ha' ATR; Z.div_mod_to_equations; lia).
    set (q := shad a' / 4096 * 4096).
    assert (Q : P0 <= q <= shad a' /\ shad a' < q + 4096 /\ q mod 4096 = 0) by (unfold q; clear - R P1 P2 P3; Z.div_mod_to_equations; lia).
    assert (I : 0 <= (q - P0) / 4096 < Z.of_nat NSTK) by (clear - Q R P3 P4; Z.div_mod_to_equations; nia).
    apply in_map_iff. exists (Z.to_nat ((q - P0) / 4096)). split.
    + unfold stkpg. rewrite Z2Nat.id by lia. apply bv_eq. rewrite (page_base_of_val (shad a')) by (unfold Shadow.KHIGH in R; lia).
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, Shadow.KHIGH in *; clear - Q I P1 P4 R; Z.div_mod_to_equations; lia).
      fold q. clear - Q P3. Z.div_mod_to_equations. lia.
    + apply in_seq. lia.
  -
    left. unfold SHLIT, Actr.TwinB.ActrA.IMGSH, STGSH, PUBSH in Hv. cbn [app In] in Hv.
    assert (R : (0x7fffa000 <= z < 0x7fffc6a0) \/ (0x800b7c58 <= z < 0x800be0e0)).
    { destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Rz; lia. }
    assert (E : forall c, bv_unsigned (page_base_of z) = c -> In c LITPG -> In (page_base_of z) (map (Z_to_bv 64) LITPG)).
    { intros c Hc Hin. apply in_map_iff. exists c. split; [| exact Hin]. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [symmetry; exact Hc|].
      unfold bv_modulus. unfold LITPG in Hin. cbn [In] in Hin. lia. }
    pose proof (page_base_of_val z ltac:(lia)) as PB.
    destruct R as [R|R].
    + destruct (Z_lt_le_dec z 0x7fffb000); [apply (E 0x7fffa000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x7fffc000); [apply (E 0x7fffb000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      apply (E 0x7fffc000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto].
    + destruct (Z_lt_le_dec z 0x800b8000); [apply (E 0x800b7000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800b9000); [apply (E 0x800b8000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800ba000); [apply (E 0x800b9000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800bb000); [apply (E 0x800ba000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800bc000); [apply (E 0x800bb000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800bd000); [apply (E 0x800bc000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      destruct (Z_lt_le_dec z 0x800be000); [apply (E 0x800bd000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto]|].
      apply (E 0x800be000); [rewrite PB; Z.div_mod_to_equations; lia| cbn; tauto].
Qed.

Lemma SHL_nodup : List.NoDup SHL.
Proof.
  pose proof P0_range as (P1 & P2 & P3 & P4 & P5). unfold SHL. apply NoDup_app.
  - apply NoDup_map_on; [| repeat (constructor; [cbn; lia|]); constructor].
    intros x y Hx Hy E. unfold LITPG in Hx, Hy. cbn [In] in Hx, Hy.
    apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; lia). exact E.
  - apply NoDup_map_on; [| apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx. apply in_seq in Hy. unfold stkpg in E.
    apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus, Shadow.KHIGH in *; lia). lia.
  - intros a Ha Hb. apply in_map_iff in Ha as (c & <- & Hc). apply in_map_iff in Hb as (i & Ei & Hi). apply in_seq in Hi.
    unfold LITPG in Hc. cbn [In] in Hc. unfold stkpg in Ei.
    apply (f_equal bv_unsigned) in Ei. rewrite !Z_to_bv_unsigned, !bv_wrap_small in Ei by (unfold bv_modulus, Shadow.KHIGH in *; lia). lia.
Qed.

Theorem SHFIX_fin : abud SHFIX KSH.
Proof.
  pose proof P0_range as (_ & _ & _ & _ & P5).
  exists SHL. split; [exact SHL_nodup|]. split; [| exact SHFIX_in].
  unfold SHL, KSH. rewrite length_app, !length_map, length_seq. cbn [length LITPG]. lia.
Qed.
End Acct.
End TwinB.
