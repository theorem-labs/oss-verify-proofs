(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma byte_roundtrip : forall b : byte, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range _ b) as Hr. unfold bv_modulus in Hr. cbn in Hr.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma data_byte_cell : forall mem data len bs p,
  data_ok mem data len bs -> (bv_unsigned data <= p)%Z -> (p < bv_unsigned data + len)%Z ->
  rdn segs mem (Z_to_bv 64 p) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 (bs_byte bs (p - bv_unsigned data)))).
Proof.
  intros mem data len bs p (Hlen & Hbs & Hnz & Hhi & Hb) H1 H2.
  cbn [rdn]. replace p with (bv_unsigned data + (p - bv_unsigned data))%Z at 1 by lia.
  rewrite (Hb (p - bv_unsigned data)%Z) by lia.
  unfold bs_byte, word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite byte_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bs_byte_range : forall bs i, (0 <= bs_byte bs i < 256)%Z.
Proof. intros. unfold bs_byte. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
(* [comment removed for export] *)
Lemma mftc_ret_word : forall (gw p cw : word),
  bv_unsigned (alu64 ALU_AND
                 (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (alu64 ALU_SLTU gw (Z_to_bv 64 2))) (Z_to_bv 64 (-1)))
                 (alu64 ALU_SLTU p cw))
  = (if (bv_unsigned gw <? 2)%Z then 0%Z else if (bv_unsigned p <? bv_unsigned cw)%Z then 1%Z else 0%Z).
Proof.
  intros gw p cw.
  rewrite (alu_sltu p cw), (alu_sltu gw). rewrite alu_and, alu_add, m_mul.
  unfold v_and, v_add, v_mul, v_sltu, c_ltu, bv_ltu.
  rewrite (u_lit64a 2). change (2 mod 2 ^ 64)%Z with 2%Z.
  destruct (bv_unsigned gw <? 2)%Z; destruct (bv_unsigned p <? bv_unsigned cw)%Z; rewrite !u_lit64a; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma u_add64 : forall x y : word,
  bv_unsigned (alu64 ALU_ADD x y) = ((bv_unsigned x + bv_unsigned y) mod 2 ^ 64)%Z.
Proof. intros. rewrite alu_add. unfold v_add. apply u_lit64a. Qed.

Lemma u_sub64 : forall x y : word,
  bv_unsigned (alu64 ALU_SUB x y) = ((bv_unsigned x - bv_unsigned y) mod 2 ^ 64)%Z.
Proof. intros. rewrite alu_sub. unfold v_sub. apply u_lit64a. Qed.

Lemma u_mul64 : forall x y : word,
  bv_unsigned (mul_div M_MUL x y) = ((bv_unsigned x * bv_unsigned y) mod 2 ^ 64)%Z.
Proof. intros. rewrite m_mul. unfold v_mul. apply u_lit64a. Qed.

(* [comment removed for export] *)
Lemma ext_val_zx_id4 : forall v : word, (bv_unsigned v < 4294967296)%Z -> ext_val false 0 4 v = v.
Proof. intros v Hv. apply ext_val_zx_id. exact Hv. Qed.
Lemma ext_val_zx_id1 : forall v : word, (bv_unsigned v < 256)%Z -> ext_val false 0 1 v = v.
Proof. intros v Hv. apply ext_val_zx_id. exact Hv. Qed.

(* [comment removed for export] *)
Lemma mul_bnd : forall x y bx by_ : Z,
  (0 <= x <= bx)%Z -> (0 <= y <= by_)%Z -> (0 <= x * y <= bx * by_)%Z.
Proof. intros. nia. Qed.

(* [comment removed for export] *)
Lemma zprod_len1 : forall l, Z.of_nat (length l) = 1%Z -> zprod l = nth 0 l 0%Z.
Proof. intros [|a [|b l]] H; cbn in H |- *; lia. Qed.
Lemma zprod_len2 : forall l, Z.of_nat (length l) = 2%Z -> zprod l = (nth 0 l 0 * nth 1 l 0)%Z.
Proof. intros [|a [|b [|c l]]] H; cbn -[Z.mul] in H |- *; try lia. Qed.
Lemma zprod_len3 : forall l, Z.of_nat (length l) = 3%Z -> zprod l = (nth 0 l 0 * (nth 1 l 0 * nth 2 l 0))%Z.
Proof. intros [|a [|b [|c [|d l]]]] H; cbn -[Z.mul] in H |- *; try lia. Qed.
Lemma zprod_len4 : forall l, Z.of_nat (length l) = 4%Z ->
  zprod l = (nth 0 l 0 * (nth 1 l 0 * (nth 2 l 0 * nth 3 l 0)))%Z.
Proof. intros [|a [|b [|c [|d [|e l]]]]] H; cbn -[Z.mul] in H |- *; try lia. Qed.
(* [comment removed for export] *)
Lemma mod_cases2 : forall x m : Z, (0 < m)%Z -> (0 <= x < 2 * m)%Z ->
  ((x < m /\ x mod m = x) \/ (m <= x /\ x mod m = x - m))%Z.
Proof.
  intros x m Hm Hx. destruct (Z_lt_le_dec x m) as [Hl|Hg].
  - left. split; [lia|]. apply Z.mod_small. lia.
  - right. split; [lia|]. rewrite <- (Z.mod_add x (-1) m) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod_cases3 : forall x m : Z, (0 < m)%Z -> (- m <= x < 2 * m)%Z ->
  ((x < 0 /\ x mod m = x + m) \/ (0 <= x < m /\ x mod m = x) \/ (m <= x /\ x mod m = x - m))%Z.
Proof.
  intros x m Hm Hx. destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - left. split; [lia|]. rewrite <- (Z.mod_add x 1 m) by lia. rewrite Z.mod_small by lia. lia.
  - right. destruct (mod_cases2 x m Hm ltac:(lia)) as [[A B]|[A B]]; [left|right]; split; lia.
Qed.

Lemma zmod_neg : forall x m : Z, (0 < m)%Z -> (- m <= x < 0)%Z -> (x mod m = x + m)%Z.
Proof.
  intros x m Hm Hx. rewrite <- (Z.mod_add x 1 m) by lia. rewrite Z.mod_small by lia. lia.
Qed.

End WithSegs.

(* [comment removed for export] *)
Ltac mod2_split :=
  repeat match goal with
  | |- context [ (?x mod ?m)%Z ] =>
      lazymatch x with context [ (_ mod _)%Z ] => fail | _ =>
        let H := fresh in let R := fresh in
        first
          [ rewrite (Z.mod_small x m) by lia
          | rewrite (zmod_neg x m) by lia
          | destruct (mod_cases2 x m ltac:(lia) ltac:(lia)) as [[R H]|[R H]]; rewrite H; clear H
          | destruct (mod_cases3 x m ltac:(lia) ltac:(lia)) as [[R H]|[[R H]|[R H]]]; rewrite H; clear H ]
      end
  end.
