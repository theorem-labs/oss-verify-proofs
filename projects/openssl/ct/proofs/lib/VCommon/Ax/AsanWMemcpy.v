(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMcStep AsanWMemset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MC_WORDS : list (Z * Z) :=
  [(0x0, 0x0035f693); (0x4, 0x10068863); (0x114, 0x00050693); (0x118, 0x00357793); (0x11c, 0xf2079ae3);
   (0x120, 0x01000713); (0x124, 0x02e66c63); (0x128, 0x00f00713); (0x12c, 0x0005a783); (0x130, 0x0045a803);
   (0x134, 0x0085a883); (0x138, 0x00c5a283); (0x13c, 0x01058593); (0x140, 0xff060613); (0x144, 0x00f6a023);
   (0x148, 0x0106a223); (0x14c, 0x0116a423); (0x150, 0x0056a623); (0x154, 0x01068693); (0x158, 0xfcc76ae3);
   (0x15c, 0x00800713); (0x160, 0x00e66e63); (0x164, 0x0005a703); (0x168, 0x0045a783); (0x16c, 0x00e6a023);
   (0x170, 0x00f6a223); (0x174, 0x00868693); (0x178, 0x00858593); (0x17c, 0x00467713); (0x180, 0x24070063);
   (0x184, 0x0005a703); (0x188, 0x00458593); (0x18c, 0x00e6a023); (0x190, 0x00468693); (0x194, 0x22c0006f);
   (0x3c0, 0x00267713); (0x3c4, 0x00071863); (0x3c8, 0x00167613); (0x3cc, 0x02061663); (0x3d0, 0x00008067);
   (0x3d4, 0x0005c703); (0x3d8, 0x0015c783); (0x3dc, 0x00258593); (0x3e0, 0x00268813); (0x3e4, 0x00e68023);
   (0x3e8, 0x00f680a3); (0x3ec, 0x00080693); (0x3f0, 0x00167613); (0x3f4, 0xfc060ee3); (0x3f8, 0x0005c583);
   (0x3fc, 0x00b68023); (0x400, 0x00008067)]%Z.

Local Ltac dec := wdec.
Lemma DC_0   : decode_any (Z_to_bv 32 0x0035f693) = Some (OpImm ALU_AND 13 11 3, 4%Z). Proof. dec. Qed.
Lemma DC_4   : decode_any (Z_to_bv 32 0x10068863) = Some (Branch BC_EQ 13 0 272, 4%Z). Proof. dec. Qed.
Lemma DC_114 : decode_any (Z_to_bv 32 0x00050693) = Some (OpImm ALU_ADD 13 10 0, 4%Z). Proof. dec. Qed.
Lemma DC_118 : decode_any (Z_to_bv 32 0x00357793) = Some (OpImm ALU_AND 15 10 3, 4%Z). Proof. dec. Qed.
Lemma DC_11c : decode_any (Z_to_bv 32 0xf2079ae3) = Some (Branch BC_NE 15 0 7988, 4%Z). Proof. dec. Qed.
Lemma DC_120 : decode_any (Z_to_bv 32 0x01000713) = Some (OpImm ALU_ADD 14 0 16, 4%Z). Proof. dec. Qed.
Lemma DC_124 : decode_any (Z_to_bv 32 0x02e66c63) = Some (Branch BC_LTU 12 14 56, 4%Z). Proof. dec. Qed.
Lemma DC_128 : decode_any (Z_to_bv 32 0x00f00713) = Some (OpImm ALU_ADD 14 0 15, 4%Z). Proof. dec. Qed.
Lemma DC_12c : decode_any (Z_to_bv 32 0x0005a783) = Some (Load SZ4 true 15 11 0, 4%Z). Proof. dec. Qed.
Lemma DC_130 : decode_any (Z_to_bv 32 0x0045a803) = Some (Load SZ4 true 16 11 4, 4%Z). Proof. dec. Qed.
Lemma DC_134 : decode_any (Z_to_bv 32 0x0085a883) = Some (Load SZ4 true 17 11 8, 4%Z). Proof. dec. Qed.
Lemma DC_138 : decode_any (Z_to_bv 32 0x00c5a283) = Some (Load SZ4 true 5 11 12, 4%Z). Proof. dec. Qed.
Lemma DC_13c : decode_any (Z_to_bv 32 0x01058593) = Some (OpImm ALU_ADD 11 11 16, 4%Z). Proof. dec. Qed.
Lemma DC_140 : decode_any (Z_to_bv 32 0xff060613) = Some (OpImm ALU_ADD 12 12 4080, 4%Z). Proof. dec. Qed.
Lemma DC_144 : decode_any (Z_to_bv 32 0x00f6a023) = Some (Store SZ4 13 15 0, 4%Z). Proof. dec. Qed.
Lemma DC_148 : decode_any (Z_to_bv 32 0x0106a223) = Some (Store SZ4 13 16 4, 4%Z). Proof. dec. Qed.
Lemma DC_14c : decode_any (Z_to_bv 32 0x0116a423) = Some (Store SZ4 13 17 8, 4%Z). Proof. dec. Qed.
Lemma DC_150 : decode_any (Z_to_bv 32 0x0056a623) = Some (Store SZ4 13 5 12, 4%Z). Proof. dec. Qed.
Lemma DC_154 : decode_any (Z_to_bv 32 0x01068693) = Some (OpImm ALU_ADD 13 13 16, 4%Z). Proof. dec. Qed.
Lemma DC_158 : decode_any (Z_to_bv 32 0xfcc76ae3) = Some (Branch BC_LTU 14 12 8148, 4%Z). Proof. dec. Qed.
Lemma DC_15c : decode_any (Z_to_bv 32 0x00800713) = Some (OpImm ALU_ADD 14 0 8, 4%Z). Proof. dec. Qed.
Lemma DC_160 : decode_any (Z_to_bv 32 0x00e66e63) = Some (Branch BC_LTU 12 14 28, 4%Z). Proof. dec. Qed.
Lemma DC_164 : decode_any (Z_to_bv 32 0x0005a703) = Some (Load SZ4 true 14 11 0, 4%Z). Proof. dec. Qed.
Lemma DC_168 : decode_any (Z_to_bv 32 0x0045a783) = Some (Load SZ4 true 15 11 4, 4%Z). Proof. dec. Qed.
Lemma DC_16c : decode_any (Z_to_bv 32 0x00e6a023) = Some (Store SZ4 13 14 0, 4%Z). Proof. dec. Qed.
Lemma DC_170 : decode_any (Z_to_bv 32 0x00f6a223) = Some (Store SZ4 13 15 4, 4%Z). Proof. dec. Qed.
Lemma DC_174 : decode_any (Z_to_bv 32 0x00868693) = Some (OpImm ALU_ADD 13 13 8, 4%Z). Proof. dec. Qed.
Lemma DC_178 : decode_any (Z_to_bv 32 0x00858593) = Some (OpImm ALU_ADD 11 11 8, 4%Z). Proof. dec. Qed.
Lemma DC_17c : decode_any (Z_to_bv 32 0x00467713) = Some (OpImm ALU_AND 14 12 4, 4%Z). Proof. dec. Qed.
Lemma DC_180 : decode_any (Z_to_bv 32 0x24070063) = Some (Branch BC_EQ 14 0 576, 4%Z). Proof. dec. Qed.
Lemma DC_188 : decode_any (Z_to_bv 32 0x00458593) = Some (OpImm ALU_ADD 11 11 4, 4%Z). Proof. dec. Qed.
Lemma DC_190 : decode_any (Z_to_bv 32 0x00468693) = Some (OpImm ALU_ADD 13 13 4, 4%Z). Proof. dec. Qed.
Lemma DC_194 : decode_any (Z_to_bv 32 0x22c0006f) = Some (Jal 0 556, 4%Z). Proof. dec. Qed.
Lemma DC_3c0 : decode_any (Z_to_bv 32 0x00267713) = Some (OpImm ALU_AND 14 12 2, 4%Z). Proof. dec. Qed.
Lemma DC_3c4 : decode_any (Z_to_bv 32 0x00071863) = Some (Branch BC_NE 14 0 16, 4%Z). Proof. dec. Qed.
Lemma DC_3c8 : decode_any (Z_to_bv 32 0x00167613) = Some (OpImm ALU_AND 12 12 1, 4%Z). Proof. dec. Qed.
Lemma DC_3cc : decode_any (Z_to_bv 32 0x02061663) = Some (Branch BC_NE 12 0 44, 4%Z). Proof. dec. Qed.
Lemma DC_3d0 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. dec. Qed.
Lemma DC_3d4 : decode_any (Z_to_bv 32 0x0005c703) = Some (Load SZ1 false 14 11 0, 4%Z). Proof. dec. Qed.
Lemma DC_3d8 : decode_any (Z_to_bv 32 0x0015c783) = Some (Load SZ1 false 15 11 1, 4%Z). Proof. dec. Qed.
Lemma DC_3dc : decode_any (Z_to_bv 32 0x00258593) = Some (OpImm ALU_ADD 11 11 2, 4%Z). Proof. dec. Qed.
Lemma DC_3e0 : decode_any (Z_to_bv 32 0x00268813) = Some (OpImm ALU_ADD 16 13 2, 4%Z). Proof. dec. Qed.
Lemma DC_3e4 : decode_any (Z_to_bv 32 0x00e68023) = Some (Store SZ1 13 14 0, 4%Z). Proof. dec. Qed.
Lemma DC_3e8 : decode_any (Z_to_bv 32 0x00f680a3) = Some (Store SZ1 13 15 1, 4%Z). Proof. dec. Qed.
Lemma DC_3ec : decode_any (Z_to_bv 32 0x00080693) = Some (OpImm ALU_ADD 13 16 0, 4%Z). Proof. dec. Qed.
Lemma DC_3f4 : decode_any (Z_to_bv 32 0xfc060ee3) = Some (Branch BC_EQ 12 0 8156, 4%Z). Proof. dec. Qed.
Lemma DC_3f8 : decode_any (Z_to_bv 32 0x0005c583) = Some (Load SZ1 false 11 11 0, 4%Z). Proof. dec. Qed.
Lemma DC_3fc : decode_any (Z_to_bv 32 0x00b68023) = Some (Store SZ1 13 11 0, 4%Z). Proof. dec. Qed.

Record MCCode (segs : list Segment) (e : Z) : Prop := {
  mcc_W : words_ok segs e MC_WORDS = true;
  mcc_bnd : (0 <= e /\ e + 0x404 <= 2 ^ 47 /\ e mod 4 = 0)%Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wrap_swrap : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
Proof. intros n z. unfold bv_swrap, bv_wrap. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

Lemma store4_load4 : forall (l : list byte), length l = 4%nat -> store_bytes SZ4 (load_word SZ4 true l) = l.
Proof.
  intros l Hl. cbn [store_bytes load_word].
  pose proof (bytes_le_to_Z_nonneg l) as H0. pose proof (bytes_le_to_Z_bound l) as H1. rewrite Hl in H1.
  change (8 * Z.of_nat 4)%Z with 32%Z in H1.
  assert (E : bv_unsigned (low32 (sext 64 (bv_extract 0 32 (le_bytes_to_word l)))) = bytes_le_to_Z l).
  { unfold low32, sext, le_bytes_to_word.
    rewrite bv_extract_unsigned, Z.shiftr_0_r, bv_sign_extend_unsigned.
    rewrite bv_wrap_bv_wrap by lia. unfold bv_signed. rewrite wrap_swrap.
    rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
    rewrite ?(Z.mod_small (bytes_le_to_Z l) (2 ^ 64)) by lia. rewrite !(Z.mod_small (bytes_le_to_Z l) (2 ^ 32)) by lia. reflexivity. }
  rewrite E. pose proof (Z_to_le_bytes_lez l) as F. rewrite Hl in F. exact F.
Qed.

Lemma store1_load1b : forall (b : byte), store_bytes SZ1 (load_word SZ1 false [b]) = [b].
Proof.
  intros b. cbn [store_bytes load_word Z_to_le_bytes]. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold zext, le_bytes_to_word. rewrite !bv_extract_unsigned, !Z.shiftr_0_r, bv_zero_extend_unsigned by lia.
  rewrite !bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite !bv_wrap_bv_wrap by lia. apply bv_wrap_bv_unsigned.
Qed.

Lemma store1_load1 : forall (l : list byte), length l = 1%nat -> store_bytes SZ1 (load_word SZ1 false l) = l.
Proof. intros l Hl. destruct l as [|b [|b' r]]; cbn in Hl; try lia. apply store1_load1b. Qed.

(* [comment removed for export] *)
Definition copied (m m0 : word -> option byte) (lo k : Z) (bs : list byte) : Prop :=
  forall x : word, ((lo <= bv_unsigned x < lo + k)%Z -> m x = Some (nth (Z.to_nat (bv_unsigned x - lo)) bs (Z_to_bv 8 0)))
              /\ (~ (lo <= bv_unsigned x < lo + k)%Z -> m x = m0 x).

Lemma copied_refl : forall m lo bs, copied m m lo 0 bs.
Proof. intros m lo bs x. split; [lia | reflexivity]. Qed.

Lemma copied_grows : forall m m0 lo k bs, copied m m0 lo k bs -> mem_grows m0 m.
Proof.
  intros m m0 lo k bs H x Hx. destruct (H x) as [H1 H2].
  destruct (Z_le_gt_dec lo (bv_unsigned x)); [destruct (Z_lt_le_dec (bv_unsigned x) (lo + k))|].
  - rewrite H1 by lia. discriminate.
  - rewrite H2 by lia. exact Hx.
  - rewrite H2 by lia. exact Hx.
Qed.

Lemma w2m_chunk : forall (l : list byte) m (a : Z) (x : word),
  (0 <= a)%Z -> (a + Z.of_nat (length l) <= 2 ^ 64)%Z ->
  write_to_mem m (Z_to_bv 64 a) l x
  = if ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat (length l)))%bool
    then Some (nth (Z.to_nat (bv_unsigned x - a)) l (Z_to_bv 8 0)) else m x.
Proof.
  induction l as [|b l IH]; intros m a x Ha Hal.
  - cbn [write_to_mem length]. replace ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat 0))%bool with false
      by (symmetry; apply andb_false_iff; destruct (Z.leb_spec a (bv_unsigned x)); [right; apply Z.ltb_ge; lia | left; reflexivity]).
    reflexivity.
  - cbn [write_to_mem length] in *. pose proof (u64_range x).
    destruct l as [|b' l'].
    + cbn [write_to_mem length] in *. destruct (bv_eqb x (Z_to_bv 64 a)) eqn:E.
      * apply bv_eqb_true_eq in E. subst x. rewrite bvu_z by lia.
        replace ((a <=? a) && (a <? a + Z.of_nat 1))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        rewrite Z.sub_diag. reflexivity.
      * replace ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat 1))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct (Z.leb_spec a (bv_unsigned x)); [right|left; reflexivity].
        apply Z.ltb_ge. destruct (Z.eq_dec (bv_unsigned x) a) as [Ex|Ex]; [|lia].
        exfalso. assert (x = Z_to_bv 64 a) by (apply bv_eq; rewrite bvu_z by lia; exact Ex). subst x.
        rewrite bv_eqb_refl in E. discriminate.
    + replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (rewrite <- zw_add; reflexivity).
      rewrite IH by (cbn [length] in *; lia). cbv beta. cbn [length] in *.
      destruct (bv_eqb x (Z_to_bv 64 a)) eqn:E.
      * apply bv_eqb_true_eq in E. subst x. rewrite bvu_z by lia.
        replace ((a + 1 <=? a) && (a <? a + 1 + Z.of_nat (S (length l'))))%bool with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
        replace ((a <=? a) && (a <? a + Z.of_nat (S (S (length l')))))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        rewrite Z.sub_diag. reflexivity.
      * assert (Hne : bv_unsigned x <> a).
        { intros Ex. assert (x = Z_to_bv 64 a) by (apply bv_eq; rewrite bvu_z by lia; exact Ex). subst x.
          rewrite bv_eqb_refl in E. discriminate. }
        destruct (Z.leb_spec (a + 1) (bv_unsigned x)); destruct (Z.leb_spec a (bv_unsigned x));
          destruct (Z.ltb_spec (bv_unsigned x) (a + 1 + Z.of_nat (S (length l')))); destruct (Z.ltb_spec (bv_unsigned x) (a + Z.of_nat (S (S (length l')))));
          cbn [andb]; try reflexivity; try lia.
        replace (Z.to_nat (bv_unsigned x - a)) with (S (Z.to_nat (bv_unsigned x - (a + 1)))) by lia. reflexivity.
Qed.

Lemma copied_step : forall m m0 (lo k : Z) bs (c : nat),
  (0 <= lo)%Z -> (0 <= k)%Z -> (k + Z.of_nat c <= Z.of_nat (length bs))%Z -> (lo + k + Z.of_nat c <= 2 ^ 64)%Z ->
  copied m m0 lo k bs ->
  copied (write_to_mem m (Z_to_bv 64 (lo + k)) (firstn c (skipn (Z.to_nat k) bs))) m0 lo (k + Z.of_nat c) bs.
Proof.
  intros m m0 lo k bs c Hlo Hk Hc Hnw H x.
  assert (Hlen : length (firstn c (skipn (Z.to_nat k) bs)) = c) by (rewrite length_firstn, length_skipn; lia).
  rewrite w2m_chunk by (rewrite ?Hlen; lia). rewrite Hlen. destruct (H x) as [H1 H2].
  destruct (Z.leb_spec (lo + k) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (lo + k + Z.of_nat c)); cbn [andb].
  - split; [|intros Hn; exfalso; lia]. intros _. f_equal. rewrite nth_firstn, nth_skipn. rewrite (proj2 (Nat.ltb_lt _ _)) by lia.
    f_equal. lia.
  - split; [intros; exfalso; lia | intros; apply H2; lia].
  - split; [intros; apply H1; lia | intros; apply H2; lia].
  - split; [intros; apply H1; lia | intros; apply H2; lia].
Qed.

(* [comment removed for export] *)
Local Ltac r16 r :=
  let H := fresh in
  assert (H : (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9
               \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15)%Z) by lia;
  repeat (destruct H as [H|H]; [subst r; vm_compute; intuition discriminate|]); subst r; vm_compute; intuition discriminate.

Lemma b8_lt : forall r, (0 <= r < 8)%Z -> (r mod 8 = r)%Z.
Proof. intros r Hr. apply Z.mod_small. lia. Qed.
Lemma b8_ge : forall r, (8 <= r < 16)%Z -> (r mod 8 = r - 8)%Z.
Proof. intros r Hr. replace r with (r - 8 + 1 * 8)%Z at 1 by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. Qed.
Lemma b4_0 : forall r, (0 <= r < 16)%Z -> Z.land r 4 = 0%Z -> (r mod 4 = r mod 8 /\ 0 <= r mod 8 < 4)%Z.
Proof. intros r Hr. r16 r. Qed.
Lemma b4_1 : forall r, (0 <= r < 16)%Z -> Z.land r 4 <> 0%Z -> (r mod 4 = r mod 8 - 4 /\ 4 <= r mod 8 < 8)%Z.
Proof. intros r Hr. r16 r. Qed.
(* [comment removed for export] *)
Local Ltac r32 r :=
  let H := fresh in
  assert (H : (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9
               \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19
               \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29
               \/ r = 30 \/ r = 31)%Z) by lia;
  repeat (destruct H as [H|H]; [subst r; vm_compute; intuition discriminate|]); subst r; vm_compute; intuition discriminate.

Lemma b2_0 : forall r, (0 <= r < 32)%Z -> Z.land r 2 = 0%Z -> (r mod 2 = r mod 4 /\ 0 <= r mod 4 < 2)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma b2_1 : forall r, (0 <= r < 32)%Z -> Z.land r 2 <> 0%Z -> (r mod 2 = r mod 4 - 2 /\ 2 <= r mod 4 < 4)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma b1_0 : forall r, (0 <= r < 32)%Z -> Z.land r 1 = 0%Z -> (r mod 2 = 0)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma b1_1 : forall r, (0 <= r < 32)%Z -> Z.land r 1 <> 0%Z -> (r mod 2 = 1)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma land3_mod4 : forall a, (0 <= a)%Z -> (a mod 4 = 0)%Z -> Z.land a 3 = 0%Z.
Proof. intros a Ha H. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma alu_andi_z : forall (a : Z) (imm : bv 12), (0 <= a < 2 ^ 64)%Z -> (0 <= bv_signed imm)%Z ->
  alu64 ALU_AND (Z_to_bv 64 a) (sext 64 imm) = Z_to_bv 64 (Z.land a (bv_signed imm)).
Proof.
  intros a imm Ha Hi. rewrite sext64_Z_to_bv. apply bv_eq. cbv [alu64 alu].
  pose proof (bv_signed_in_range _ imm ltac:(lia)) as Hr. change (bv_half_modulus 12) with 2048%Z in Hr.
  rewrite bv_and_unsigned, !bvu_z by (try apply Z_land_range; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition MC_CLOB : list reg := [5; 11; 12; 13; 14; 15; 16; 17].

Record MCRc (CL : list reg) (ms0 ms : machine_state) : Prop := {
  mcr_svc : ms_svc_pending ms = None;
  mcr_rom : ms_rom ms = ms_rom ms0;
  mcr_fregs : ms_fregs ms = ms_fregs ms0;
  mcr_fcsr : ms_fcsr ms = ms_fcsr ms0;
  mcr_resv : ms_resv ms = ms_resv ms0 \/ ms_resv ms = None;
  mcr_regs : forall r, ~ In r CL -> rg ms r = rg ms0 r
}.

(* [comment removed for export] *)
Abbreviation MCR := (MCRc MC_CLOB).

Lemma MCR_refl : forall CL S, ms_svc_pending S = None -> MCRc CL S S.
Proof.
  intros CL S H. constructor; [exact H | reflexivity | reflexivity | reflexivity | left; reflexivity | intros; reflexivity].
Qed.

Lemma MCR_setx : forall CL ms0 S rd v p r m,
  MCRc CL ms0 S -> (rd = 0 \/ In rd CL) -> r = ms_resv S -> m = ms_mem S -> MCRc CL ms0 (setx S rd v p r m).
Proof.
  intros CL ms0 S rd v p r m [H1 H2 H3 H4 H5 H6] Hrd -> ->.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | exact H5 |].
  intros r0 Hr0. rewrite <- (H6 r0 Hr0).
  destruct Hrd as [->|Hin]; [apply rg_setx_x0|]. apply rg_setx_other. intros ->. exact (Hr0 Hin).
Qed.

Lemma MCR_store : forall CL ms0 S v p (a : word) r m,
  MCRc CL ms0 S -> r = inval a (ms_resv S) -> MCRc CL ms0 (setx S 0 v p r m).
Proof.
  intros CL ms0 S v p a r m [H1 H2 H3 H4 H5 H6] ->.
  constructor; [reflexivity | exact H2 | exact H3 | exact H4 | | ].
  - rewrite resv_setx. destruct (inval_cases a (ms_resv S)) as [E|E]; rewrite E; [exact H5 | right; reflexivity].
  - intros r0 Hr0. rewrite rg_setx_x0. exact (H6 r0 Hr0).
Qed.

Ltac in_lit := cbn [In MC_CLOB]; repeat first [ left; reflexivity | right ].
Ltac in_clob :=
  first [ solve [ in_lit ]
        | match goal with H : forall r, In r MC_CLOB -> In r ?CL |- In _ ?CL => apply H; solve [ in_lit ] end ].
Ltac mcr_chain HS :=
  repeat first
   [ (eapply MCR_store; [ | reflexivity ])
   | (eapply MCR_setx; [ | first [ left; reflexivity | right; in_clob ]
                      | reflexivity | reflexivity ]) ];
  exact HS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MCW.
Variable segs : list Segment.
Variable e : Z.
Hypothesis HC : MCCode segs e.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs e MC_WORDS); [exact (mcc_W _ _ HC) | inw | lia].

Lemma FC_0   : fetch_word segs (pcw e 0x0)   = Some (Z_to_bv 32 0x0035f693). Proof. fw. Qed.
Lemma FC_4   : fetch_word segs (pcw e 0x4)   = Some (Z_to_bv 32 0x10068863). Proof. fw. Qed.
Lemma FC_114 : fetch_word segs (pcw e 0x114) = Some (Z_to_bv 32 0x00050693). Proof. fw. Qed.
Lemma FC_118 : fetch_word segs (pcw e 0x118) = Some (Z_to_bv 32 0x00357793). Proof. fw. Qed.
Lemma FC_11c : fetch_word segs (pcw e 0x11c) = Some (Z_to_bv 32 0xf2079ae3). Proof. fw. Qed.
Lemma FC_120 : fetch_word segs (pcw e 0x120) = Some (Z_to_bv 32 0x01000713). Proof. fw. Qed.
Lemma FC_124 : fetch_word segs (pcw e 0x124) = Some (Z_to_bv 32 0x02e66c63). Proof. fw. Qed.
Lemma FC_128 : fetch_word segs (pcw e 0x128) = Some (Z_to_bv 32 0x00f00713). Proof. fw. Qed.
Lemma FC_12c : fetch_word segs (pcw e 0x12c) = Some (Z_to_bv 32 0x0005a783). Proof. fw. Qed.
Lemma FC_130 : fetch_word segs (pcw e 0x130) = Some (Z_to_bv 32 0x0045a803). Proof. fw. Qed.
Lemma FC_134 : fetch_word segs (pcw e 0x134) = Some (Z_to_bv 32 0x0085a883). Proof. fw. Qed.
Lemma FC_138 : fetch_word segs (pcw e 0x138) = Some (Z_to_bv 32 0x00c5a283). Proof. fw. Qed.
Lemma FC_13c : fetch_word segs (pcw e 0x13c) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FC_140 : fetch_word segs (pcw e 0x140) = Some (Z_to_bv 32 0xff060613). Proof. fw. Qed.
Lemma FC_144 : fetch_word segs (pcw e 0x144) = Some (Z_to_bv 32 0x00f6a023). Proof. fw. Qed.
Lemma FC_148 : fetch_word segs (pcw e 0x148) = Some (Z_to_bv 32 0x0106a223). Proof. fw. Qed.
Lemma FC_14c : fetch_word segs (pcw e 0x14c) = Some (Z_to_bv 32 0x0116a423). Proof. fw. Qed.
Lemma FC_150 : fetch_word segs (pcw e 0x150) = Some (Z_to_bv 32 0x0056a623). Proof. fw. Qed.
Lemma FC_154 : fetch_word segs (pcw e 0x154) = Some (Z_to_bv 32 0x01068693). Proof. fw. Qed.
Lemma FC_158 : fetch_word segs (pcw e 0x158) = Some (Z_to_bv 32 0xfcc76ae3). Proof. fw. Qed.
Lemma FC_15c : fetch_word segs (pcw e 0x15c) = Some (Z_to_bv 32 0x00800713). Proof. fw. Qed.
Lemma FC_160 : fetch_word segs (pcw e 0x160) = Some (Z_to_bv 32 0x00e66e63). Proof. fw. Qed.
Lemma FC_164 : fetch_word segs (pcw e 0x164) = Some (Z_to_bv 32 0x0005a703). Proof. fw. Qed.
Lemma FC_168 : fetch_word segs (pcw e 0x168) = Some (Z_to_bv 32 0x0045a783). Proof. fw. Qed.
Lemma FC_16c : fetch_word segs (pcw e 0x16c) = Some (Z_to_bv 32 0x00e6a023). Proof. fw. Qed.
Lemma FC_170 : fetch_word segs (pcw e 0x170) = Some (Z_to_bv 32 0x00f6a223). Proof. fw. Qed.
Lemma FC_174 : fetch_word segs (pcw e 0x174) = Some (Z_to_bv 32 0x00868693). Proof. fw. Qed.
Lemma FC_178 : fetch_word segs (pcw e 0x178) = Some (Z_to_bv 32 0x00858593). Proof. fw. Qed.
Lemma FC_17c : fetch_word segs (pcw e 0x17c) = Some (Z_to_bv 32 0x00467713). Proof. fw. Qed.
Lemma FC_180 : fetch_word segs (pcw e 0x180) = Some (Z_to_bv 32 0x24070063). Proof. fw. Qed.
Lemma FC_184 : fetch_word segs (pcw e 0x184) = Some (Z_to_bv 32 0x0005a703). Proof. fw. Qed.
Lemma FC_188 : fetch_word segs (pcw e 0x188) = Some (Z_to_bv 32 0x00458593). Proof. fw. Qed.
Lemma FC_18c : fetch_word segs (pcw e 0x18c) = Some (Z_to_bv 32 0x00e6a023). Proof. fw. Qed.
Lemma FC_190 : fetch_word segs (pcw e 0x190) = Some (Z_to_bv 32 0x00468693). Proof. fw. Qed.
Lemma FC_194 : fetch_word segs (pcw e 0x194) = Some (Z_to_bv 32 0x22c0006f). Proof. fw. Qed.
Lemma FC_3c0 : fetch_word segs (pcw e 0x3c0) = Some (Z_to_bv 32 0x00267713). Proof. fw. Qed.
Lemma FC_3c4 : fetch_word segs (pcw e 0x3c4) = Some (Z_to_bv 32 0x00071863). Proof. fw. Qed.
Lemma FC_3c8 : fetch_word segs (pcw e 0x3c8) = Some (Z_to_bv 32 0x00167613). Proof. fw. Qed.
Lemma FC_3cc : fetch_word segs (pcw e 0x3cc) = Some (Z_to_bv 32 0x02061663). Proof. fw. Qed.
Lemma FC_3d0 : fetch_word segs (pcw e 0x3d0) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.
Lemma FC_3d4 : fetch_word segs (pcw e 0x3d4) = Some (Z_to_bv 32 0x0005c703). Proof. fw. Qed.
Lemma FC_3d8 : fetch_word segs (pcw e 0x3d8) = Some (Z_to_bv 32 0x0015c783). Proof. fw. Qed.
Lemma FC_3dc : fetch_word segs (pcw e 0x3dc) = Some (Z_to_bv 32 0x00258593). Proof. fw. Qed.
Lemma FC_3e0 : fetch_word segs (pcw e 0x3e0) = Some (Z_to_bv 32 0x00268813). Proof. fw. Qed.
Lemma FC_3e4 : fetch_word segs (pcw e 0x3e4) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FC_3e8 : fetch_word segs (pcw e 0x3e8) = Some (Z_to_bv 32 0x00f680a3). Proof. fw. Qed.
Lemma FC_3ec : fetch_word segs (pcw e 0x3ec) = Some (Z_to_bv 32 0x00080693). Proof. fw. Qed.
Lemma FC_3f0 : fetch_word segs (pcw e 0x3f0) = Some (Z_to_bv 32 0x00167613). Proof. fw. Qed.
Lemma FC_3f4 : fetch_word segs (pcw e 0x3f4) = Some (Z_to_bv 32 0xfc060ee3). Proof. fw. Qed.
Lemma FC_3f8 : fetch_word segs (pcw e 0x3f8) = Some (Z_to_bv 32 0x0005c583). Proof. fw. Qed.
Lemma FC_3fc : fetch_word segs (pcw e 0x3fc) = Some (Z_to_bv 32 0x00b68023). Proof. fw. Qed.
Lemma FC_400 : fetch_word segs (pcw e 0x400) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.

Section Loop.
Variable CL : list reg.
Hypothesis HCL : forall r, In r MC_CLOB -> In r CL.
Hypothesis HCL1 : ~ In 1 CL.
Variable model : Model.
Variable J : machine_state -> Prop.   (* [comment removed for export] *)
Hypothesis J_acc : forall ms ms' acc, ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms.
Variable ms0 : machine_state.
Variables (dst src n : Z) (bs : list byte).
Hypothesis Hh : m_halted model = None.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Hypothesis Hnls : no_lazy model src (src + n).
Hypothesis Hnld : no_lazy model dst (dst + n).
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms', MCRc CL ms0 ms' -> copied (ms_mem ms') (ms_mem ms0) dst n bs ->
  ms_pc_val ms' = rg ms0 1 -> J ms'.

Lemma Lbs : length bs = Z.to_nat n.
Proof. exact (rdn_length _ _ _ _ _ Hbs). Qed.

Lemma src_rd : forall m k' (k : Z) (c : nat), copied m (ms_mem ms0) dst k' bs -> (0 <= k' <= n)%Z ->
  (0 <= k)%Z -> (k + Z.of_nat c <= n)%Z ->
  rdn segs m (Z_to_bv 64 (src + k)) c = Some (firstn c (skipn (Z.to_nat k) bs)).
Proof.
  intros m k' k c Hc Hk' Hk Hkc.
  assert (E : rdn segs m (Z_to_bv 64 (src + k)) c = rdn segs (ms_mem ms0) (Z_to_bv 64 (src + k)) c).
  { apply rdn_ext; [rewrite bvu_z by lia; lia|].
    intros x Hx. rewrite bvu_z in Hx by lia. apply (proj2 (Hc x)). lia. }
  rewrite E.
  pose proof (SeqExec.rdn_skipn segs (ms_mem ms0) (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat k) Hbs ltac:(lia)) as Hs.
  unfold nat_to_word in Hs. rewrite zw_add, Z2Nat.id in Hs by lia.
  apply (SeqExec.rdn_firstn segs (ms_mem ms0) (Z.to_nat n - Z.to_nat k)); [exact Hs | lia].
Qed.

Lemma sok_sub : forall m k' (k : Z) (c : nat), copied m (ms_mem ms0) dst k' bs ->
  (0 <= k)%Z -> (k + Z.of_nat c <= n)%Z -> store_ok segs m (Z_to_bv 64 (dst + k)) c = true.
Proof.
  intros m k' k c Hc Hk Hkc.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (copied_grows _ _ _ _ _ Hc) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Lemma len4 : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z -> length (firstn 4 (skipn (Z.to_nat k) bs)) = 4%nat.
Proof. intros k Hk Hkn. rewrite length_firstn, length_skipn, Lbs. lia. Qed.

Lemma mc_ret : forall S off, MCRc CL ms0 S -> ms_pc_val S = pcw e off ->
  fetch_word segs (pcw e off) = Some (Z_to_bv 32 0x00008067) ->
  copied (ms_mem S) (ms_mem ms0) dst n bs -> J S.
Proof.
  intros S off HS Hpc HF Hf.
  eapply xj_acc; [ exact J_acc | exact Hh | exact (mcr_svc _ _ _ HS) | eapply wacc_Jalr; [ rewrite Hpc; exact HF | reflexivity | exact DC_3d0 ]
                  | apply acc_ok_nil | ].
  apply HK.
  - eapply MCR_setx; [exact HS | left; reflexivity | reflexivity | reflexivity].
  - exact Hf.
  - rewrite pc_setx. rewrite (mcr_regs _ _ _ HS 1) by exact HCL1. apply ret_even. exact Hra.
Qed.

Ltac mcnorm := rgn; unfold w0; rewrite ?alu_add, ?zw_add, ?zw_add_sext; lits; rewrite ?Z.add_0_r, ?Z.add_0_l.
Ltac rwregs := repeat match goal with H : rg ?S ?r = _ |- context [rg ?S ?r] => rewrite H end.
Ltac acc_src NL := rwregs; mcnorm; apply acc_ok_one; rewrite bvu_z by lia; cbn [msz_n Z.of_nat Pos.of_succ_nat Pos.succ];
                   [lia | eapply no_lazy_sub; [exact NL | lia | lia]].
Ltac rd_src Hf := rewrite ?mem_setx; rgn; rwregs; mcnorm;
  first [ (eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]) | (eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]) ].

(* [comment removed for export] *)
Lemma t1 : forall S k, MCRc CL ms0 S -> ms_pc_val S = pcw e 0x3f8 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> (0 <= k)%Z -> (k + 1 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k HS Hpc H11 H13 Hk Hkn Hf.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | exact (mcr_svc _ _ _ HS) | eapply wacc_Load; [ rewrite Hpc; exact FC_3f8 | reflexivity | exact DC_3f8 | ] | | ].
  { rewrite H11. mcnorm. eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]. }
  { acc_src Hnls. }
  rewrite Hpc. pcn.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_3fc | reflexivity | exact DC_3fc | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 1); [exact Hf | lia | lia]. }
  { rgn. acc_src Hnld. }
  pcn. rgn. rewrite H13. mcnorm. rewrite store1_load1 by (rewrite length_firstn, length_skipn, Lbs; lia).
  apply (mc_ret _ 0x400); [ mcr_chain HS | reflexivity | exact FC_400 | ].
  rewrite ?mem_setx. replace n with (k + Z.of_nat 1)%Z by lia. rewrite <- (Z.add_0_l k) at 2.
  rewrite Z.add_0_l. replace (dst + k)%Z with (dst + k)%Z by reflexivity.
  apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf].
Qed.

(* [comment removed for export] *)
Lemma t2 : forall S k r, MCRc CL ms0 S -> ms_pc_val S = pcw e 0x3c0 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + r mod 4 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_3c0 DC_3c0. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_3c4 | reflexivity | exact DC_3c4 ] | apply acc_ok_nil | ].
  mcnorm. rewrite branch_ne_z by (try (pose proof (Z_land_range r 2); lia); lia). pcn.
  destruct (Z.eqb_spec (Z.land r 2) 0) as [B2|B2]; cbn [negb]; pcn.
  - (* [comment removed for export] *)
    destruct (b2_0 r Hr B2) as [M2 M4].
    jst wacc_OpImm FC_3c8 DC_3c8. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_3cc | reflexivity | exact DC_3cc ] | apply acc_ok_nil | ].
    mcnorm. rewrite branch_ne_z by (try (pose proof (Z_land_range r 1); lia); lia). pcn.
    destruct (Z.eqb_spec (Z.land r 1) 0) as [B1|B1]; cbn [negb]; pcn.
    + pose proof (b1_0 r Hr B1). apply (mc_ret _ 0x3d0); [ mcr_chain HS | reflexivity | exact FC_3d0 | ].
      rewrite ?mem_setx. replace n with k by lia. exact Hf.
    + pose proof (b1_1 r Hr B1). apply (t1 _ k); [ mcr_chain HS | reflexivity | | | lia | lia | ].
      * rgn. exact H11.
      * rgn. exact H13.
      * rewrite ?mem_setx. exact Hf.
  - (* [comment removed for export] *)
    destruct (b2_1 r Hr B2) as [M2 M4].
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_3d4 | reflexivity | exact DC_3d4 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]. }
    { rgn. acc_src Hnls. }
    pcn.
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_3d8 | reflexivity | exact DC_3d8 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 1); [exact Hf | lia | lia | lia]. }
    { rgn. acc_src Hnls. }
    pcn.
    (* [comment removed for export] *)
    jst wacc_OpImm FC_3dc DC_3dc. jst wacc_OpImm FC_3e0 DC_3e0.
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_3e4 | reflexivity | exact DC_3e4 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 1); [exact Hf | lia | lia]. }
    { rgn. acc_src Hnld. }
    pcn. rgn. rewrite H13. mcnorm. rewrite store1_load1 by (rewrite length_firstn, length_skipn, Lbs; lia).
    assert (Hf1 : copied (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 1 (skipn (Z.to_nat k) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 1) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf]. }
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_3e8 | reflexivity | exact DC_3e8 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 1)%Z with (dst + (k + Z.of_nat 1))%Z by lia.
      eapply (sok_sub _ _ _ 1); [exact Hf1 | lia | lia]. }
    { rgn. acc_src Hnld. }
    pcn. rgn. rewrite H13. mcnorm. rewrite store1_load1 by (rewrite length_firstn, length_skipn, Lbs; lia).
    replace (src + k + 1)%Z with (src + (k + Z.of_nat 1))%Z by lia.
    replace (dst + k + 1)%Z with (dst + (k + Z.of_nat 1))%Z by lia.
    replace (Z.to_nat (k + 1)) with (Z.to_nat (k + Z.of_nat 1)) by (f_equal; lia).
    assert (Hf2 : copied (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 1 (skipn (Z.to_nat k) bs)))
                            (Z_to_bv 64 (dst + (k + Z.of_nat 1))) (firstn 1 (skipn (Z.to_nat (k + Z.of_nat 1)) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 1 + Z.of_nat 1) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf1]. }
    (* [comment removed for export] *)
    jst wacc_OpImm FC_3ec DC_3ec. jst wacc_OpImm FC_3f0 DC_3c8. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_3f4 | reflexivity | exact DC_3f4 ] | apply acc_ok_nil | ].
    mcnorm. rewrite branch_eq_z by (try (pose proof (Z_land_range r 1); lia); lia). pcn.
    destruct (Z.eqb_spec (Z.land r 1) 0) as [B1|B1]; pcn.
    + pose proof (b1_0 r Hr B1). apply (mc_ret _ 0x3d0); [ mcr_chain HS | reflexivity | exact FC_3d0 | ].
      rewrite ?mem_setx. replace n with (k + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf2.
    + pose proof (b1_1 r Hr B1). apply (t1 _ (k + 2)%Z); [ mcr_chain HS | reflexivity | | | lia | lia | ].
      * rgn. rwregs. mcnorm. f_equal. lia.
      * rgn. rwregs. mcnorm. f_equal. lia.
      * rewrite ?mem_setx. replace (k + 2)%Z with (k + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf2.
Qed.

(* [comment removed for export] *)
Lemma t4 : forall S k r, MCRc CL ms0 S -> ms_pc_val S = pcw e 0x17c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 16)%Z -> (0 <= k)%Z -> (k + r mod 8 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_17c DC_17c. rgn. rewrite H12. rewrite alu_andi_z by (lits; lia). lits.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_180 | reflexivity | exact DC_180 ] | apply acc_ok_nil | ].
  mcnorm. rewrite branch_eq_z by (try (pose proof (Z_land_range r 4); lia); lia). pcn.
  destruct (Z.eqb_spec (Z.land r 4) 0) as [B4|B4]; pcn.
  - destruct (b4_0 r Hr B4) as [M4 M8].
    apply (t2 _ k r); [ mcr_chain HS | reflexivity | rgn; exact H11 | rgn; exact H13 | rgn; exact H12 | lia | lia | lia | ].
    rewrite ?mem_setx. exact Hf.
  - destruct (b4_1 r Hr B4) as [M4 M8].
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_184 | reflexivity | exact DC_164 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
    { rgn. acc_src Hnls. }
    pcn.
    (* [comment removed for export] *)
    jst wacc_OpImm FC_188 DC_188.
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_18c | reflexivity | exact DC_16c | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 4); [exact Hf | lia | lia]. }
    { rgn. acc_src Hnld. }
    pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
    (* [comment removed for export] *)
    jst wacc_OpImm FC_190 DC_190. jst wacc_Jal FC_194 DC_194.
    apply (t2 _ (k + 4)%Z r); [ mcr_chain HS | reflexivity | | | | lia | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. exact H12.
    + rewrite ?mem_setx. replace (k + 4)%Z with (k + Z.of_nat 4)%Z by reflexivity.
      apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf].
Qed.

(* [comment removed for export] *)
Lemma t8 : forall S k r, MCRc CL ms0 S -> ms_pc_val S = pcw e 0x15c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 16)%Z -> (0 <= k)%Z -> (k + r = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_15c DC_15c. mcnorm.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_160 | reflexivity | exact DC_160 ] | apply acc_ok_nil | ].
  mcnorm. rewrite H12. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec r 8) as [R8|R8]; pcn.
  - pose proof (b8_lt r ltac:(lia)).
    apply (t4 _ k r); [ mcr_chain HS | reflexivity | rgn; exact H11 | rgn; exact H13 | rgn; exact H12 | lia | lia | lia | ].
    rewrite ?mem_setx. exact Hf.
  - pose proof (b8_ge r ltac:(lia)).
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_164 | reflexivity | exact DC_164 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
    { rgn. acc_src Hnls. }
    pcn.
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_168 | reflexivity | exact DC_168 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
    { rgn. acc_src Hnls. }
    pcn.
    (* [comment removed for export] *)
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_16c | reflexivity | exact DC_16c | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 4); [exact Hf | lia | lia]. }
    { rgn. acc_src Hnld. }
    pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
    assert (Hf1 : copied (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 4) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf]. }
    eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_170 | reflexivity | exact DC_170 | ] | | ].
    { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
      eapply (sok_sub _ _ _ 4); [exact Hf1 | lia | lia]. }
    { rgn. acc_src Hnld. }
    pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
    replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
    replace (Z.to_nat (k + 4)) with (Z.to_nat (k + Z.of_nat 4)) by (f_equal; lia).
    assert (Hf2 : copied (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                            (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                    (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4) bs).
    { apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf1]. }
    (* [comment removed for export] *)
    jst wacc_OpImm FC_174 DC_174. jst wacc_OpImm FC_178 DC_178.
    apply (t4 _ (k + 8)%Z r); [ mcr_chain HS | reflexivity | | | | lia | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. exact H12.
    + rewrite ?mem_setx. replace (k + 8)%Z with (k + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf2.
Qed.

(* [comment removed for export] *)
Lemma loop16 : forall (d : nat) S k, (n - k < 16 * Z.of_nat d)%Z ->
  MCRc CL ms0 S -> ms_pc_val S = pcw e 0x12c ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = Z_to_bv 64 15 -> (16 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  induction d as [|d IH]; intros S k Hd HS Hpc H11 H13 H12 H14 Hnk Hk Hf; [lia|].
  pose proof (mcr_svc _ _ _ HS) as Hsvc.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | exact Hsvc | eapply wacc_Load; [ rewrite Hpc; exact FC_12c | reflexivity | exact DC_12c | ] | | ].
  { rewrite H11. mcnorm. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { acc_src Hnls. }
  rewrite Hpc. pcn.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_130 | reflexivity | exact DC_130 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { rgn. acc_src Hnls. }
  pcn.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_134 | reflexivity | exact DC_134 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { rgn. acc_src Hnls. }
  pcn.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Load; [ fetch_tac FC_138 | reflexivity | exact DC_138 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H11. mcnorm. rewrite <- Z.add_assoc. eapply (src_rd _ _ _ 4); [exact Hf | lia | lia | lia]. }
  { rgn. acc_src Hnls. }
  pcn.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_13c DC_13c. jst wacc_OpImm FC_140 DC_140.
  (* [comment removed for export] *)
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_144 | reflexivity | exact DC_144 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. eapply (sok_sub _ _ _ 4); [exact Hf | lia | lia]. }
  { rgn. acc_src Hnld. }
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  assert (Hf1 : copied (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4) bs) by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf]).
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_148 | reflexivity | exact DC_148 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
    eapply (sok_sub _ _ _ 4); [exact Hf1 | lia | lia]. }
  { rgn. acc_src Hnld. }
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  replace (dst + k + 4)%Z with (dst + (k + Z.of_nat 4))%Z by lia.
  replace (Z.to_nat (k + 4)) with (Z.to_nat (k + Z.of_nat 4)) by (f_equal; lia).
  assert (Hf2 : copied (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4) bs) by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf1]).
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_14c | reflexivity | exact DC_14c | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 8)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
    eapply (sok_sub _ _ _ 4); [exact Hf2 | lia | lia]. }
  { rgn. acc_src Hnld. }
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  replace (dst + k + 8)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
  replace (Z.to_nat (k + 8)) with (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4)) by (f_equal; lia).
  assert (Hf3 : copied (write_to_mem (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4 + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4)) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) bs)
    by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf2]).
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Store; [ fetch_tac FC_150 | reflexivity | exact DC_150 | ] | | ].
  { rewrite ?mem_setx. rgn. rewrite H13. mcnorm. replace (dst + k + 12)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
    eapply (sok_sub _ _ _ 4); [exact Hf3 | lia | lia]. }
  { rgn. acc_src Hnld. }
  pcn. rgn. rewrite H13. mcnorm. rewrite store4_load4 by (apply len4; lia).
  replace (dst + k + 12)%Z with (dst + (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4))%Z by lia.
  replace (Z.to_nat (k + 12)) with (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)) by (f_equal; lia).
  assert (Hf4 : copied (write_to_mem (write_to_mem (write_to_mem (write_to_mem (ms_mem S) (Z_to_bv 64 (dst + k)) (firstn 4 (skipn (Z.to_nat k) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4)) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4 + Z.of_nat 4))) (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4)) bs)))
                          (Z_to_bv 64 (dst + (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)))
                          (firstn 4 (skipn (Z.to_nat (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)) bs)))
                  (ms_mem ms0) dst (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) bs)
    by (apply copied_step; [lia | lia | rewrite Lbs; lia | lia | exact Hf3]).
  (* [comment removed for export] *)
  jst wacc_OpImm FC_154 DC_154.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_158 | reflexivity | exact DC_158 ] | apply acc_ok_nil | ].
  mcnorm. rewrite H14, H12. mcnorm. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec 15 (n - k + -16)) as [Lt|Ge]; pcn.
  - apply (IH _ (k + 16)%Z); [ lia | mcr_chain HS | reflexivity | | | | | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. exact H14.
    + rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf4.
  - apply (t8 _ (k + 16)%Z (n - k + -16)%Z); [ mcr_chain HS | reflexivity | | | | lia | lia | lia | ].
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. f_equal. lia.
    + rgn. rwregs. mcnorm. reflexivity.
    + rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z by lia. exact Hf4.
Qed.

(* [comment removed for export] *)
Lemma al120 : forall S k, MCRc CL ms0 S -> ms_pc_val S = pcw e 0x120 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (0 <= k <= n)%Z -> copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k HS Hpc H11 H13 H12 Hk Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_120 DC_120. mcnorm.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_124 | reflexivity | exact DC_124 ] | apply acc_ok_nil | ].
  mcnorm. rewrite H12. rewrite branch_ltu_z by lia. pcn.
  destruct (Z.ltb_spec (n - k) 16) as [N16|N16]; pcn.
  - apply (t8 _ k (n - k)%Z); [ mcr_chain HS | reflexivity | rgn; exact H11 | rgn; exact H13 | rgn; exact H12 | lia | lia | lia | ].
    rewrite ?mem_setx. exact Hf.
  - jst wacc_OpImm FC_128 DC_128. mcnorm.
    apply (loop16 (Z.to_nat ((n - k) / 16) + 1) _ k).
    + pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)).
      rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). lia.
    + mcr_chain HS.
    + reflexivity.
    + rgn. exact H11.
    + rgn. exact H13.
    + rgn. exact H12.
    + rgn. reflexivity.
    + lia.
    + lia.
    + rewrite ?mem_setx. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma mc_entry :
  ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw e 0 ->
  rg ms0 10 = Z_to_bv 64 dst -> rg ms0 11 = Z_to_bv 64 src -> rg ms0 12 = Z_to_bv 64 n ->
  (src mod 4 = 0)%Z -> (dst mod 4 = 0)%Z ->
  J ms0.
Proof.
  intros Hsvc Hpc H10 H11 H12 Hsa Hda. pose proof (MCR_refl CL ms0 Hsvc) as HS.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_0 DC_0. mcnorm. rewrite H11. rewrite alu_andi_z by (lits; lia). lits.
  rewrite land3_mod4 by assumption.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_4 | reflexivity | exact DC_4 ] | apply acc_ok_nil | ].
  mcnorm. rewrite branch_eq_z by lia. pcn. cbn [Z.eqb]. pcn.
  (* [comment removed for export] *)
  jst wacc_OpImm FC_114 DC_114. mcnorm. rewrite H10. mcnorm.
  jst wacc_OpImm FC_118 DC_118. mcnorm. rewrite H10. rewrite alu_andi_z by (lits; lia). lits. rewrite land3_mod4 by assumption.
  eapply xj_acc; [ exact J_acc | exact Hh | reflexivity | eapply wacc_Branch; [ fetch_tac FC_11c | reflexivity | exact DC_11c ] | apply acc_ok_nil | ].
  mcnorm. rewrite branch_ne_z by lia. pcn. cbn [Z.eqb negb]. pcn.
  apply (al120 _ 0%Z); [ mcr_chain HS | reflexivity | | | | lia | ].
  + rgn. rewrite H11; f_equal; lia.
  + rgn. rwregs. mcnorm. f_equal; lia.
  + rgn. rewrite H12; f_equal; lia.
  + rewrite ?mem_setx. apply copied_refl.
Qed.

End Loop.
End MCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem memcpy_aligned_sum_J : forall (segs : list Segment) (e : Z), MCCode segs e ->
  forall (model : Model) (J : machine_state -> Prop),
  (forall ms ms' acc, ms_svc_pending ms = None ->
     step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms) ->
  forall (ms : machine_state) (dst src n : Z) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = Z_to_bv 64 src -> rg ms 12 = Z_to_bv 64 n ->
  (src mod 4 = 0)%Z -> (dst mod 4 = 0)%Z ->
  (0 <= dst)%Z -> (0 <= src)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z -> (src + n <= 2 ^ 47)%Z ->
  (src + n <= dst \/ dst + n <= src)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  no_lazy model src (src + n) -> no_lazy model dst (dst + n) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', MCR ms ms' -> copied (ms_mem ms') (ms_mem ms) dst n bs ->
     ms_pc_val ms' = rg ms 1 -> J ms') ->
  J ms.
Proof.
  intros segs e HC model J J_acc ms dst src n bs Hsvc Hpc Hh H10 H11 H12 Hsa Hda Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
  exact (mc_entry segs e HC MC_CLOB (fun r H => H) ltac:(cbn; intuition discriminate) model J J_acc ms dst src n bs
           Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK Hsvc Hpc H10 H11 H12 Hsa Hda).
Qed.

(* [comment removed for export] *)
Theorem memcpy_aligned_sum : forall (segs : list Segment) (cfg : SpuriousCfg) (e : Z), MCCode segs e ->
  forall (ms : machine_state) (model : Model) (K : TSet) (dst src n : Z) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = Z_to_bv 64 src -> rg ms 12 = Z_to_bv 64 n ->
  (src mod 4 = 0)%Z -> (dst mod 4 = 0)%Z ->
  (0 <= dst)%Z -> (0 <= src)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z -> (src + n <= 2 ^ 47)%Z ->
  (src + n <= dst \/ dst + n <= src)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  no_lazy model src (src + n) -> no_lazy model dst (dst + n) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', MCR ms ms' -> copied (ms_mem ms') (ms_mem ms) dst n bs ->
     ms_pc_val ms' = rg ms 1 -> realizes_cfg segs cfg (mkCfg ms' model) K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros segs cfg e HC ms model K dst src n bs Hsvc Hpc Hh.
  exact (memcpy_aligned_sum_J segs e HC model (fun S => realizes_cfg segs cfg (mkCfg S model) K)
           (fun ms0 ms' acc => rzc_acc segs cfg ms0 model ms' acc K Hh) ms dst src n bs Hsvc Hpc Hh).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

