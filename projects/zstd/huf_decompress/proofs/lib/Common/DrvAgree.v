(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (16 recorded proofs replaced by written proofs (zbytes_length, zbytes_app, zbytes_map_unsigned' and 13 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_DrvAgree () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib6Common8DrvAgree6zbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapK47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib6Common8DrvAgreeDzbytes_map_unsigned'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powK47Corelib5Lists7ListDef6Forall02K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8DrvAgree?bytes_at_magreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8DrvAgree<wr_at_magreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr:u64s_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC46Stdlib5Lists4List9app_nil_lC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.

Lemma zbytes_length : forall l, length (zbytes l) = length l.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_app : forall l1 l2, zbytes (l1 ++ l2) = zbytes l1 ++ zbytes l2.
Proof. intros. unfold zbytes. apply map_app. Qed.

Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. intros bs. rewrite map_map. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.
Lemma zbytes_map_unsigned : forall bs : list byte, zbytes (map bv_unsigned bs) = bs.
Proof. exact zbytes_map_unsigned'. Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; constructor.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    assert (bv_unsigned b <> 0); [| lia]. intros E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. rewrite E. reflexivity.
  - apply IH. intros X. apply H. right. exact X.
Qed.

Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition magree (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Lemma magree_refl : forall P m, magree P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma magree_trans : forall P m1 m2 m3, magree P m1 m2 -> magree P m2 m3 -> magree P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma magree_mono : forall (P P' : Z -> Prop) m m', magree P m m' -> (forall a, P' a -> P a) -> magree P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma bytes_at_magree : forall P m m' A bs,
  magree P m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at segs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_magree : forall P m m' A n,
  magree P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_magree : forall P m m' A cs,
  magree P m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells segs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_magree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_magree; eauto.
Qed.

Lemma stk_magree : forall P m m' lo hi,
  magree P m m' -> stk segs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk segs m' lo hi.
Proof.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HS a Ha) as [W [b R]]. destruct (HP a ltac:(lia) ltac:(apply HR; lia)) as [E W'].
  split; [apply W'; exact W|]. exists b. unfold mrd in *. rewrite E. exact R.
Qed.

(* [comment removed for export] *)
Lemma magree_of_munch : forall W m m', munch W m m' -> wmono segs m m' -> magree (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

(* [comment removed for export] *)
Lemma u64ro_read : forall m A ws (i : Z) w a,
  bytes_at segs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End WithSegs.
