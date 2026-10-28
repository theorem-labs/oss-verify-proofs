(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacM DecAux DecAuxM S0_dec_U13 S0_dec_U7D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU4 BzDU6 BzDUM BzDU7. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacFR2 S0F_decRet S0F_decCuts7.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts7.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Lemma zw32_clear256 : forall a, zw32 (clear256 256 0 a) 256 = repeat (Z_to_bv 64 0) (Z.to_nat 256).
Proof.
  intros a. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat 256)) as [Hk|Hk].
  - rewrite nth_error_repeat by exact Hk. replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite zw32_nth by lia. rewrite zget_clear256_in by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.
Lemma u7_zw32_clear256_snoc : forall a k, (0 <= k < 256)%Z ->
  zw32 (zset (clear256 (Z.to_nat k) 0 a) k 0) 256 = zw32 (clear256 (Z.to_nat (k + 1)) 0 a) 256.
Proof.
  intros a k Hk. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (Z.to_nat 256)) as [Hn|Hn].
  - replace n with (Z.to_nat (Z.of_nat n)) by lia. rewrite !zw32_nth by lia. f_equal. f_equal.
    rewrite zget_zset, !zget_clear256.
    destruct (Z.eqb_spec (Z.of_nat n) k) as [E|NE];
    destruct (Z.leb_spec 0 (Z.of_nat n)); destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat k)));
    destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat (k + 1)))); cbn [andb]; try reflexivity; try lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.
Lemma u7_swrap32_land64_add : forall a b, (- 2147483648 <= a + b < 2147483648)%Z ->
  bv_swrap 32 (Z.land a 18446744073709551615 + b)%Z = (a + b)%Z.
Proof.
  intros a b H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  rewrite (Z.mod_eq a (2 ^ 64)) by lia.
  replace (a - 2 ^ 64 * (a / 2 ^ 64) + b + 2147483648)%Z with ((a + b + 2147483648) + (- (a / 2 ^ 64) * 4294967296) * 4294967296)%Z by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac zw32_store_done ARR i v :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le4 ?x)) _) =>
      lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zw32_write segs mm A a n i x v ARR ltac:(lia)
                      ltac:(first [ reflexivity | rewrite unsigned_lit by lia; first [ reflexivity | f_equal; lia ] ])) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL7G : S0F_cut_L7G A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Notation KFR m j0 f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 pb d :=
    (S0FR A m j0 f8 (Z_to_bv 64 (S + 64012)) (Z_to_bv 64 (S + 57820)) (Z_to_bv 64 (S + 45436)) (Z_to_bv 64 (S + 51628))
         (Z_to_bv 64 (18446744073709551615 - (S + 64012))) (Z_to_bv 64 (18446744073709551615 - (S + 57820)))
         (Z_to_bv 64 (18446744073709551615 - (S + 51628))) (Z_to_bv 64 (18446744073709551615 - (S + 45436)))
         f80 (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (100000 * d_bs100k d)) f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb) (only parsing).

  (* [comment removed for export] *)
  Definition L7K (ii : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x16 x21 x22 x23 x24 x25 x27 x28 x29 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    KFR m j0 f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 pb d ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (dinv_L7K L d ii /\ 0 <= ii)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7K F L d s ii))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
              (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (18446744073709551615 - (S + 3724)))
              (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) (Z_to_bv 64 (3855 + 16 * ii)) x16 (Z_to_bv 64 ii)
              (Z_to_bv 64 S) (Z_to_bv 64 (sv_alphaSize L - 1)) (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29
              (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26b4c) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition L7J (ii dd : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x6 x7 x8 x9 x21 x22 x23 x24 x25 x27 x28 x29 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    KFR m j0 f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 pb d ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (dinv_L7J L d ii dd /\ dd <= 15)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7J F L d s ii dd))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) (Z_to_bv 64 (16 * ii + 15 - dd)) x6 x7 x8 x9
              (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (18446744073709551615 - (S + 3724)))
              (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (18446744073709551615 - (S + 7820))) (Z_to_bv 64 (3855 + 16 * ii - dd))
              (Z_to_bv 64 ii) (Z_to_bv 64 (dd - 16))
              (Z_to_bv 64 S) (Z_to_bv 64 (sv_alphaSize L - 1)) (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29
              (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26b58) (a_fc A) None m (seg_rom s0segs)).

  Definition L7Z (k : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_unzftab d (clear256 (Z.to_nat k) 0 (d_unzftab d))) s) ->
    KFR m j0 f8 f80 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 pb d ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    dinv_H7M L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_H7M F L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
              (Z_to_bv 64 (4 * k)) (Z_to_bv 64 (S + 68)) (Z_to_bv 64 (18446744073709551615 - (S + 68))) (Z_to_bv 64 1024) x14 x15 x16 x17
              (Z_to_bv 64 S) (Z_to_bv 64 (sv_alphaSize L - 1)) (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 (Z_to_bv 64 (sv_nSelectors L)) x27 x28 x29
              (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26b08) (a_fc A) None m (seg_rom s0segs)).

  Lemma S0F_U7_K : forall ii, L7J ii 0 -> L7K ii.
  Proof.
    intros ii NX. unfold L7K. intros until pb. intros DM FR ST MU WM MI DP [DI Hii] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (SEL & TABS & U0 & Hii' & MB & MA).
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro. rewrite K_L7K_in in KQ by lia.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    enter_sameF NX DP.
    split; [| lia]. unfold dinv_L7J. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    intros k Hk. apply MA. lia.
  Qed.

  Lemma S0F_U7_J : forall ii dd, L7J ii (dd + 1) -> L7K (ii - 1) -> L7J ii dd.
  Proof.
    intros ii dd NXJ NXK. unfold L7J. intros until pb. intros DM FR ST MU WM MI DP [DI Hdd] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (SEL & TABS & U0 & Hii & Hdd' & MB & MA).
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro. rewrite K_L7J_step in KQ by lia.
    replace (ii * 16 + (15 - dd))%Z with (16 * ii + 15 - dd)%Z in KQ by lia.
    unfold r_of in DR. dr_open. hide_all_but_at [S + 3724; S + 7820]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820); (S + 7820, S + 7884)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl. wstepl; notrap. wstepl; notrap. wstepl. wstepl. wstepl.
    try rewrite (u7_swrap32_land64_add (dd - 16) 1) by lia.
    lazymatch goal with H : u8arr _ _ (S + 3724)%Z _ |- _ =>
      zb8_sb H (3855 + 16 * ii - dd)%Z; try rewrite (Z.mod_small (16 * ii + 15 - dd) 256) in H by lia end.
    (* [comment removed for export] *)
    wstepl.
    wstepl; if_cases KC; zify_cond_z KC.
    - assert (D15 : dd <> 15%Z) by (intro E; rewrite E in KC; apply KC; reflexivity).
      revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NXJ DP.
      split; [| lia]. unfold dinv_L7J. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
      intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k (3855 + 16 * ii - dd)); [lia|]. apply MA. lia.
    - (* [comment removed for export] *)
      assert (D15 : dd = 15%Z) by (destruct (Z.eq_dec dd 15) as [?|NE]; [assumption| exfalso; change 18446744073709551615%Z with (Z.ones 64) in KC; rewrite Z.land_ones in KC by lia; Z.div_mod_to_equations; lia]).
      wstepl. wstepl; notrap. wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 7820)%Z ?ws |- _ =>
        pose proof (u32arr_store_ok s0segs mm (S + 7820) ws ii _ H ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
        wstepl; zw32_store_done H ii (3840 + 16 * ii)%Z end.
      try clear SO.
      (* [comment removed for export] *)
      wstepl. wstepl.
      wstepl; if_cases K2; zify_cond_z K2.
      + replace (dd + 1)%Z with 16%Z in KQ by lia. rewrite K_L7J_exit in KQ by lia.
        revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NXK DP.
        split; [| lia]. unfold dinv_L7K. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
        all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
        all: try (intros l Hl; rewrite zget_zset; destruct (Z.eqb_spec l ii); [lia|]; apply MB; lia).
        all: intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k (3855 + 16 * ii - dd)); [lia|]; apply MA; lia.
      + (* [comment removed for export] *)
        replace (dd + 1)%Z with 16%Z in KQ by lia. subst ii. rewrite K_L7J_last in KQ.
        revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF HL7G DP.
        unfold dinv_L7G, mtf_okF, mtfb. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption.
        all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
        all: try (apply (mtf_inv_ext (fun l => 3840 + 16 * l)%Z); [| exact mtf_inv_home];
                  intros l Hl; rewrite zget_zset; destruct (Z.eqb_spec l 0); [lia|]; rewrite MB by lia; reflexivity).
        all: try lia.
        (* [comment removed for export] *)
        all: intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k (3855 + 16 * 0 - dd)); [lia|];
          destruct (Z_lt_le_dec k (3855 + 16 * 0 - dd));
          [ pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP; unfold drep in RP; dmodel_cbn_in RP;
            cps_destruct RP as (_ & _ & _ & _ & _ & MTFA); apply MTFA; lia
          | apply MA; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U7_Z : forall k, (0 <= k <= 255)%Z -> L7K 15 -> ((k < 255)%Z -> L7Z (k + 1)) -> L7Z k.
  Proof.
    intros k Hk NXK NXT. unfold L7Z. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [COM TABS]. pose proof COM as COM'. destruct COM' as [SEL LALL].
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro.
    unfold r_of in DR. dr_open. repeat match goal with H : u32arr _ _ _ _ |- _ => progress dmodel_cbn_in H end.
    hide_all_but_at [S + 68; usp + -336]%Z.
    pose proof (munch_refl [(S + 68, S + 1092)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl; notrap. wstepl. wstepl.
    lazymatch goal with H : u32arr _ ?mm (S + 68)%Z ?ws |- _ =>
      pose proof (u32arr_store_ok s0segs mm (S + 68) ws k _ H ltac:(rewrite zw32_length_nat; lia) ltac:(first [reflexivity | f_equal; lia])) as SO;
      wstepl; try (lazymatch goal with |- context [Z_to_le_bytes 4 ?z] => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)) end);
      zw32_store_done H k 0%Z; rewrite (u7_zw32_clear256_snoc (d_unzftab d) k) in H by lia end.
    try clear SO.
    wstepl; if_cases KC; zify_cond_z KC.
    - pose proof (NXT ltac:(lia)) as NX. unfold L7Z in NX.
      try replace (4 * k + 4)%Z with (4 * (k + 1))%Z by lia.
      revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NX DP. exact DI.
    - (* [comment removed for export] *)
      do 11 wstepl.
      match goal with H : u32arr _ _ (S + 68)%Z _ |- _ => replace (Z.to_nat (k + 1)) with 256%nat in H by lia end.
      rewrite K_H7M_memset in KQ.
      revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NXK DP.
      split; [| lia]. unfold dinv_L7K. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
      all: try apply unz0_clear.
      all: intros; exfalso; lia.
  Qed.
  Lemma S0F_U7_Z_all : L7K 15 -> forall k, (0 <= k <= 255)%Z -> L7Z k.
  Proof.
    intros NXK.
    assert (G : forall j : nat, (j <= 255)%nat -> L7Z (255 - Z.of_nat j)%Z).
    { induction j as [|j IH]; intros Hj.
      - apply S0F_U7_Z; [lia | exact NXK | intros; exfalso; lia].
      - apply S0F_U7_Z; [lia | exact NXK | intros _].
        replace (255 - Z.of_nat (Datatypes.S j) + 1)%Z with (255 - Z.of_nat j)%Z by lia. apply IH. lia. }
    intros k Hk. replace k with (255 - Z.of_nat (Z.to_nat (255 - k)))%Z by lia. apply G. lia.
  Qed.

  Lemma S0F_U7_M : L7K 15 -> S0F_cut_H7M A F.
  Proof.
    intros NXK. pose proof (S0F_U7_Z_all NXK 0 ltac:(lia)) as NX. unfold S0F_cut_H7M. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [COM TABS]. pose proof COM as COM'. destruct COM' as [SEL LALL].
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro.
    unfold r_of in DR. dr_open.
    (* [comment removed for export] *)
    hide_all_but_at [S; S + 3152; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    wstepl. wstepl. wstepl. wstepl; notrap.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl; notrap.
    wstepl. wstepl. wstepl. wstepl.
    try replace (Z_to_bv 64 (d_nInUse d + 1)) with (Z_to_bv 64 (sv_alphaSize L - 1)) in * by (f_equal; unfold alpha_ok in AL; lia).
    try replace (d_bs100k d * 100000)%Z with (100000 * d_bs100k d)%Z in * by lia.
    revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NX DP. exact DI.
  Qed.
End R.

Lemma S0F_U7_mtf : forall A, act_ok 320 A -> forall F, S0F_cut_L7G A F -> S0F_cut_H7M A F.
Proof.
  intros A AOK F HL7G. apply (S0F_U7_M A AOK F).
  assert (J : forall ii, L7K A F (ii - 1) -> forall k : nat, forall dd, (15 - Z.of_nat k <= dd)%Z -> L7J A F ii dd).
  { intros ii NXK. induction k as [|k IH]; intros dd Hdd.
    - (* [comment removed for export] *)
      apply (S0F_U7_J A AOK F HL7G); [| exact NXK].
      unfold L7J. intros until pb. intros DM FR ST MU WM MI DP [DI Hdd2] FU. exfalso. cbn in Hdd. lia.
    - apply (S0F_U7_J A AOK F HL7G); [| exact NXK]. apply IH. lia. }
  assert (K : forall k : nat, forall ii, (ii <= Z.of_nat k - 1)%Z -> L7K A F ii).
  { induction k as [|k IH]; intros ii Hii.
    - unfold L7K. intros until pb. intros DM FR ST MU WM MI DP [DI Hii2] FU. exfalso. cbn in Hii. lia.
    - apply (S0F_U7_K A AOK F). apply (J ii ltac:(apply IH; lia) 16%nat). cbn; lia. }
  apply (K 16%nat). cbn; lia.
Qed.

End ACeilS1.
