(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import
     BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith BzWalkArith3 S0_dec_U13 S0_decCuts S0_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU12F. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecAux12F.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SepFast.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= SepFast.tlia_dr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma zw32_read_b0 : forall segs m A a n i ad, u32arr segs m A (zw32 a n) -> (0 <= i < n)%Z -> (0 <= zget a i < 2 ^ 32)%Z ->
  ad = wa (A + 4 * i) -> ov_read_bytes segs m ad 1 = Some [Z_to_bv 8 (Z.land (zget a i) 255)].
Proof.
  intros segs m A a n i ad H Hi Hv ->.
  rewrite (u32arr_read_b0 segs m A (zw32 a n) i (Z_to_bv 64 (zget a i)) _ H (zw32_nth a n i Hi) ltac:(lia) eq_refl).
  f_equal. f_equal. rewrite unsigned_lit by lia. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply Z_to_bv8_mod256.
Qed.

Lemma land3_mod : forall x, Z.land x 3 = (x mod 4)%Z.
Proof. intros x. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.
  Ltac revive_smF SM MUL WML LIN DP :=
    clear LIN;
    let L1 := fresh "LINs" in let L2 := fresh "LINm" in
    pose proof (act_lin_core _ _ AOK) as L1;
    first [ pose proof (act_lin_ll _ _ AOK SM) as L2 | pose proof (act_lin_tt _ _ AOK SM) as L2 ];
    revive_all_sm AOK SM MUL WML;
    clear L1 L2; pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at s0segs mm cx (blk_of cx D)) end.
  Ltac bdec :=
    rewrite ?land3_mod;
    repeat match goal with
      | |- context [(?a <? ?b)%Z] => first [ rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia ]
      | |- context [(?a <=? ?b)%Z] => first [ rewrite (proj2 (Z.leb_gt a b)) by lia | rewrite (proj2 (Z.leb_le a b)) by lia ]
      | |- context [(?a =? ?b)%Z] => first [ rewrite (proj2 (Z.eqb_neq a b)) by lia | rewrite (proj2 (Z.eqb_eq a b)) by lia ]
      end;
    cbn [Z.b2z];
    repeat match goal with
      | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let c := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with c
      | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
      end.
  Ltac ck := bdec; notrap.

  Section FA.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym tt0 : Z -> Z).
  Notation nb := (sv_nblock L).

  (* [comment removed for export] *)
  Definition L29cF (i : Z) : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
      dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
           (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
      stk s0segs m (a_lo A) (usp + -336) ->
      munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      fuel_ok F d s ->
      dinv_L29 L d i sym tt0 ->
      evt s0segs (QF A (K_L29 F L d s i))
        (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
                (Z_to_bv 64 (256 * i)) (Z_to_bv 64 TT) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (8388608 - i)) (Z_to_bv 64 (nb - i))
                (Z_to_bv 64 (TT + 4 * i)) (Z_to_bv 64 (TT + 4 * i)) (Z_to_bv 64 S)
                x19 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 nb) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            (a_F A) (Z_to_bv 64 163416) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition AFTcF : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
      dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
           (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
      stk s0segs m (a_lo A) (usp + -336) ->
      munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      fuel_ok F d s ->
      dinv_AFT L d sym tt0 ->
      evt s0segs (QF A (dgo F (be_aft L d s)))
        (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
                x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S)
                x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 nb) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            (a_F A) (Z_to_bv 64 163752) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Lemma S0F_U12_L29 : forall i, (0 <= i < nb)%Z -> ((i + 1 < nb)%Z -> L29cF (i + 1)) -> ((i + 1)%Z = nb -> AFTcF) -> L29cF i.
  Proof.
    intros i Hi NXT LAST. unfold L29cF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    cps_pose DI as (_ & ORIG & NB1 & NB9 & HDR & TS & SM0 & SYMB & HIST & HT0 & HT0R & TTV & CFV).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM0 in SMALL. symmetry in SMALL.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    prepS DM MU DP SMALL.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
    pose proof (act_tt_s _ _ AOK SMALL) as [[TT0 TT1] SEPtt].
    cps_pose (l29_facts L d i sym tt0 DI ltac:(lia)) as (EUC & UCR & KR & VR & ALLR & VR2 & _).
    pose proof (ALLR i ltac:(lia)) as TIR. unfold l29_v, l29_k, l29_uc in EUC, UCR, KR, VR, VR2.
    hide_all_but_at [S + 1096; TT]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (TT, TT + 400000 * b_n cx)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_L29_step F L d s i) in KQ by lia.
    remember (Z.land (zget (d_tt d) i) 255) as uc eqn:Euc.
    remember (zget (d_cftab d) uc) as k eqn:Ek.
    remember (Z.lor (zget (d_tt d) k) (Z.shiftl i 8)) as v eqn:Ev.
    assert (Ev' : Z.lor (zget (d_tt d) k) (256 * i) = v) by (rewrite Ev, Z.shiftl_mul_pow2 by lia; f_equal; lia).
    (* [comment removed for export] *)
    wstepl; ck. wstepl. wstepl. wstepl; ck. wstepl; ck. wstepl; ck.
    pose proof (zw32_read_b0 s0segs m TT (d_tt d) _ i _ TTA ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    rewrite <- Euc in RD.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    wstepl. wstepl. wstepl; ck. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m (S + 1096) (d_cftab d) 257 uc _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    rewrite <- Ek in RD.
    wstepl. clear RD.
    wstepl. wstepl. wstepl; ck. wstepl. wstepl. wstepl. wstepl. wstepl; ck. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m TT (d_tt d) _ k _ TTA ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstepl. clear RD.
    wstepl. (* [comment removed for export] *) rewrite Ev'.
    zw32_sw TTA k v ltac:(rewrite unsigned_lit by lia; reflexivity). (* [comment removed for export] *)
    wstepl; ck.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read s0segs mm (S + 1096) (d_cftab d) 257 uc _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    rewrite <- Ek in RD. wstepl. clear RD.
    wstepl. wstepl; ck.
    zw32_sw CF uc (k + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity).
    wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    pose proof (dinv_L29_step L d i sym tt0 DI ltac:(lia)) as DI'. unfold l29_d', l29_v, l29_k, l29_uc in DI'.
    rewrite <- Euc, <- Ek, <- Ev in DI'.
    pose proof (dpureF_set_tt _ _ _ _ _ _ k v DP ltac:(lia)) as DP'.
    wstepl; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      clear SEPtt. revive_smF SMALL MUL WML LIN DP.
      blk_goal (d_set_cftab (d_set_tt d (zset (d_tt d) k v)) (zset (d_cftab d) uc (k + 1))).
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SMALL.
      pose proof (NXT ltac:(lia)) as NX. unfold L29cF in NX.
      subst v. subst k. subst uc.
      kq_fold. enter_cutF NX DP'.
      exact DI'.
    - (* [comment removed for export] *)
      wstepl. wstepl.
      clear SEPtt. revive_smF SMALL MUL WML LIN DP.
      blk_goal (d_set_cftab (d_set_tt d (zset (d_tt d) k v)) (zset (d_cftab d) uc (k + 1))).
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SMALL.
      pose proof (LAST ltac:(lia)) as NX. unfold AFTcF in NX.
      replace (i + 1)%Z with (sv_nblock L) in KQ by lia. rewrite (K_L29_exit F L) in KQ.
      replace (i + 1)%Z with (sv_nblock L) in DI' by lia.
      subst v. subst k. subst uc.
      kq_fold. enter_cutF NX DP'.
      exact DI'.
  Time Qed.

  Lemma S0F_U12_L29_all : (1 <= nb)%Z -> AFTcF -> L29cF 0.
  Proof.
    intros Hn LAST.
    assert (G : forall k : nat, (Z.of_nat k < nb)%Z -> L29cF (nb - 1 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply S0F_U12_L29; [lia| intros; exfalso; lia| intros _; exact LAST].
      - apply S0F_U12_L29; [lia| intros _| intros; exfalso; lia].
        replace (nb - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (nb - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G (Z.to_nat (nb - 1)) ltac:(lia)) as G0.
    replace (nb - 1 - Z.of_nat (Z.to_nat (nb - 1)))%Z with 0%Z in G0 by lia. exact G0.
  Qed.
  End FA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U12_HFAST : (forall L s J sym tt0, AFTcF L s J sym tt0) -> S0F_cut_HFAST A F.
  Proof.
    intros AFT. unfold S0F_cut_HFAST. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    cps_pose DI as (EOB & ORIG & CFP & TS & SM0). cps_pose EOB as (NB1 & NB9 & SYMB & HIST & HDR).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM0 in SMALL. symmetry in SMALL.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP. unfold drep in RP. destruct RP as (TTR & _).
    pose proof (dinv_L29_entry L d DI TTR) as DI0.
    prepS DM MU DP SMALL.
    pose proof (act_tt_s _ _ AOK SMALL) as [[TT0 TT1] _]. pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG.
    hide_all_but_at [S + 3152; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite K_HFAST_L29 in KQ.
    wstepl; if_cases K0; zify_cond_z K0; [exfalso; lia|]. (* [comment removed for export] *)
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    bdec. revive_all MUL WML AOK. fold_MU MU SMALL.
    pose proof (S0F_U12_L29_all L s J (bsym d) (zget (d_tt d)) ltac:(lia) (AFT L s J _ _)) as NX. unfold L29cF in NX.
    kq_fold. enter_cutF NX DP.
    exact DI0.
  Time Qed.
End R.
End ACeilS1.
