(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV B0_cmp_msV B0_b2c_cbV B0_b2c_hcV B0_b2c_hcA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0_cmp_prep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma copy_output_progress : forall f e z p,
  copy_output f e z p = let '(e1, z1, q1) := copy_output f e z false in (e1, z1, p || q1).
Proof.
  induction f as [|f IH]; intros e z p; cbn [copy_output].
  - rewrite Bool.orb_false_r. reflexivity.
  - destruct (z_avail_out z =? 0)%Z; [rewrite Bool.orb_false_r; reflexivity|].
    destruct (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z; [rewrite Bool.orb_false_r; reflexivity|].
    destruct (inc64 _ _) as [lo' hi']. rewrite (IH _ _ true).
    destruct (copy_output f _ _ false) as [[e1 z1] q1]. rewrite Bool.orb_true_r. reflexivity.
Qed.

Section B0HCD.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (OB : list byte) (P STRM lo : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x62b000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z. Hypothesis EIMG : (0x62b000 <= E)%Z.
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo + 16 <= P)%Z. Hypothesis PHI : (P + 288 <= 18446744073709551616)%Z.
  Hypothesis OOK : out_okB (aci_c B0C) cx ob on. Hypothesis LOB : Z.of_nat (length OB) = on.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80. Hypothesis SOS : apartv ob on STRM 80.

  (* [comment removed for export] *)
  Notation AFTR ra t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 t3 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 92)) (Z_to_bv 64 (E + 96)) t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) (Z_to_bv 64 1) s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB t3 (Z_to_bv 64 (E + 16)) t5 t6).
  Notation TOPR s1 a0 a1 a4 a5 a6 a7 s2 s3 s7 t6 :=
    (AFTR (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 108)) s1 a0 a1 (Z_to_bv 64 (E + 12)) (Z_to_bv 64 (SHE + 1)) a4 a5 a6 a7 s2 s3 s7 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (E + 112)) t6).

  Ltac hcbn := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd bw_buff bw_live bw_numZ hc_prep_a].
  (* [comment removed for export] *)
  Ltac hci_facts HI :=
    let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    pose proof (HCIB_mode _ _ _ _ _ HI) as MD; pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD.

  Definition haft_W : list (Z * Z) := [(E + 12, E + 16); (E + 108, E + 124); (E + 128, E + 384); (E + 648, E + 652); (E + 660, E + 664); (P - 16, P); (P + 72, P + 80)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hc_aft : forall g e z (pin pout itb : bool) (m : amem) (v64 v80 v88 : word) (ra t2 s1 a1 a2 a5 a6 a7 s2 s7 t3 t5 t6 : word),
    e_state e = BZ_S_OUTPUT -> (z_avail_out z = 0 \/ bw_numZ (e_bw e) <= e_state_out_pos e)%Z ->
    HCXB cx on g e z ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr b0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
    rw_cells b0segs m P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout)) v80 v88) -> stk b0segs m lo P -> mem_inv b0segs m -> aconsts B0C m ->
    shzW b0segs haft_W m E (E + ESTATE_SIZE) ->
    (forall m' (a0' a1' a2' s2' : word),
        hc_aft e z (pout || itb) = (e, z, pout || itb, true) ->
        rw_cells b0segs m' E (EHEAD1 cx g e) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
        u8arr b0segs m' (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
        rw_cells b0segs m' P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z (pout || itb))) v80 v88) -> stk b0segs m' lo P -> mem_inv b0segs m' ->
        munch haft_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (AFTR ra t2 s1 a0' a1' a2' (Z_to_bv 64 (Z.b2z itb)) (Z_to_bv 64 (SHE + 15)) a5 a6 a7 s2' (Z_to_bv 64 (Z.b2z pin)) s7 t3 t5 t6)
                         F (Z_to_bv 64 0x834f4) fc None m' (seg_rom b0segs))) ->
    (forall m' (a1' a4' a5' a6' a7' s2' : word),
        hc_aft e z (pout || itb) = (hc_prep e, z, pout || itb, false) -> HCXB cx on g (hc_prep e) z ->
        rw_cells b0segs m' E (EHEAD1 cx g (hc_prep e)) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g (hc_prep e)) ->
        u8arr b0segs m' (E + 128) (ovb (e_inUse (hc_prep e)) (jseg J 128 256) 256) ->
        rw_cells b0segs m' P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z (pout || itb))) v80 v88) -> stk b0segs m' lo P -> mem_inv b0segs m' ->
        munch haft_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (TOPR s1 (Z_to_bv 64 4) a1' a4' a5' a6' a7' s2' (Z_to_bv 64 (Z.b2z pin)) s7 t6) F (Z_to_bv 64 0x829a8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (AFTR ra t2 s1 (Z_to_bv 64 (SHE + -2147450866)) a1 a2 (Z_to_bv 64 (Z.b2z itb)) (Z_to_bv 64 (SHE + -2147450865)) a5 a6 a7 s2 (Z_to_bv 64 (Z.b2z pin)) s7 t3 t5 t6)
                     F (Z_to_bv 64 0x82850) fc None m (seg_rom b0segs)).
  Proof.
    intros g e z pin pout itb m v64 v80 v88 ra t2 s1 a1 a2 a5 a6 a7 s2 s7 t3 t5 t6 STO EXO HX EH1 EH2 INU SL ST MI AC SHe KR KM.
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI. destruct MD as (MD & GA & AIE).
    cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL).
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (proj2 AE : saddr E SHE) as AEs. pose proof (proj1 AE) as EM8. pose proof (proj1 AS) as SM8.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range itb) as BI. pose proof (b2z_range pin) as BPI.
    pose proof (munch_refl haft_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold haft_W in MU, SHe.
    unfold EHEAD1 in EH1. rewrite GA, MD, <- ESTRM in EH1. unfold EHEAD2 in EH2. unfold hc_slots in SL.
    (* [comment removed for export] *)
    brun.
    try rewrite (sx32_of_Z (e_state_out_pos e)) by lia. try rewrite (sx32_of_Z (bw_numZ (e_bw e))) by lia.
    rewrite (lor_b2z itb pout), (Bool.orb_comm itb pout) in SL |- *.
    if_cases KP; zify_cond_z KP.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KR mm _ _ _ _) end;
        [ st_eq | unfold hc_aft; replace (e_state_out_pos e <? bw_numZ (e_bw e))%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
        | unfold EHEAD1; rewrite GA, MD, <- ESTRM; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | unfold hc_slots; exact SL | exact ST | assumption | unfold haft_W; exact MU | exact WM ]. }
    assert (T1 : (e_state_out_pos e <? bw_numZ (e_bw e))%Z = false) by (apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    assert (PREP : forall (mj : amem) (x10 x11 : word),
      ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false ->
      rw_cells b0segs mj E (EHEAD1 cx g e) -> rw_cells b0segs mj (E + 640) (EHEAD2 cx g e) ->
      u8arr b0segs mj (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
      rw_cells b0segs mj P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z (pout || itb))) v80 v88) -> stk b0segs mj lo P -> mem_inv b0segs mj -> aconsts B0C mj ->
      munch haft_W m mj -> wmono b0segs m mj ->
      evt b0segs Q (MS (AFTR ra t2 s1 x10 x11 (Z_to_bv 64 (Z.b2z (pout || itb))) (Z_to_bv 64 (Z.b2z itb)) (Z_to_bv 64 (SHE + 15)) a5 a6 a7 (Z_to_bv 64 (SHE + -2147450878)) (Z_to_bv 64 (Z.b2z pin)) s7 t3 t5 t6)
                       F (Z_to_bv 64 0x828e8) fc None mj (seg_rom b0segs))).
    { clear EH1 EH2 INU SL ST MI MU WM GOT SBV. intros mj x10 x11 NF EH1 EH2 INU SL ST MI ACj MU WM. unfold haft_W in MU.
      pose proof (hlB_prep _ _ LAWS cx on g e z HX STO ltac:(lia) NF) as HX'.
      unfold EHEAD1 in EH1. rewrite GA, MD, <- ESTRM in EH1. unfold EHEAD2 in EH2. unfold hc_slots in SL.
      (* [comment removed for export] *)
      pose proof ACj as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
      (* [comment removed for export] *)
      brun_to 0x81e74%Z.
      (* [comment removed for export] *)
      destruct (rw_cells_cutZ b0segs _ E _ 19%nat EH1) as [EHa EHr]. cbn [firstn skipn cells_size csize Nat.add] in EHa, EHr. change (Z.of_nat 108) with 108%Z in EHr.
      destruct (rw_cells_cutZ b0segs _ (E + 108) _ 4%nat EHr) as [EHm EHb]. cbn [firstn skipn cells_size csize Nat.add] in EHm, EHb.
      replace (E + 108 + Z.of_nat 16)%Z with (E + 124)%Z in EHb by lia. clear EH1 EHr.
      destruct (rw_cells_cutZ b0segs _ (E + 640) _ 2%nat EH2) as [E2a E2r]. cbn [firstn skipn cells_size csize Nat.add] in E2a, E2r.
      replace (E + 640 + Z.of_nat 8)%Z with (E + 648)%Z in E2r by lia.
      destruct (rw_cells_cutZ b0segs _ (E + 648) _ 1%nat E2r) as [E2c E2s]. cbn [firstn skipn cells_size csize Nat.add] in E2c, E2s.
      replace (E + 648 + Z.of_nat 4)%Z with (E + 652)%Z in E2s by lia.
      destruct (rw_cells_cutZ b0segs _ (E + 652) _ 2%nat E2s) as [E2d E2t]. cbn [firstn skipn cells_size csize Nat.add] in E2d, E2t.
      replace (E + 652 + Z.of_nat 8)%Z with (E + 660)%Z in E2t by lia.
      destruct (rw_cells_cutZ b0segs _ (E + 660) _ 1%nat E2t) as [E2n E2u]. cbn [firstn skipn cells_size csize Nat.add] in E2n, E2u.
      replace (E + 660 + Z.of_nat 4)%Z with (E + 664)%Z in E2u by lia. clear EH2 E2r E2s E2t.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (B0_cmp_prep.B0_prep_P Q E lo gp tp F fc EM8 ltac:(lia) ltac:(unfold CEILv; lia) ltac:(unfold CEILv; lia) P mm (e_inUse e) (jseg J 128 256) _ _ _ _ _ (e_blockNo e));
          [ lia | exact EHm | exact INU | exact E2c | exact E2n | lia | exact MI | exact ST | lia | exact ACj
          | eapply (shzW_sub b0segs _ _ m mm); [exact SHe| exact MU| unfold B0_cmp_prep.prep_W; a_sub_fp| lia| lia] |] end.
      clear EHm INU E2c E2n ST MI.
      intros m' a0' a1' a2' a3' a4' a5' a6' a7' EHm INU E2c E2n MI' ST MU' WM'. unfold B0_cmp_prep.prep_W in MU'.
      lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU' WM' end. clear MU' WM'.
      rewrite (ret_pc_even 0x828f0 ltac:(lia) eq_refl).
      (* [comment removed for export] *)
      pose proof (rw_cells_glue b0segs m' (E + 108) _ _ (E + 124) EHm EHb ltac:(cbn [cells_size csize Nat.add]; lia)) as EHr.
      pose proof (rw_cells_glue b0segs m' E _ _ (E + 108) EHa EHr ltac:(cbn [cells_size csize Nat.add]; lia)) as EH1. cbn [app] in EH1. clear EHa EHm EHb EHr.
      pose proof (rw_cells_glue b0segs m' (E + 660) _ _ (E + 664) E2n E2u ltac:(cbn [cells_size csize Nat.add]; lia)) as E2t.
      pose proof (rw_cells_glue b0segs m' (E + 652) _ _ (E + 660) E2d E2t ltac:(cbn [cells_size csize Nat.add]; lia)) as E2s.
      pose proof (rw_cells_glue b0segs m' (E + 648) _ _ (E + 652) E2c E2s ltac:(cbn [cells_size csize Nat.add]; lia)) as E2r.
      pose proof (rw_cells_glue b0segs m' (E + 640) _ _ (E + 648) E2a E2r ltac:(cbn [cells_size csize Nat.add]; lia)) as EH2. cbn [app] in EH2. clear E2a E2c E2d E2n E2u E2t E2s E2r.
      (* [comment removed for export] *)
      brun_to 0x829a8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KM mm _ _ _ _ _ _) end;
        [ st_eq
        | unfold hc_aft; rewrite T1; rewrite NF; unfold hc_prep, prepare_new_block; hcbn; hcbn; rewrite MD; cbn [Z.eqb Pos.eqb BZ_M_FLUSHING andb]; reflexivity
        | exact HX'
        | rewrite hc_prep_of_a; unfold EHEAD1; hcbn; rewrite GA, MD, <- ESTRM; unfold BZ_S_INPUT; first [exact EH1 | cells_eq_by EH1]
        | rewrite hc_prep_of_a; unfold EHEAD2; hcbn; unfold crc_init; first [exact EH2 | cells_eq_by EH2]
        | rewrite hc_prep_of_a; hcbn; exact INU
        | unfold hc_slots; exact SL | exact ST | exact MI' | unfold haft_W; exact MU | exact WM ]. }
    idtac "PREP done".
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (e_avail_in_expect e)) by lia. sh_norm.
    if_cases KE; zify_cond_z KE.
    { assert (NF : ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false).
      { replace (e_avail_in_expect e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_false_r. reflexivity. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (PREP mm _ _ NF) end;
        [ st_eq | unfold EHEAD1; rewrite GA, MD, <- ESTRM; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | unfold hc_slots; exact SL | exact ST | assumption | split; assumption | unfold haft_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (e_state_in_ch e)) by lia.
    if_cases KC; zify_cond_z KC.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KR mm _ _ _ _) end;
        [ st_eq
        | unfold hc_aft; rewrite T1; unfold isempty_RL_e, isempty_RL, est_rl; hcbn; rewrite MD;
          replace (e_avail_in_expect e =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          cbn [Z.eqb Pos.eqb BZ_M_FINISHING andb]; replace (e_state_in_ch e <? 256)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | unfold EHEAD1; rewrite GA, MD, <- ESTRM; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | unfold hc_slots; exact SL | exact ST | assumption | unfold haft_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (e_state_in_len e)) by lia.
    if_cases KL; zify_cond_z KL.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KR mm _ _ _ _) end;
        [ st_eq
        | unfold hc_aft; rewrite T1; unfold isempty_RL_e, isempty_RL, est_rl; hcbn; rewrite MD;
          replace (e_avail_in_expect e =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          cbn [Z.eqb Pos.eqb BZ_M_FINISHING andb]; replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia);
          replace (0 <? e_state_in_len e)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | unfold EHEAD1; rewrite GA, MD, <- ESTRM; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | unfold hc_slots; exact SL | exact ST | assumption | unfold haft_W; exact MU | exact WM ]. }
    assert (NF : ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false).
    { unfold isempty_RL_e, isempty_RL, est_rl. hcbn.
      replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      replace (0 <? e_state_in_len e)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb]. apply Bool.andb_false_r. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (PREP mm _ _ NF) end;
      [ st_eq | unfold EHEAD1; rewrite GA, MD, <- ESTRM; exact EH1 | unfold EHEAD2; exact EH2 | exact INU | unfold hc_slots; exact SL | exact ST | assumption | split; assumption | unfold haft_W; exact MU | exact WM ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hco_W : list (Z * Z) :=
    [(E + 12, E + 16); (E + 108, E + 124); (E + 128, E + 384); (E + 648, E + 652); (E + 660, E + 664); (STRM + 24, STRM + 44); (ob, ob + on); (P - 16, P); (P + 72, P + 80)]%Z.

  Lemma B0_hc_out : forall g e z (pin pout : bool) (ni : Z) (m : amem) (v64 v80 v88 : word) (s1 a0 a1 a4 a5 a6 a7 s2 s7 t6 : word),
    e_state e = BZ_S_OUTPUT -> HCXB cx on g e z ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr b0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
    rw_cells b0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> u8arr b0segs m ob (outb (z_outr z) OB) ->
    rw_cells b0segs m P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout)) v80 v88) -> stk b0segs m lo P ->
    u8arrW hco_W m A2 (zb8 (e_arr2 e) ARR2_SIZE) -> mem_inv b0segs m -> acoW hco_W m ->
    shzW b0segs hco_W m E (E + ESTATE_SIZE) -> shzW b0segs hco_W m STRM (STRM + 80) -> shzW b0segs hco_W m A2 (A2 + ARR2_SIZE) -> shpW b0segs hco_W m ob (ob + on) ->
    (forall e1 z1 pout1 m' (a0' a1' a2' a3' a4' a5' a6' s2' : word),
        hc_out e z pout = (e1, z1, pout1, true) -> HCXB cx on g e1 z1 -> z_in z1 = z_in z -> z_avail_in z1 = z_avail_in z -> e_arr2 e1 = e_arr2 e ->
        rw_cells b0segs m' E (EHEAD1 cx g e1) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e1) ->
        u8arr b0segs m' (E + 128) (ovb (e_inUse e1) (jseg J 128 256) 256) ->
        rw_cells b0segs m' STRM (STRMB cx ob on dbza dbzfr z1 ni p1 p2) -> u8arr b0segs m' ob (outb (z_outr z1) OB) ->
        rw_cells b0segs m' P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout1)) v80 v88) -> stk b0segs m' lo P -> mem_inv b0segs m' ->
        munch hco_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (AFTR (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 108)) s1 a0' a1' a2' a3' a4' a5' a6' a7 s2' (Z_to_bv 64 (Z.b2z pin)) s7 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (E + 112)) t6)
                         F (Z_to_bv 64 0x834f4) fc None m' (seg_rom b0segs))) ->
    (forall e1 z1 pout1 m' (a1' a4' a5' a6' a7' s2' : word),
        hc_out e z pout = (hc_prep e1, z1, pout1, false) -> HCXB cx on g (hc_prep e1) z1 -> z_in z1 = z_in z -> z_avail_in z1 = z_avail_in z -> e_arr2 e1 = e_arr2 e ->
        rw_cells b0segs m' E (EHEAD1 cx g (hc_prep e1)) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g (hc_prep e1)) ->
        u8arr b0segs m' (E + 128) (ovb (e_inUse (hc_prep e1)) (jseg J 128 256) 256) ->
        rw_cells b0segs m' STRM (STRMB cx ob on dbza dbzfr z1 ni p1 p2) -> u8arr b0segs m' ob (outb (z_outr z1) OB) ->
        rw_cells b0segs m' P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout1)) v80 v88) -> stk b0segs m' lo P -> mem_inv b0segs m' ->
        munch hco_W m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (TOPR s1 (Z_to_bv 64 4) a1' a4' a5' a6' a7' s2' (Z_to_bv 64 (Z.b2z pin)) s7 t6) F (Z_to_bv 64 0x829a8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (TOPR s1 a0 a1 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.b2z pin)) s7 t6) F (Z_to_bv 64 0x825d4) fc None m (seg_rom b0segs)).
  Proof.
    intros g e z pin pout ni m v64 v80 v88 s1 a0 a1 a4 a5 a6 a7 s2 s7 t6 STO HX EH1 EH2 INU SM OBM SL ST VA2 MI VAC SHe SHs SH2 SHo KR KI.
    pose proof EH1 as EH1f. pose proof SM as SMf. pose proof SHe as SHe0. pose proof SHs as SHs0.
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI. destruct MD as (MD & GA & AIE).
    cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL).
    cb_ranges CX.
    pose proof OOK as OOK'. unfold out_okB, apart, img_apart in OOK'. cbn [ci_hi aci_c B0C] in OOK'. cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO).
    unfold CEILv, CEIL, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj2 AE : saddr E SHE) as AEs. pose proof (proj1 AE) as EM8. pose proof (proj1 AS) as SM8.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BPI.
    pose proof (munch_refl hco_W m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold hco_W in MU, SHe, SHs.
    assert (DJO : forall outr, (Z.of_nat (length outr) <= on)%Z -> disjoint_from haft_W ob (Z.of_nat (length (outb outr OB)))).
    { intros outr Ho. rewrite (outb_length outr OB on LOB Ho). unfold haft_W. cbn [disjoint_from]. clear - SO1 XE0 XE1 RO1 RO2 RO3 PLO LLO LONN. unfold id in SO1. lia. }
    rewrite hc_out_aft in KR, KI.
    replace (Z.to_nat (z_avail_out z) + 1)%nat with (S (Z.to_nat (z_avail_out z))) in KR, KI by lia.
    rewrite (copy_output_progress (S (Z.to_nat (z_avail_out z))) e z pout) in KR, KI.
    (* [comment removed for export] *)
    assert (AFT : forall e' z' (itb : bool) (mj : amem) (x11 x12 x15 x16 : word),
      e_state e' = BZ_S_OUTPUT -> (z_avail_out z' = 0 \/ bw_numZ (e_bw e') <= e_state_out_pos e')%Z ->
      HCXB cx on g e' z' -> z_in z' = z_in z -> z_avail_in z' = z_avail_in z -> e_arr2 e' = e_arr2 e ->
      copy_output (S (Z.to_nat (z_avail_out z))) e z false = (e', z', itb) ->
      rw_cells b0segs mj E (EHEAD1 cx g e') -> rw_cells b0segs mj (E + 640) (EHEAD2 cx g e') -> u8arr b0segs mj (E + 128) (ovb (e_inUse e') (jseg J 128 256) 256) ->
      rw_cells b0segs mj STRM (STRMB cx ob on dbza dbzfr z' ni p1 p2) -> u8arr b0segs mj ob (outb (z_outr z') OB) ->
      rw_cells b0segs mj P (hc_slots E SHE v64 (Z_to_bv 64 (Z.b2z pout)) v80 v88) -> stk b0segs mj lo P ->
      mem_inv b0segs mj -> munch hco_W m mj -> wmono b0segs m mj ->
      evt b0segs Q (MS (AFTR (Z_to_bv 64 (SHE + 14)) (Z_to_bv 64 (E + 108)) s1 (Z_to_bv 64 (SHE + -2147450866)) x11 x12 (Z_to_bv 64 (Z.b2z itb)) (Z_to_bv 64 (SHE + -2147450865)) x15 x16 a7
                            s2 (Z_to_bv 64 (Z.b2z pin)) s7 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (E + 112)) t6)
                       F (Z_to_bv 64 0x82850) fc None mj (seg_rom b0segs))).
    { clear EH1 EH1f EH2 INU SM SMf OBM SL ST MI MU WM. intros e' z' itb mj x11 x12 x15 x16 ST' EX' HXn ZI' ZA' AR' CO' EH1 EH2 INU SM OBM SL ST MI MU WM.
      rewrite CO' in KR, KI.
      pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HXn) as HI'. pose proof (HCIB_avail_out _ _ _ _ _ HI') as (AOR' & OLEN').
      unfold hco_W in MU.
      eapply (B0_hc_aft g e' z' pin pout itb mj v64 v80 v88); [ exact ST' | exact EX' | exact HXn | exact EH1 | exact EH2 | exact INU | exact SL | exact ST | exact MI
        | exact (VAC mj MU)
        | eapply (shzW_sub b0segs _ _ m mj _ _ _ _ SHe0 MU); [unfold hco_W, haft_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia] | |].
      - intros m' a0' a1' a2' s2' HA EH1' EH2' INU' SL' STK' MI' MU' WM'.
        pose proof (u8arr_transport b0segs _ mj m' ob _ OBM MU' WM' (DJO (z_outr z') ltac:(lia))) as OBM'.
        unfold STRMB in SM. clear EH1 EH2 INU SL ST OBM MI. unfold haft_W in MU'. transport_after_call b0segs mj m' MU' WM'.
        eapply (KR e' z' (pout || itb) m'); [exact HA | exact HXn | exact ZI' | exact ZA' | exact AR' | exact EH1' | exact EH2' | exact INU' | unfold STRMB; exact SM | exact OBM' | exact SL' | exact STK' | exact MI'
          | unfold hco_W; exact MU | exact WM].
      - intros m' a1' x4 x5 x6 x7 s2' HA HX' EH1' EH2' INU' SL' STK' MI' MU' WM'.
        pose proof (u8arr_transport b0segs _ mj m' ob _ OBM MU' WM' (DJO (z_outr z') ltac:(lia))) as OBM'.
        unfold STRMB in SM. clear EH1 EH2 INU SL ST OBM MI. unfold haft_W in MU'. transport_after_call b0segs mj m' MU' WM'.
        eapply (KI e' z' (pout || itb) m'); [exact HA | exact HX' | exact ZI' | exact ZA' | exact AR' | exact EH1' | exact EH2' | exact INU' | unfold STRMB; exact SM | exact OBM' | exact SL' | exact STK' | exact MI'
          | unfold hco_W; exact MU | exact WM]. }
    idtac "AFT done".
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM, STO in EH1. unfold BZ_S_OUTPUT in EH1. unfold STRMB in SM. unfold hc_slots in SL.
    (* [comment removed for export] *)
    brun_to 0x82608%Z.
    pose proof SLO as SLO'. pose proof SHI as SHI'. pose proof SES as SES'. pose proof SOS as SOS'. pose proof AS as AS'. rewrite ESTRM in SLO', SHI', SES', SOS', AS'.
    pose proof SMf as SMc. rewrite ESTRM in SMc.
    enter_with (B0_b2c_hcA.B0_co_loop cx Q HCXB CBFACTS SHE SHS ob on dbza dbzfr p1 p2 OB gp tp F fc CX SEP LAWS AE AS' SLO' SHI' OOK LOB SES' SOS'
                  (S (Z.to_nat (z_avail_out z))) g e z false ni m m);
      [ st_eq | lia | exact STO | exact HX | exact EH1f | exact SMc | exact OBM
      | intros mv MUv; apply VA2; eapply munch_weaken; [| exact MUv]; unfold B0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp
      | exact MI | apply munch_refl | apply wmono_refl
      | eapply (shzW_sub b0segs _ _ m m _ _ _ _ SHe0 (munch_refl _ _)); [unfold B0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
      | rewrite <- ESTRM; eapply (shzW_sub b0segs _ _ m m _ _ _ _ SHs0 (munch_refl _ _)); [unfold B0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs _ _ m m _ _ _ _ SH2 (munch_refl _ _)); [unfold B0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| lia]
      | eapply (shpW_sub b0segs _ _ m m _ _ _ _ SHo (munch_refl _ _)); [unfold B0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp| lia| lia]
      | ].
    intros e' z' p' m' a2' a5' a6' CO' ST' EX' HXn ZI' ZA' AR' EH1' SM' OBM' MI' MU' WM'.
    rewrite <- ESTRM in SM'.
    assert (MUh : munch hco_W m m') by (eapply munch_weaken; [| exact MU']; unfold B0_b2c_hcA.co_W, hco_W; rewrite <- ESTRM; a_sub_fp).
    unfold EHEAD2 in EH2.
    clear EH1 EH1f SM SMf SMc OBM MI. unfold B0_b2c_hcA.co_W in MU'. rewrite <- ESTRM in MU'. transport_after_call b0segs m m' MU' WM'.
    enter_with (AFT e' z' p' m' _ _ _ _); [ st_eq | exact ST' | exact EX' | exact HXn | exact ZI' | exact ZA' | exact AR' | exact CO'
      | exact EH1'
      | pose proof (copy_output_frame (S (Z.to_nat (z_avail_out z))) e z false) as FRM; rewrite CO' in FRM; cbn [fst] in FRM; rewrite FRM; unfold EHEAD2; hcbn; exact EH2
      | pose proof (copy_output_frame (S (Z.to_nat (z_avail_out z))) e z false) as FRM; rewrite CO' in FRM; cbn [fst] in FRM; rewrite FRM; hcbn; exact INU
      | exact SM' | exact OBM' | unfold hc_slots; exact SL | exact ST | exact MI' | exact MUh | exact WM' ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End B0HCD.

End ACeilS1.
