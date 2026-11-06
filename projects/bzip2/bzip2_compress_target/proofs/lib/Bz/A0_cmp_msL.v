(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Import BzCSewC.BzCSewB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW A0_cmp_msS A0_cmp_msK.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma app_fp_WT1 : forall X Y SHF, msenv_ok X -> amenv_ok X Y -> amenv_offsh X Y -> amenv_shx X Y SHF ->
  app_fp [(me_A1 X, me_A1 X + ARR1_SIZE); (am_P Y + 40, am_P Y + 104); (am_P Y + 184, am_P Y + 192); (am_P Y + 216, am_P Y + 384);
          (am_P Y + 436, am_P Y + 440); (am_P Y - 16, am_P Y); (am_SLO Y, am_SLO Y + 400); (am_SHI Y, am_SHI Y + 400); (am_SD Y, am_SD Y + 400)]%Z.
Proof.
  intros X Y SHF XOK YOK YOFF SHX. pose proof alloc_ceiling_range as ACR.
  pose proof (amsh_P X Y SHF SHX) as [_ PH].
  unfold msenv_ok, CEILm in XOK. cbv zeta in XOK. unfold amenv_ok, CEILm in YOK. cbv zeta in YOK.
  unfold amenv_offsh, SH_LO, SH_HI in YOFF. unfold SH_HI in PH.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YOFF as (O1 & O2 & O3 & O4).
  cbn [app_fp]. unfold SH_LO, SH_HI. repeat split; lia.
Qed.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation WQA := [(A1, A1 + ARR1_SIZE); (P + 216, P + 384); (P + 436, P + 440); (P - 16, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.
  (* [comment removed for export] *)
  Notation WQC := [(A1, A1 + ARR1_SIZE); (P + 40, P + 104); (P + 184, P + 192); (P + 216, P + 384); (P + 436, P + 440); (P - 16, P);
                   (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400); (SHF + 4, SHF + 170)]%Z.
  Notation WT1 := [(A1, A1 + ARR1_SIZE); (P + 40, P + 104); (P + 184, P + 192); (P + 216, P + 384); (P + 436, P + 440); (P - 16, P);
                   (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.

  Ltac shc3_move H MU WM H' := pose proof (shc3_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.

  (* [comment removed for export] *)
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  (* [comment removed for export] *)
  Tactic Notation "ovw_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (ovw ?a ?J ?n) =>
        let H := fresh "ARRw" in
        pose proof (ovw_write segs m A a J n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.

  (* [comment removed for export] *)
  Lemma A0_qcall : forall (j lo hi b : Z) (a1 a2 sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte)
      (w40 w48 w56 w72 w80 w88 w96 : word) (w216 w224 w232 w240 w256 w264 w288 w320 w328 w336 w344 w352 w360 w368 w376 : word)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q0 := MQS a1 1 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd b false in
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= b < 2147483648)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q0 in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop (mqs_fuel lo hi) a2 qo n q0) <= 0 \/ mq_exit (mqs_loop (mqs_fuel lo hi) a2 qo n q0) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr a0segs m SLO (ovw sl Jlo 100) -> u32arr a0segs m SHI (ovw sh Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 40) (scl_cells X (mkSCL w40 w48 w56 w72 w80 w88 w96)) -> rw_cells a0segs m (P + 184) [C8 (Z_to_bv 64 hi)] ->
    rw_cells a0segs m (P + 216) (scq_cells Y (mkSCQ w216 w224 w232 w240 w256 w264 (Z_to_bv 64 lo) w288 w320 w328 w336 w344 w352 w360 w368 w376)) ->
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P ->
    id (rw_cells a0segs m (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m ->
    munch WQC me m -> wmono a0segs me m -> mviews X Y SHF WQC me ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (b' : Z) (v72 v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376 : word)
            (y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' 0 sl' sh' sd' nl' nh' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw sl' Jlo 100) -> u32arr a0segs m' SHI (ovw sh' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 40) (scl_cells X (mkSCL x26 (Z_to_bv 64 j) x25 v72 w80 w88 w96)) -> rw_cells a0segs m' (P + 184) [C8 (Z_to_bv 64 hi)] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ v216 v224 v232 v240 w256 w264 (Z_to_bv 64 lo) (Z_to_bv 64 0) v320 v328 v336 v344 v352 v360 v368 v376)) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P ->
      id (rw_cells a0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m' ->
      munch WQC me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 w96 y14 y15 y16 y17
                            y18 cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) x23 (Z_to_bv 64 j) x25 x26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x999b8) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (qsp' b' : Z) (v216 v224 v232 v240 v288 v320 v328 v336 v344 v352 v360 v368 v376 : word)
            (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' qsp' sl' sh' sd' nl' nh' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw sl' Jlo 100) -> u32arr a0segs m' SHI (ovw sh' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 40) (scl_cells X (mkSCL x26 (Z_to_bv 64 j) x25 w72 w80 w88 w96)) -> rw_cells a0segs m' (P + 184) [C8 (Z_to_bv 64 hi)] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ v216 v224 v232 v240 w256 w264 (Z_to_bv 64 lo) v288 v320 v328 v336 v344 v352 v360 v368 v376)) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P ->
      id (rw_cells a0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m' ->
      munch WQC me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (-8)) y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) x23 y24 y25 y26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 (Z_to_bv 64 2) x23 (Z_to_bv 64 j) x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x987e0) fc None m (seg_rom a0segs)).
  Proof.
    intros j lo hi b a1 a2 sl sh sd nl nh nd Jlo Jhi Jd w40 w48 w56 w72 w80 w88 w96 w216 w224 w232 w240 w256 w264 w288 w320 w328 w336 w344 w352 w360 w368 w376
           x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x25 x26 x27 x28 x29 x30 x31 me m.
    intros q0 Hlo Hlh Hhi Hb OKv FIN A1OK A2OK PR LJlo LJhi LJd AR1 AR2 SLOB SHIB SDB SCL HIC SCQ BUD STK SHC MI MU WM MV Kset Kexit. subst q0.
    msenv_open XOK. amenv_open YOK.
    pose proof (amsx_1_SLO X Y YSX) as AS1l. pose proof (amsx_1_SHI X Y YSX) as AS1h. pose proof (amsx_1_SD X Y YSX) as AS1d.
    pose proof (amsx_2_SLO X Y YSX) as AS2l. pose proof (amsx_2_SHI X Y YSX) as AS2h. pose proof (amsx_2_SD X Y YSX) as AS2d.
    amenv_shx_open X Y SHF YSHX.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    mviews_open MV.
    open_scl_in SCL. open_scq_in SCQ.
    pose proof (munch_refl WT1 m) as MUp. pose proof (wmono_refl a0segs m) as WMp.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (VCK mm MU) as RO_ end. unfold sck_cells in RO_. wstep. clear RO_.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
    enter_with (A0_ms_scope_begin X SHF Q m1 m1 f8b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact SHC1| exact MI| apply munch_refl| apply wmono_refl|].
    intros m2 SHC2 MI2 MU2 WM2. clear SHC1 MI. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    pose proof (app_fp_WT1 X Y SHF XOK YOK YOFF YSHX) as AFt.
    destruct YSF as (AX & _ & _).
    destruct (ams_stack_readers X Y SHF WT1 m2 XOK YOK AX AFt SHC2) as (SHl2 & SHh2 & SHd2).
    change (rw_cells a0segs m2 (SHF + 4) (shc3 z8)) with (id (rw_cells a0segs m2 (SHF + 4) (shc3 z8))) in SHC2.
    pose proof (munch_refl WT1 m2) as MUp. pose proof (wmono_refl a0segs m2) as WMp.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SLO _ 0 _ SLOB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO1 end.
    wstep. ovw_store_at SLOB 0%Z lo (apply unsigned_lit_mod32). try clear SO1.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SHI _ 0 _ SHIB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
    wstep. ovw_store_at SHIB 0%Z hi (apply unsigned_lit_mod32). try clear SO2.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SD _ 0 _ SDB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
    wstep. ovw_store_at SDB 0%Z 2%Z (apply unsigned_lit_mod32). try clear SO3.
    (* [comment removed for export] *)
    wstep. wstep. wstep. lit_store. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (VCC mm MU) as RO_ end. unfold scc_cells in RO_. wstep. clear RO_.
    (* [comment removed for export] *)
    wstep. lit_store. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mq := mm) in * end.
    enter_with (A0_qloop X Y Q XOK XSEP YOK YSX (mqs_fuel lo hi) 1 b a1 a2 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd Jlo Jhi Jd
                  (mkSCQ w216 w224 w232 w240 w256 w264 (Z_to_bv 64 lo) (Z_to_bv 64 0) w320 w328 w336 w344 (Z_to_bv 64 SLO) (Z_to_bv 64 1) w368 w376)
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| | reflexivity| cbn [q352]; f_equal; lia| reflexivity| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SCQ| exact BUD| exact STK| exact MI2| apply munch_refl| apply wmono_refl| | |].
    { intros i Hi. replace i with 0%Z by lia. rewrite !zdef_zset_same. CmpFast.tauto_g. }
    { unfold qviews.
      split; [eapply (frdW_sub a0segs); [exact VCC| exact MU| sub_fp_solve]|].
      split; [eapply (frdW_sub a0segs); [eapply (frdW_cell_at a0segs _ me (P + 152) (sck_cells X Y SHF) 0 _ (P + 152)%Z); [exact VCK| reflexivity| lia]| exact MU| sub_fp_solve]|].
      split; [eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve]|].
      split; [eapply (shzW_sub a0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]|].
      split; [eapply (shzW_sub a0segs); [exact SH2| exact MU| sub_fp_solve| lia| lia]|].
      split; [eapply (shpW_sub a0segs); [exact SHBU| exact MU| sub_fp_solve| lia| lia]|].
      split; [eapply (shzW_sub a0segs); [exact SHIN| exact MU| sub_fp_solve| lia| lia]|].
      split; [eapply (shzW_sub a0segs); [exact SHl2| exact MUp| sub_fp_solve| lia| lia]|].
      split; [eapply (shzW_sub a0segs); [exact SHh2| exact MUp| sub_fp_solve| lia| lia]|].
      eapply (shzW_sub a0segs); [exact SHd2| exact MUp| sub_fp_solve| lia| lia]. }
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' b' v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376
             y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCQ' BUD' STK' MI' MU' WM'. cbn [q256 q264 q272] in SCQ'.
      clear AR1 AR2 SLOB SHIB SDB SCQ BUD STK MI2.
      transport_after_call a0segs mq m' MU' WM'. clear MU' WM'.
      open_scq_in SCQ'.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (VCK mm MU) as RO_ end. unfold sck_cells in RO_. wstep. clear RO_.
      wstep.
      (* [comment removed for export] *)
      shc3_move SHC2 MUp WMp SHC3. clear SHC2 MUp WMp SHl2 SHh2 SHd2.
      enter_with (A0_ms_scope_end1 X SHF Q m' m' z8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact SHC3| exact MI'| apply munch_refl| apply wmono_refl|].
      intros m5 SHC5 MI5 MU5 WM5. clear SHC3 MI'. transport_after_call a0segs m' m5 MU5 WM5. clear MU5 WM5.
      change (rw_cells a0segs m5 (SHF + 4) (shc3 f8b)) with (id (rw_cells a0segs m5 (SHF + 4) (shc3 f8b))) in SHC5.
      pose proof (munch_refl WT1 m5) as MUp. pose proof (wmono_refl a0segs m5) as WMp.
      (* [comment removed for export] *)
      wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia]; exfalso; lia | clear Kb].
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep. wstep.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep. wstep.
      shc3_move SHC5 MUp WMp SHC6. clear SHC5 MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kset mm a1' slo' shi' sd' nlo' nhi' nd' b' _ v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SCL| exact HIC| exact SCQ'| exact BUD'| exact STK'
        | exact SHC6| exact MI5| exact MU| exact WM].
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' v288 v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376
             y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCQ' BUD' STK' MI' MU' WM'. cbn [q256 q264 q272] in SCQ'.
      clear AR1 AR2 SLOB SHIB SDB SCQ BUD STK MI2.
      transport_after_call a0segs mq m' MU' WM'. clear MU' WM'.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (VCK mm MU) as RO_ end. unfold sck_cells in RO_. wstep. clear RO_.
      shc3_move SHC2 MUp WMp SHC3. clear SHC2 MUp WMp SHl2 SHh2 SHd2.
      enter_with (A0_ms_scope_end2 X SHF Q m' m' z8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact SHC3| exact MI'| apply munch_refl| apply wmono_refl|].
      intros m5 SHC5 MI5 MU5 WM5. clear SHC3 MI'. transport_after_call a0segs m' m5 MU5 WM5. clear MU5 WM5.
      change (rw_cells a0segs m5 (SHF + 4) (shc3 f8b)) with (id (rw_cells a0segs m5 (SHF + 4) (shc3 f8b))) in SHC5.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kexit mm a1' slo' shi' sd' nlo' nhi' nd' qsp' b' v216 v224 v232 v240 v288 v320 v328 v336 v344 v352 v360 v368 v376 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SCL| exact HIC| exact SCQ'| exact BUD'| exact STK'
        | exact SHC5| exact MI5| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  Notation WS1 := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (P + 40, P + 104); (P + 184, P + 192); (P + 216, P + 384); (P + 436, P + 440); (P - 16, P);
                   (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400); (SHF + 4, SHF + 170)]%Z.

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.
  Tactic Notation "zw32_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.

  (* [comment removed for export] *)
  Lemma A0_step1 : forall (cnt : nat) (j ss b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte)
      (w40 w48 w56 w72 w80 w88 w184 : word) (sq : scq)
      (x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, j + Z.of_nat k < 256 -> let s' := ms_step1 k qo n ss j s in s_exit s' = false -> step1F qo n ss (j + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) ->
    u32arr a0segs m SLO (ovw sl Jlo 100) -> u32arr a0segs m SHI (ovw sh Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 40) (scl_cells X (mkSCL w40 w48 w56 w72 w80 w88 (Z_to_bv 64 (FT + 1024 * ss)))) -> rw_cells a0segs m (P + 184) [C8 w184] ->
    rw_cells a0segs m (P + 216) (scq_cells Y sq) ->
    rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P ->
    id (rw_cells a0segs m (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m ->
    munch WS1 me m -> wmono a0segs me m -> mviews X Y SHF WS1 me ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (v40 v48 v56 v72 v184 : word) (sq' : scq)
            (y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) ->
      u32arr a0segs m' SLO (ovw sl' Jlo 100) -> u32arr a0segs m' SHI (ovw sh' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 40) (scl_cells X (mkSCL v40 v48 v56 v72 w80 w88 (Z_to_bv 64 (FT + 1024 * ss)))) -> rw_cells a0segs m' (P + 184) [C8 v184] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y sq') ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P ->
      id (rw_cells a0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m' ->
      munch WS1 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 (Z_to_bv 64 (FT + 1024 * ss)) y14 y15 y16 y17
                            y18 cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) (Z_to_bv 64 256) (Z_to_bv 64 ss) (Z_to_bv 64 ss) x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x99a5c) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (v40 v48 v56 v72 v184 : word) (sq' : scq)
            (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) ->
      u32arr a0segs m' SLO (ovw sl' Jlo 100) -> u32arr a0segs m' SHI (ovw sh' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 40) (scl_cells X (mkSCL v40 v48 v56 v72 w80 w88 (Z_to_bv 64 (FT + 1024 * ss)))) -> rw_cells a0segs m' (P + 184) [C8 v184] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y sq') ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P ->
      id (rw_cells a0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m' ->
      munch WS1 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (-8)) y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 (Z_to_bv 64 SHF) (Z_to_bv 64 FT) y24 y25 y26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a260) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 (Z_to_bv 64 (FT + 1024 * ss)) x14 x15 x16 x17
                          x18 cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) (Z_to_bv 64 j) (Z_to_bv 64 ss) (Z_to_bv 64 ss) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x9875c) fc None m (seg_rom a0segs)).
  Proof.
    induction cnt as [|cnt IH].
    { intros. exfalso. lia. }
    intros j ss b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd Jlo Jhi Jd w40 w48 w56 w72 w80 w88 w184 sq
           x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x27 x28 x29 x30 x31 me m.
    intros s Hcnt Hj Hss Hb S1F A1OK A2OK PR LJlo LJhi LJd AR1 AR2 FTB SLOB SHIB SDB SCL HIC SCQ BUD STK SHC MI MU WM MV Knext Kexit. subst s.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_SLO X Y YSX) as AS1l. pose proof (amsx_1_SHI X Y YSX) as AS1h. pose proof (amsx_1_SD X Y YSX) as AS1d.
    pose proof (amsx_2_SLO X Y YSX) as AS2l. pose proof (amsx_2_SHI X Y YSX) as AS2h. pose proof (amsx_2_SD X Y YSX) as AS2d.
    pose proof (amsx_F_SLO X Y YSX) as ASFl. pose proof (amsx_F_SHI X Y YSX) as ASFh. pose proof (amsx_F_SD X Y YSX) as ASFd.
    amenv_shx_open X Y SHF YSHX.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    mviews_open MV.
    set (sb := (Z.shiftl ss 8 + j)%Z). assert (Hsb : sb = (256 * ss + j)%Z) by (subst sb; rewrite shl8; reflexivity).
    (* [comment removed for export] *)
    assert (NEXTK : forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (v40 v48 v56 v72 v184 : word) (sq' : scq)
                (y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) ->
      u32arr a0segs m' SLO (ovw sl' Jlo 100) -> u32arr a0segs m' SHI (ovw sh' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 40) (scl_cells X (mkSCL v40 v48 v56 v72 w80 w88 (Z_to_bv 64 (FT + 1024 * ss)))) -> rw_cells a0segs m' (P + 184) [C8 v184] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y sq') ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P ->
      id (rw_cells a0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m' ->
      munch WS1 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 (Z_to_bv 64 (FT + 1024 * ss)) y14 y15 y16 y17
                            y18 cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) (Z_to_bv 64 j) (Z_to_bv 64 ss) (Z_to_bv 64 ss) x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x999d8) fc None m' (seg_rom a0segs))).
    { intros m' a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' v40 v48 v56 v72 v184 sq' y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31
             EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCL' HIC' SCQ' BUD' STK' SHC' MI' MU' WM'.
      clear AR1 AR2 FTB SLOB SHIB SDB SCL HIC SCQ BUD STK SHC MI MU WM.
      rewrite (EQ cnt) in Knext, Kexit.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc; zify_cond_z Kc.
      - assert (cnt = 0%nat) as -> by lia. cbn [ms_step1] in Knext.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Knext mm a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' v40 v48 v56 v72 v184 sq' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact SCL'| exact HIC'| exact SCQ'
          | exact BUD'| exact STK'| exact SHC'| exact MI'| exact MU'| exact WM'].
      - wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss b' nqs' a1' a2 ft' bd cs ce sl' sh' sd' nl' nh' nd' Jlo Jhi Jd v40 v48 v56 v72 w80 w88 v184 sq'
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| | exact OK'| exact A2OK| exact PR'| exact LJlo| exact LJhi| exact LJd| exact AR1'| exact AR2'| exact FTB'
          | exact SLO'| exact SHI'| exact SD'| exact SCL'| exact HIC'| exact SCQ'| exact BUD'| exact STK'| exact SHC'| exact MI'| exact MU'| exact WM'| exact MV| | ].
        + intros k Hk. pose proof (S1F (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. cbv zeta in Fk. rewrite (EQ k) in Fk. cbv zeta. rewrite Nat2Z.inj_succ in Fk.
          replace (j + 1 + Z.of_nat k)%Z with (j + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
        + intros until 0. intros EQ2 Hb2. eapply Knext; [exact EQ2| lia].
        + exact Kexit. }
    clear IH.
    pose proof (S1F 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [ms_step1] in F0. rewrite Z.add_0_r in F0. unfold step1F in F0.
    cbn [s_ft s_mql s_a1 s_a2 s_budget ml_slo ml_shi ml_sd ml_nlo ml_nhi ml_nd] in F0. fold sb in F0.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    2:{ wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (NEXTK mm a1 ft sl sh sd nl nh nd b nqs w40 w48 w56 w72 w184 sq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| intros k; apply ms_step1_skip; lia| lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLOB| exact SHIB| exact SDB
          | exact SCL| exact HIC| exact SCQ| exact BUD| exact STK| exact SHC| exact MI| exact MU| exact WM]. }
    cps_destruct (F0 ltac:(lia)) as (c0 & c1 & Hc01 & Hc1n & FC0 & FC1 & FQ). clear F0.
    assert (Hc0 : (0 <= c0 < 2097152)%Z) by lia. assert (Hc1 : (0 <= c1 < 2097152)%Z) by lia.
    pose proof (ftcell_cases _ _ Hc0 FC0) as X0. pose proof (ftcell_cases _ _ Hc1 FC1) as X1.
    pose proof (ftcell_clear _ _ Hc0 FC0) as CL0. pose proof (ftcell_clear _ _ Hc1 FC1) as CL1.
    open_scq_in SCQ. open_scl_in SCL.
    (* [comment removed for export] *)
    arun_to 0x98774%Z.
    replace (FT + 1024 * ss + j * 4)%Z with (FT + 4 * sb)%Z by lia.
    pose proof (saddr_intro (FT + 4 * sb)%Z) as ASB. set (SHsb := ((FT + 4 * sb) / 8 + 2147450880)%Z) in *. clearbody SHsb.
    (* [comment removed for export] *)
    assert (SETK : forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (v40 v48 v56 v72 v184 : word)
                (v216 v224 v232 v240 v272 v288 v320 v328 v336 v344 v352 v360 v368 v376 : word)
                (y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 (zset ft sb (Z.lor (zget ft sb) SETMASK)) bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) ->
      (0 <= b' <= b)%Z -> zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft 65537) ->
      u32arr a0segs m' SLO (ovw sl' Jlo 100) -> u32arr a0segs m' SHI (ovw sh' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 40) (scl_cells X (mkSCL v40 v48 v56 v72 w80 w88 (Z_to_bv 64 (FT + 1024 * ss)))) -> rw_cells a0segs m' (P + 184) [C8 v184] ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ v216 v224 v232 v240 (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb)) v272 v288 v320 v328 v336 v344 v352 v360 v368 v376)) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P ->
      id (rw_cells a0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv a0segs m' ->
      munch WS1 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 (Z_to_bv 64 (FT + 1024 * ss)) y14 y15 y16 y17
                            y18 cSB (Z_to_bv 64 256) (Z_to_bv 64 4) (Z_to_bv 64 2) (Z_to_bv 64 FT) (Z_to_bv 64 j) (Z_to_bv 64 ss) (Z_to_bv 64 ss) x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x999b8) fc None m' (seg_rom a0segs))).
    { intros m' a1' sl' sh' sd' nl' nh' nd' b' nqs' v40 v48 v56 v72 v184 v216 v224 v232 v240 v272 v288 v320 v328 v336 v344 v352 v360 v368 v376
             y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31 EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCL' HIC' SCQ' BUD' STK' SHC' MI' MU' WM'.
      clear AR1 AR2 FTB SLOB SHIB SDB SCL HIC SCQ BUD STK SHC MI MU WM. open_scq_in SCQ'. open_scl_in SCL'.
      pose proof (zb8_length a1' ARR1_SIZE ltac:(lia)) as L1'.
      pose proof (ovw_length sl' Jlo 100 ltac:(lia)) as Llo'. pose proof (ovw_length sh' Jhi 100 ltac:(lia)) as Lhi'. pose proof (ovw_length sd' Jd 100 ltac:(lia)) as Ld'.
      pose proof (munch_refl [(FT, FT + 262148)]%Z m') as MUp. pose proof (wmono_refl a0segs m') as WMp.
      (* [comment removed for export] *)
      arun. rd32_at FTB' sb.
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm FT _ sb _ FTB' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store_at FTB' sb (Z.lor (zget ft sb) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
      shc3_move SHC' MUp WMp SHC2. clear SHC' MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (NEXTK mm a1' (zset ft sb (Z.lor (zget ft sb) SETMASK)) sl' sh' sd' nl' nh' nd' b' nqs' v40 v48 v56 v72 v184
                      (mkSCQ v216 v224 v232 v240 (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb)) v272 v288 v320 v328 v336 v344 v352 v360 v368 v376)
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'
        | exact SCL'| exact HIC'| exact SCQ'| exact BUD'| exact STK'| exact SHC2| exact MI'| exact MU'| exact WM']. }
    clear NEXTK.
    pose proof (munch_refl WT1 m) as MUp. pose proof (wmono_refl a0segs m) as WMp.
    (* [comment removed for export] *)
    wstep. arun. rd32_at FTB sb.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    wstep; if_cases Km; [apply negb_true_iff in Km; apply slt42_false in Km; [|lia] | apply negb_false_iff in Km; apply slt42_true in Km; [|lia]].
    2:{ (* [comment removed for export] *)
      wstep. shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd b nqs w40 w48 w56 w72 w184 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLOB| exact SHIB| exact SDB| exact SCL| exact HIC| exact SCQ| exact BUD| exact STK
        | exact SHC1| exact MI| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. left. fold sb.
      destruct X0 as [E0|E0]; [exfalso; lia|]. rewrite E0, <- lor_setmask by lia. apply has_setmask_marked. lia. }
    destruct X0 as [E0|E0]; [|exfalso; lia].
    (* [comment removed for export] *)
    arun_to 0x987a8%Z. ack_rd (FT + 4 * sb + 4)%Z 4%Z. ack_merge.
    rd32_at FTB (sb + 1)%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (VCM mm MU) as RO_ end. wstep. clear RO_.
    wstep. rewrite land_CM64, CL1 by lia.
    wstep. wstep. rewrite E0. wstep.
    rewrite E0 in SCQ. replace (c1 + -1)%Z with (c1 - 1)%Z in * by lia.
    wstep; if_cases Kge; zify_cond_z Kge.
    2:{ (* [comment removed for export] *)
      wstep. shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd b nqs w40 w48 w56 w72 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLOB| exact SHIB| exact SDB| exact SCL| exact HIC| exact SCQ| exact BUD| exact STK
        | exact SHC1| exact MI| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. right. fold sb. rewrite CL0, CL1. lia. }
    (* [comment removed for export] *)
    astep. astep.
    destruct (FQ E0 ltac:(lia)) as [OKv FIN].
    shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mc := mm) in * end.
    enter_with (A0_qcall j c0 (c1 - 1)%Z b a1 a2 sl sh sd nl nh nd Jlo Jhi Jd w40 w48 w56 w72 w80 w88 (Z_to_bv 64 (FT + 1024 * ss))
                  (q216 sq) (q224 sq) (q232 sq) (q240 sq) (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb)) (q288 sq) (q320 sq) (q328 sq) (q336 sq) (q344 sq)
                  (q352 sq) (q360 sq) (q368 sq) (q376 sq)
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mc);
      [st_eq| lia| lia| lia| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SCL| exact HIC| exact SCQ| exact BUD| exact STK| exact SHC1| exact MI
      | apply munch_refl| apply wmono_refl| eapply mviews_sub; [exact MV| exact MU| sub_fp_solve]| |].
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' b' v72 v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376 y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y18 y28 y29 y30 y31.
      intros EQl Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCL' HIC' SCQ' BUD' STK' SHC' MI' MU' WM'.
      clear AR1 AR2 SLOB SHIB SDB SCL HIC SCQ BUD STK SHC1 MI. transport_after_call a0segs mc m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1' sl' sh' sd' nl' nh' nd' b' (nqs + (c1 - 1 - c0 + 1))%Z _ _ _ v72 _ v216 v224 v232 v240 _ _ v320 v328 v336 v344 v352 v360 v368 v376
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact SCL'| exact HIC'| exact SCQ'| exact BUD'| exact STK'
        | exact SHC'| exact MI'| exact MU| exact WM].
      intros k. pose proof (ms_step1_q k qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' 0 sl' sh' sd' nl' nh' nd' b' false ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with false in SQ by (symmetry; apply Z.ltb_ge; lia). exact SQ.
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' qsp' b' v216 v224 v232 v240 v288 v320 v328 v336 v344 v352 v360 v368 v376
             y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y24 y25 y26 y28 y29 y30 y31.
      intros EQl Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCL' HIC' SCQ' BUD' STK' SHC' MI' MU' WM'.
      clear AR1 AR2 SLOB SHIB SDB SCL HIC SCQ BUD STK SHC1 MI. transport_after_call a0segs mc m' MU' WM'. clear MU' WM'.
      eapply (Kexit m' a1' ft sl' sh' sd' nl' nh' nd' b' (nqs + (c1 - 1 - c0 + 1))%Z _ _ _ _ _ _);
        [| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact SCL'| exact HIC'| exact SCQ'| exact BUD'| exact STK'
         | exact SHC'| exact MI'| exact MU| exact WM].
      pose proof (ms_step1_q cnt qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' qsp' sl' sh' sd' nl' nh' nd' b' true ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with true in SQ by (symmetry; apply Z.ltb_lt; lia). exact SQ.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
