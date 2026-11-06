(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_fsS B0_cmp_msV B0_cmp_msW B0_cmp_msS B0_cmp_msK B0_cmp_msX B0_cmp_msF B0_cmp_fsW BzCLemmasMs5.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Ltac sx_norm_all := repeat match goal with |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_of_Z_signed v) by lia end.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id; demod; sx_norm_all.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation NBD := (18446744073709551615 - am_BD Y)%Z.
  Notation WQA := [(A1, A1 + ARR1_SIZE); (P, P + 536); (P - 32, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.
  (* [comment removed for export] *)
  Notation WQC := [(A1, A1 + ARR1_SIZE); (P, P + 536); (P - 32, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400); (SHF + 4, SHF + 170)]%Z.
  Notation WS1 := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (P, P + 536); (P - 32, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400); (SHF + 4, SHF + 170)]%Z.
  Notation SLM q80 q88 q96 q104 q160 q168 q176 q184 q224 q232 q240 q248 q264 q272 q312 q328 q336 q344 q352 q392 q408 q416 q440 q480 :=
    (slm_cells X Y SHF SHn (mkSLQ q80 q88 q96 q104 q160 q168 q176 q184 q224 q232 q240 q248 q264 q272 q312 q328 q336 q344 q352 q392 q408 q416 q440 q480)).
  (* [comment removed for export] *)
  Notation SLS w80 w88 ss sq :=
    (slm_cells X Y SHF SHn (mkSLQ w80 w88 (Z_to_bv 64 ss) (Z_to_bv 64 (ss * 256)) (q160 sq) (q168 sq) (q176 sq) (q184 sq) (q224 sq) (q232 sq) (q240 sq) (q248 sq)
                                  (q264 sq) (q272 sq) (q312 sq) (q328 sq) (q336 sq) (q344 sq) (q352 sq) (q392 sq) (q408 sq) (q416 sq) (q440 sq) (q480 sq))).
  (* [comment removed for export] *)
  Notation RM ss x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s10 t3 :=
    (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 32) s4 (Z_to_bv 64 33) s6 (Z_to_bv 64 18446744073707454463) (Z_to_bv 64 ss) (Z_to_bv 64 (ss * 256)) s10 cSB
         t3 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152)).
  (* [comment removed for export] *)

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
  Lemma B0_qcall : forall (j lo hi b nqs : Z) (a1 a2 sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte)
      (w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480 : word) (nx : nxt)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q0 := MQS a1 1 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd b false in
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= b < 2147483648)%Z -> (0 <= j < 256)%Z ->
    (0 <= nqs /\ nqs + n <= 2147483647)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q0 in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop (mqs_fuel lo hi) a2 qo n q0) <= 0 \/ mq_exit (mqs_loop (mqs_fuel lo hi) a2 qo n q0) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr b0segs m SLO (ovw sl Jlo 100) -> u32arr b0segs m SHI (ovw sh Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLM w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480) ->
    rw_cells b0segs m (P + 500) (nxt_cells nx) -> rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P ->
    id (rw_cells b0segs m (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m -> b0_incs m ->
    munch WQC me m -> wmono b0segs me m -> mviews X Y WQC me ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (b' : Z) (v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 : word) (nx' : nxt)
            (y5 y6 y7 y11 y12 y13 y15 y16 y17 y20 y22 y28 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' 0 sl' sh' sd' nl' nh' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLM w80 w88 w96 w104 (Z_to_bv 64 j) (Z_to_bv 64 nqs) (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 (hi - lo)) w224 w232
                                v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 w480) ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P ->
      id (rw_cells b0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQC me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 65535) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P) w232 y11 y12 y13 w224 y15 y16 y17
                            (Z_to_bv 64 (nqs + (hi - lo + 1))) (Z_to_bv 64 32) y20 (Z_to_bv 64 33) y22 (Z_to_bv 64 18446744073707454463) w96 w104 (Z_to_bv 64 j) cSB
                            y28 (Z_to_bv 64 NBD) (Z_to_bv 64 256) (Z_to_bv 64 2097152))
                       F (Z_to_bv 64 0xa3c30) fc None m' (seg_rom b0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (qsp' b' : Z) (v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 : word) (nx' : nxt),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' qsp' sl' sh' sd' nl' nh' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLM w80 w88 w96 w104 (Z_to_bv 64 j) (Z_to_bv 64 nqs) (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 (hi - lo)) w224 w232
                                v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 w480) ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P ->
      id (rw_cells b0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQC me m' -> wmono b0segs me m' ->
      bmfree_at X Y Q 0xa4444 m') ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 nqs) x19 (Z_to_bv 64 lo) x21 (Z_to_bv 64 hi) x23 x24 x25 (Z_to_bv 64 j) cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa21c0) fc None m (seg_rom b0segs)).
  Proof.
    intros j lo hi b nqs a1 a2 sl sh sd nl nh nd Jlo Jhi Jd
           w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480 nx
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 x31 me m.
    intros q0 Hlo Hlh Hhi Hb Hj Hnqs OKv FIN A1OK A2OK PR LJlo LJhi LJd AR1 AR2 SLOB SHIB SDB SLB NX BUD STK SHC MI IB MU WM MV Kset Kexit. subst q0.
    msenv_open XOK. amenv_open YOK. bz_params.
    pose proof (amsx_1_SLO X Y YSX) as AS1l. pose proof (amsx_1_SHI X Y YSX) as AS1h. pose proof (amsx_1_SD X Y YSX) as AS1d.
    pose proof (amsx_2_SLO X Y YSX) as AS2l. pose proof (amsx_2_SHI X Y YSX) as AS2h. pose proof (amsx_2_SD X Y YSX) as AS2d.
    amenv_shx_open X Y SHF YSHX. destruct YSF as (AX & SFL & SFH). unfold SH_LO, SH_HI in SFL, SFH.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    mviews_open MV.
    open_slb_in SLB. unfold b0_incs, B0_INCS in IB.
    pose proof (munch_refl WQA m) as MUp. pose proof (wmono_refl b0segs m) as WMp.
    (* [comment removed for export] *)
    brun_to 0xa21f0%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
    enter_with (B0_ms_scope_begin X SHF Q m1 m1 f8b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact SHC1| exact MI| apply munch_refl| apply wmono_refl|].
    intros m2 SHC2 MI2 MU2 WM2. clear SHC1 MI. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    pose proof (app_fp_WQA X Y SHF XOK YOK YOFF YSHX) as AFt.
    destruct (ams_stack_readers X Y SHF WQA m2 XOK YOK AX AFt SHC2) as (SHl2 & SHh2 & SHd2).
    change (rw_cells b0segs m2 (SHF + 4) (shc3 z8)) with (id (rw_cells b0segs m2 (SHF + 4) (shc3 z8))) in SHC2.
    pose proof (munch_refl WQA m2) as MUp. pose proof (wmono_refl b0segs m2) as WMp.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm SLO _ 0 _ SLOB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO1 end.
    wstep. ovw_store_at SLOB 0%Z lo (apply unsigned_lit_mod32). try clear SO1.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm SHI _ 0 _ SHIB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
    wstep. ovw_store_at SHIB 0%Z hi (apply unsigned_lit_mod32). try clear SO2.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm SD _ 0 _ SDB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
    wstep. ovw_store_at SDB 0%Z 2%Z (apply unsigned_lit_mod32). try clear SO3.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0xa24a4%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mq := mm) in * end.
    (* [comment removed for export] *)
    assert (TAIL : forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (qsp' b' : Z) (ex : bool)
                (v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 : word) (nx' : nxt),
      mqs_loop (mqs_fuel lo hi) a2 qo n (MQS a1 1 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd b false) = MQS a1' qsp' sl' sh' sd' nl' nh' nd' b' ex ->
      ((ex = false /\ qsp' = 0 /\ 0 <= b' <= b) \/ (ex = true /\ -2147483648 < b' < 0))%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLM w80 w88 w96 w104 (Z_to_bv 64 j) (Z_to_bv 64 nqs) (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 (hi - lo)) w224 w232
                                v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 w480) ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQA mq m' -> wmono b0segs mq m' ->
      bfree_at X Y Q 0xa3970 m').
    { intros m' a1' sl' sh' sd' nl' nh' nd' qsp' b' ex v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 nx'.
      intros EQ CASE OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM'.
      clear AR1 AR2 SLOB SHIB SDB SLB NX BUD STK MI2 IB.
      transport_after_call b0segs mq m' MU' WM'. clear MU' WM'.
      assert (Hb' : (-2147483648 < b' < 2147483648)%Z) by lia.
      unfold bfree_at. intros. open_slb_in SLB'. unfold b0_incs, B0_INCS in IB'.
      (* [comment removed for export] *)
      wstep. wstep.
      (* [comment removed for export] *)
      shc3_move SHC2 MUp WMp SHC3. clear SHC2 MUp WMp SHl2 SHh2 SHd2.
      enter_with (B0_ms_scope_end X SHF Q m' m' z8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact SHC3| exact MI'| apply munch_refl| apply wmono_refl|].
      intros m5 SHC5 MI5 MU5 WM5. clear SHC3 MI'. transport_after_call b0segs m' m5 MU5 WM5. clear MU5 WM5.
      change (rw_cells b0segs m5 (SHF + 4) (shc3 f8b)) with (id (rw_cells b0segs m5 (SHF + 4) (shc3 f8b))) in SHC5.
      (* [comment removed for export] *)
      brun_to 0xa3c2c%Z.
      (* [comment removed for export] *)
      wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia] | apply bvlts0_false in Kb; [|lia]].
      - destruct CASE as [(E1 & E2 & E3)|(E1 & E3)]; [exfalso; lia|]. subst ex.
        pose proof (Kexit m5 a1' sl' sh' sd' nl' nh' nd' qsp' b' v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 nx' EQ ltac:(lia) OK' PR') as KK.
        specialize (KK AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' SHC5 MI5 IB' MU WM).
        unfold bmfree_at in KK. enter_with KK. st_eq.
      - destruct CASE as [(E1 & E2 & E3)|(E1 & E3)]; [|exfalso; lia]. subst ex qsp'.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kset mm a1' sl' sh' sd' nl' nh' nd' b' v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 nx' _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'
          | exact SHC5| exact MI5| exact IB'| exact MU| exact WM]. }
    assert (BQ : bqat X Y Q 1 mq).
    { eapply (B0_qloop X Y SHF SHn Q XOK XSEP YOK YSX _ _ _ _ _ _ _ _ _ _ _ (mqs_fuel lo hi) 1 b a1 a2 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd Jlo Jhi Jd
                       _ _ _ _ _ _ _ _ _ _ _ _ _ nx mq mq);
        [lia| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| | exact LJlo| exact LJhi| exact LJd
        | exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SLB| repeat split; lia| exact NX| exact BUD| exact STK| exact MI2| exact IB
        | apply munch_refl| apply wmono_refl| | |].
      - intros i Hi. replace i with 0%Z by lia. rewrite !zdef_zset_same. CmpFast.tauto_g.
      - unfold qviews.
        split; [eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve]|].
        split; [eapply (shzW_sub b0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub b0segs); [exact SH2| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shpW_sub b0segs); [exact SHBU| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub b0segs); [exact SHIN| exact MU| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub b0segs); [exact SHl2| exact MUp| sub_fp_solve| lia| lia]|].
        split; [eapply (shzW_sub b0segs); [exact SHh2| exact MUp| sub_fp_solve| lia| lia]|].
        eapply (shzW_sub b0segs); [exact SHd2| exact MUp| sub_fp_solve| lia| lia].
      - (* [comment removed for export] *)
        intros m' a1' slo' shi' sd' nlo' nhi' nd' b' v240 v248 v264 v272 v328 v336 v344 v352 v392 v408 v416 v440 nx'.
        intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM'.
        eapply (TAIL m' a1' slo' shi' sd' nlo' nhi' nd' 0%Z b' false v240 v248 v264 v272 _ v328 v336 v344 v352 v392 v408 v416 v440 nx');
          [exact EQ| left; repeat split; lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'
          | exact MI'| exact IB'| exact MU'| exact WM'].
      - (* [comment removed for export] *)
        intros m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' v312 v240 v248 v264 v272 v328 v336 v344 v352 v392 v408 v416 v440 nx'.
        intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM'.
        eapply (TAIL m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' true v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 nx');
          [exact EQ| right; repeat split; lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'
          | exact MI'| exact IB'| exact MU'| exact WM']. }
    unfold bqat in BQ. enter_with BQ. st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

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
  Lemma B0_step1 : forall (cnt : nat) (j ss b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte)
      (w80 w88 : word) (sq : slq) (nx : nxt)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, j + Z.of_nat k < 256 -> let s' := ms_step1 k qo n ss j s in s_exit s' = false -> step1F qo n ss (j + Z.of_nat k) s')%Z ->
    (forall k, j + Z.of_nat k < 256 -> let s' := ms_step1 k qo n ss j s in s_exit s' = false -> step1N qo n ss (j + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m FT (zw32 ft 65537) ->
    u32arr b0segs m SLO (ovw sl Jlo 100) -> u32arr b0segs m SHI (ovw sh Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLS w80 w88 ss sq) ->
    rw_cells b0segs m (P + 500) (nxt_cells nx) -> rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P ->
    id (rw_cells b0segs m (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m -> b0_incs m ->
    munch WS1 me m -> wmono b0segs me m -> mviews X Y WS1 me ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (sq' : slq) (nx' : nxt)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y22 y28 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ft' 65537) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLS w80 w88 ss sq') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P ->
      id (rw_cells b0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m' -> b0_incs m' ->
      munch WS1 me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RM ss y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 nqs') y20 y22 (Z_to_bv 64 256) y28)
                       F (Z_to_bv 64 0xa3cd0) fc None m' (seg_rom b0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (sq' : slq) (nx' : nxt),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ft' 65537) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLS w80 w88 ss sq') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P ->
      id (rw_cells b0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m' -> b0_incs m' ->
      munch WS1 me m' -> wmono b0segs me m' ->
      bmfree_at X Y Q 0xa4444 m') ->
    evt b0segs Q (MS (RM ss x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 nqs) x20 x22 (Z_to_bv 64 j) x28)
                     F (Z_to_bv 64 0xa20fc) fc None m (seg_rom b0segs)).
  Proof.
    induction cnt as [|cnt IH].
    { intros. exfalso. lia. }
    intros j ss b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd Jlo Jhi Jd w80 w88 sq nx
           x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 me m.
    intros s Hcnt Hj Hss Hb S1F S1N A1OK A2OK PR LJlo LJhi LJd AR1 AR2 FTB SLOB SHIB SDB SLB NX BUD STK SHC MI IB MU WM MV Knext Kexit. subst s.
    destruct sq as [z80 z88 z96 z104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480].
    cbn [q160 q168 q176 q184 q224 q232 q240 q248 q264 q272 q312 q328 q336 q344 q352 q392 q408 q416 q440 q480] in SLB.
    msenv_open XOK. amenv_open YOK. bz_params. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_SLO X Y YSX) as AS1l. pose proof (amsx_1_SHI X Y YSX) as AS1h. pose proof (amsx_1_SD X Y YSX) as AS1d.
    pose proof (amsx_2_SLO X Y YSX) as AS2l. pose proof (amsx_2_SHI X Y YSX) as AS2h. pose proof (amsx_2_SD X Y YSX) as AS2d.
    pose proof (amsx_F_SLO X Y YSX) as ASFl. pose proof (amsx_F_SHI X Y YSX) as ASFh. pose proof (amsx_F_SD X Y YSX) as ASFd.
    amenv_shx_open X Y SHF YSHX. pose proof YSF as (AX & SFL & SFH). unfold SH_LO, SH_HI in SFL, SFH.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    mviews_open MV.
    set (sb := (Z.shiftl ss 8 + j)%Z). assert (Hsb : sb = (256 * ss + j)%Z) by (subst sb; rewrite shl8; reflexivity).
    (* [comment removed for export] *)
    assert (NEXTK : forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (sq' : slq) (nx' : nxt)
                (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y22 y28 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ft' 65537) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLS w80 w88 ss sq') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P ->
      id (rw_cells b0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m' -> b0_incs m' ->
      munch WS1 me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RM ss y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 nqs') y20 y22 (Z_to_bv 64 j) y28)
                       F (Z_to_bv 64 0xa3c44) fc None m' (seg_rom b0segs))).
    { intros m' a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' sq' nx' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y22 y28
             EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SLB' NX' BUD' STK' SHC' MI' IB' MU' WM'.
      clear AR1 AR2 FTB SLOB SHIB SDB SLB NX BUD STK SHC MI IB MU WM.
      rewrite (EQ cnt) in Knext, Kexit.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc; zify_cond_z Kc.
      - assert (cnt = 0%nat) as -> by lia. cbn [ms_step1] in Knext.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Knext mm a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' sq' nx' _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'
          | exact BUD'| exact STK'| exact SHC'| exact MI'| exact IB'| exact MU'| exact WM'].
      - wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss b' nqs' a1' a2 ft' bd cs ce sl' sh' sd' nl' nh' nd' Jlo Jhi Jd w80 w88 sq' nx'
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| | | exact OK'| exact A2OK| exact PR'| exact LJlo| exact LJhi| exact LJd| exact AR1'| exact AR2'| exact FTB'
          | exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'| exact SHC'| exact MI'| exact IB'| exact MU'| exact WM'| exact MV| | ].
        + intros k Hk. pose proof (S1F (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. cbv zeta in Fk. rewrite (EQ k) in Fk. cbv zeta. rewrite Nat2Z.inj_succ in Fk.
          replace (j + 1 + Z.of_nat k)%Z with (j + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
        + intros k Hk. pose proof (S1N (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. cbv zeta in Fk. rewrite (EQ k) in Fk. cbv zeta. rewrite Nat2Z.inj_succ in Fk.
          replace (j + 1 + Z.of_nat k)%Z with (j + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
        + intros * EQ2 Hb2. eapply Knext; [exact EQ2| lia].
        + exact Kexit. }
    clear IH.
    pose proof (S1F 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [ms_step1] in F0. rewrite Z.add_0_r in F0. unfold step1F in F0.
    cbn [s_ft s_mql s_a1 s_a2 s_budget ml_slo ml_shi ml_sd ml_nlo ml_nhi ml_nd] in F0. fold sb in F0.
    pose proof (S1N 0%nat ltac:(cbn; lia) eq_refl) as N0. cbn [ms_step1] in N0. unfold step1N in N0. cbn [s_nqs] in N0.
    open_slb_in SLB. unfold b0_incs, B0_INCS in IB.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    2:{ wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (NEXTK mm a1 ft sl sh sd nl nh nd b nqs
                        (mkSLQ z80 z88 z96 z104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480) nx
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| intros k; apply ms_step1_skip; lia| lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLOB| exact SHIB| exact SDB
          | exact SLB| exact NX| exact BUD| exact STK| exact SHC| exact MI| exact IB| exact MU| exact WM]. }
    cps_destruct (F0 ltac:(lia)) as (c0 & c1 & Hc01 & Hc1n & FC0 & FC1 & FQ). clear F0.
    assert (Hc0 : (0 <= c0 < 2097152)%Z) by lia. assert (Hc1 : (0 <= c1 < 2097152)%Z) by lia.
    pose proof (ftcell_cases _ _ Hc0 FC0) as X0. pose proof (ftcell_cases _ _ Hc1 FC1) as X1.
    pose proof (ftcell_clear _ _ Hc0 FC0) as CL0. pose proof (ftcell_clear _ _ Hc1 FC1) as CL1.
    (* [comment removed for export] *)
    brun_to 0xa2134%Z.
    replace (FT + (j + ss * 256) * 4)%Z with (FT + 4 * sb)%Z by lia.
    pose proof (saddr_intro (FT + 4 * sb)%Z) as ASB. set (SHsb := ((FT + 4 * sb) / 8 + 2147450880)%Z) in *. clearbody SHsb.
    (* [comment removed for export] *)
    assert (SETK : forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (sq' : slq) (nx' : nxt)
                (y5 y6 y7 y11 y12 y13 y15 y16 y17 y20 y22 y28 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 (zset ft sb (Z.lor (zget ft sb) SETMASK)) bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) ->
      (0 <= b' <= b)%Z -> zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr b0segs m' FT (zw32 ft 65537) ->
      u32arr b0segs m' SLO (ovw sl' Jlo 100) -> u32arr b0segs m' SHI (ovw sh' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLS w80 w88 ss sq') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P ->
      id (rw_cells b0segs m' (SHF + 4) (shc3 f8b)) -> mem_inv b0segs m' -> b0_incs m' ->
      munch WS1 me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RM ss y5 y6 y7 (Z_to_bv 64 (FT + 4 * sb)) y11 y12 y13 (Z_to_bv 64 SHsb) y15 y16 y17 (Z_to_bv 64 nqs') y20 y22 (Z_to_bv 64 j) y28)
                       F (Z_to_bv 64 0xa3c30) fc None m' (seg_rom b0segs))).
    { intros m' a1' sl' sh' sd' nl' nh' nd' b' nqs' sq' nx' y5 y6 y7 y11 y12 y13 y15 y16 y17 y20 y22 y28
             EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SLB' NX' BUD' STK' SHC' MI' IB' MU' WM'.
      clear AR1 AR2 FTB SLOB SHIB SDB SLB NX BUD STK SHC MI IB MU WM. unfold b0_incs, B0_INCS in IB'.
      pose proof (zb8_length a1' ARR1_SIZE ltac:(lia)) as L1'.
      pose proof (ovw_length sl' Jlo 100 ltac:(lia)) as Llo'. pose proof (ovw_length sh' Jhi 100 ltac:(lia)) as Lhi'. pose proof (ovw_length sd' Jd 100 ltac:(lia)) as Ld'.
      pose proof (munch_refl [(FT, FT + 262148)]%Z m') as MUp. pose proof (wmono_refl b0segs m') as WMp.
      (* [comment removed for export] *)
      brun. rd32_at FTB' sb.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok b0segs mm FT _ sb _ FTB' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store_at FTB' sb (Z.lor (zget ft sb) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
      shc3_move SHC' MUp WMp SHC2. clear SHC' MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (NEXTK mm a1' (zset ft sb (Z.lor (zget ft sb) SETMASK)) sl' sh' sd' nl' nh' nd' b' nqs' sq' nx' _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'
        | exact SLB'| exact NX'| exact BUD'| exact STK'| exact SHC2| exact MI'| exact IB'| exact MU'| exact WM']. }
    clear NEXTK.
    pose proof (munch_refl WQA m) as MUp. pose proof (wmono_refl b0segs m) as WMp.
    assert (FR0 : (0 <= zget ft sb < 4194304)%Z) by (destruct X0 as [E0|E0]; rewrite E0; lia).
    (* [comment removed for export] *)
    brun. rd32_at FTB sb.
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Km; [apply negb_true_iff in Km; apply slt42_false in Km; [|lia] | apply negb_false_iff in Km; apply slt42_true in Km; [|lia]].
    2:{ (* [comment removed for export] *)
      wstep. shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd b nqs
                      (mkSLQ z80 z88 z96 z104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480) nx
                      _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLOB| exact SHIB| exact SDB| exact SLB| exact NX| exact BUD| exact STK
        | exact SHC1| exact MI| exact IB| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. left. fold sb.
      destruct X0 as [E0|E0]; [exfalso; lia|]. rewrite E0, <- lor_setmask by lia. apply has_setmask_marked. lia. }
    destruct X0 as [E0|E0]; [|exfalso; lia].
    assert (FR1 : (0 <= zget ft (sb + 1) < 4194304)%Z) by (destruct X1 as [E1|E1]; rewrite E1; lia).
    (* [comment removed for export] *)
    brun_to 0xa21a0%Z.
    replace ((j + ss * 256 + 1) * 4 + FT)%Z with (FT + 4 * sb + 4)%Z by lia.
    ack_rd (FT + 4 * sb + 4)%Z 4%Z. ack_merge.
    (* [comment removed for export] *)
    rd32_at FTB (sb + 1)%Z.
    (* [comment removed for export] *)
    wstep. rewrite land_CM64, CL1 by lia.
    wstep. rewrite E0.
    wstep; if_cases Kge; zify_cond_z Kge.
    2:{ (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd b nqs
                      (mkSLQ z80 z88 z96 z104 w160 w168 w176 w184 (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb)) w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480) nx
                      _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLOB| exact SHIB| exact SDB| exact SLB| exact NX| exact BUD| exact STK
        | exact SHC1| exact MI| exact IB| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. right. fold sb. rewrite CL0, CL1. lia. }
    destruct (FQ E0 ltac:(lia)) as [OKv FIN].
    shc3_move SHC MUp WMp SHC1. clear SHC MUp WMp.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mc := mm) in * end.
    enter_with (B0_qcall j c0 (c1 - 1)%Z b nqs a1 a2 sl sh sd nl nh nd Jlo Jhi Jd
                  w80 w88 (Z_to_bv 64 ss) (Z_to_bv 64 (ss * 256)) w160 w168 w176 w184 (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb))
                  w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w440 w480 nx
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc mc);
      [st_eq| lia| lia| lia| lia| lia| exact N0| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SLB| exact NX| exact BUD| exact STK| exact SHC1| exact MI| exact IB
      | apply munch_refl| apply wmono_refl| eapply mviews_sub; [exact MV| exact MU| sub_fp_solve]| |].
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' b' v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 nx' y5 y6 y7 y11 y12 y13 y15 y16 y17 y20 y22 y28.
      intros EQl Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' SHC' MI' IB' MU' WM'.
      clear AR1 AR2 SLOB SHIB SDB SLB NX BUD STK SHC1 MI IB. transport_after_call b0segs mc m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1' sl' sh' sd' nl' nh' nd' b' (nqs + (c1 - 1 - c0 + 1))%Z
                      (mkSLQ z80 z88 z96 z104 (Z_to_bv 64 j) (Z_to_bv 64 nqs) (Z_to_bv 64 (c1 - 1 - c0)) (Z_to_bv 64 (c1 - 1 - c0)) (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb))
                             v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 w480) nx'
                      _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'
        | exact SHC'| exact MI'| exact IB'| exact MU| exact WM].
      intros k. pose proof (ms_step1_q k qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' 0 sl' sh' sd' nl' nh' nd' b' false ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with false in SQ by (symmetry; apply Z.ltb_ge; lia). exact SQ.
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' qsp' b' v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 nx'.
      intros EQl Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' SHC' MI' IB' MU' WM'.
      clear AR1 AR2 SLOB SHIB SDB SLB NX BUD STK SHC1 MI IB. transport_after_call b0segs mc m' MU' WM'. clear MU' WM'.
      eapply (Kexit m' a1' ft sl' sh' sd' nl' nh' nd' b' (nqs + (c1 - 1 - c0 + 1))%Z
                (mkSLQ z80 z88 z96 z104 (Z_to_bv 64 j) (Z_to_bv 64 nqs) (Z_to_bv 64 (c1 - 1 - c0)) (Z_to_bv 64 (c1 - 1 - c0)) (Z_to_bv 64 SHsb) (Z_to_bv 64 (FT + 4 * sb))
                       v240 v248 v264 v272 v312 v328 v336 v344 v352 v392 v408 v416 v440 w480) nx');
        [| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'
         | exact SHC'| exact MI'| exact IB'| exact MU| exact WM].
      pose proof (ms_step1_q cnt qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' qsp' sl' sh' sd' nl' nh' nd' b' true ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with true in SQ by (symmetry; apply Z.ltb_lt; lia). exact SQ.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
