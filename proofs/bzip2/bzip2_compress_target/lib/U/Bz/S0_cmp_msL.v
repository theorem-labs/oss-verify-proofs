(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs2 BzCLemmasMs3 CmpMsKit2 S0_cmp_msV S0_cmp_msK.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit BzIncs.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.

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

  Definition WS1 : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 8, p + 340); (p + 3668, p + 4904)]%Z.

  (* [comment removed for export] *)
  Lemma S0_qcall : forall (j sb lo hi b nqs : Z) (a1 a2 ft sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte) (nx : list word)
      (w40 w48 w64 w72 w96 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 : word)
      (x0 x4 x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let q0 := MQS a1 1 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd b false in
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= b < 2147483648)%Z -> (0 <= sb <= 65535)%Z -> zget ft sb = lo -> (0 <= j < 256)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q0 in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop (mqs_fuel lo hi) a2 qo n q0) <= 0 \/ mq_exit (mqs_loop (mqs_fuel lo hi) a2 qo n q0) = true)%Z ->
    (0 <= nqs)%Z -> (nqs + n <= 2147483647)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u32arr s0segs m (p + 4504) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4104) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    Z.of_nat (length nx) = 9%Z -> u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 w96 (Z_to_bv 64 nqs) (Z_to_bv 64 (hi - lo)))) ->
    rw_cells s0segs m (p + 120) (scb_cells X (mkSCB (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 j) w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)) ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> rw_cells s0segs m 210296 [CB 56 incs_bytes] ->
    mem_inv s0segs m -> munch WS1 me m -> wmono s0segs me m ->
    apart A1 ARR1_SIZE 210296 56 ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' : Z) (v144 v152 v168 v176 v184 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y8 y9 y10 y13 y14 y15 y16 y26 y27 y28 y29 y30 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' 0 sl' sh' sd' nl' nh' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 nqs) (Z_to_bv 64 (hi - lo)))) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 j) v144 v152 v168 v176 v184 (Z_to_bv 64 0) v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 lo) y8 y9 y10 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 j) y13 y14 y15 y16
                            (Z_to_bv 64 A1) w64 (Z_to_bv 64 A2) w72 (Z_to_bv 64 (nqs + (hi - lo + 1))) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32) y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x21c7c) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (qsp' b' : Z) (v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' qsp' sl' sh' sd' nl' nh' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 nqs) (Z_to_bv 64 (hi - lo)))) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 j) v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 b') y8 y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22114) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 lo) (Z_to_bv 64 hi) x9 x10 x11 x12 x13 x14 x15 x16
                            (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 (Z_to_bv 64 (hi - lo)) x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20ee0) fc None m (seg_rom s0segs)).
  Proof.
    intros j sb lo hi b nqs a1 a2 ft sl sh sd nl nh nd Jlo Jhi Jd nx w40 w48 w64 w72 w96 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288
           x0 x4 x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 me m.
    intros q0 Hlo Hlh Hhi Hb Hsb Esb Hj OKv FIN Hnq Hnqn A1OK A2OK PR LJlo LJhi LJd AR1 AR2 FTB SLO SHI SD LNX NX SCA SCB BUD INC MI MU WM APT Kset Kexit.
    subst q0.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WS1 in *. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    open_sc_in SCA. open_sc_in SCB.
    (* [comment removed for export] *)
    urun_to 0x20eec%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4504) _ 0 _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO1 end.
    wstep. ovw_store_at SLO 0%Z lo (apply unsigned_lit_mod32).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4104) _ 0 _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
    wstep. ovw_store_at SHI 0%Z hi (apply unsigned_lit_mod32).
    urun_to 0x20ef8%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3704) _ 0 _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
    wstep. ovw_store_at SD 0%Z 2%Z (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    urun_to 0x20f00%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_qloop X Q XOK XSEP (mqs_fuel lo hi) 1 b a1 a2 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd Jlo Jhi Jd nx
                    (mkSCB (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 j) w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| | exact LJlo| exact LJhi| exact LJd| exact LNX
      | exact AR1| exact AR2| exact SLO| exact SHI| exact SD| exact NX| | exact BUD| exact MI| exact INC| exact APT| | apply wmono_refl| |].
    { intros i Hi. replace i with 0%Z by lia. rewrite !zdef_zset_same. CmpFast.tauto_g. }
    { match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end. }
    { apply munch_refl. }
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' b' nx' v144 v152 v168 v176 v184 v232 v240 v248 v256 v288
             y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' LNX' NX' SCB' BUD' MI' INC' MU' WM'. cbn [k128 k136] in SCB'.
      clear AR1 AR2 SLO SHI SD NX BUD MI SCB INC.
      unfold WQ in *. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      open_sc_in SCB'.
      (* [comment removed for export] *)
      urun_to 0x21c60%Z.
      ustep. if_cases Kb; zify_cond_z Kb; [exfalso; lia|].
      urun_to 0x21c68%Z.
      rd32_at FTB sb. rewrite Esb.
      urun_to 0x21c7c%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kset mm a1' sl' sh' sd' nl' nh' nd' nx' b' v144 v152 v168 v176 v184 v232 v240 v248 v256 v288 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'
        | | | exact BUD'| exact INC'| exact MI'| exact MU| exact WM].
      { match goal with H : rw_cells _ _ (p + 8)%Z _ |- _ => exact H end. }
      { match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end. }
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' qsp' b' nx' v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
             y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' LNX' NX' SCB' BUD' MI' INC' MU' WM'. cbn [k128 k136] in SCB'.
      clear AR1 AR2 SLO SHI SD NX BUD MI SCB INC.
      unfold WQ in *. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      open_sc_in SCB'.
      urun_to 0x21c60%Z.
      rewrite ?sx32_of_Z_signed by lia. ustep. if_cases Kb; zify_cond_z Kb; [|exfalso; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kexit mm a1' sl' sh' sd' nl' nh' nd' nx' qsp' b' v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'
        | | | exact BUD'| exact INC'| exact MI'| exact MU| exact WM].
      { match goal with H : rw_cells _ _ (p + 8)%Z _ |- _ => exact H end. }
      { match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end. }
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_step1 : forall (cnt : nat) (j ss b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte) (nx : list word)
      (w40 w48 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 : word)
      (x0 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, j + Z.of_nat k < 256 -> let s' := ms_step1 k qo n ss j s in s_exit s' = false -> step1F qo n ss (j + Z.of_nat k) s')%Z ->
    (forall k, j + Z.of_nat k < 256 -> let s' := ms_step1 k qo n ss j s in s_exit s' = false -> 0 <= s_nqs s' /\ s_nqs s' + n <= 2147483647)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u32arr s0segs m (p + 4504) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4104) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    Z.of_nat (length nx) = 9%Z -> u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 8) (sca_cells X (mkSCA w40 w48 (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) w96 w104 w112)) ->
    rw_cells s0segs m (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)) ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> rw_cells s0segs m 210296 [CB 56 incs_bytes] ->
    mem_inv s0segs m -> munch WS1 me m -> wmono s0segs me m ->
    apart FT 262148 210296 56 -> apart A1 ARR1_SIZE 210296 56 ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y26 y27 y28 y29 y30 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA w40 w48 (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8 y9 y10 y11 (Z_to_bv 64 256) y13 y14 y15 y16
                            (Z_to_bv 64 A1) (Z_to_bv 64 ss) (Z_to_bv 64 A2) (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32) y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x21c8c) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 b') y8 y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22114) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 j) x13 x14 x15 x16
                            (Z_to_bv 64 A1) (Z_to_bv 64 ss) (Z_to_bv 64 A2) (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 nqs) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32) x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20e2c) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH].
    { intros. exfalso. lia. }
    intros j ss b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd Jlo Jhi Jd nx w40 w48 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 x0 x4 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x26 x27 x28 x29 x30 me m.
    intros s Hcnt Hj Hss Hb S1F S1N A1OK A2OK PR LJlo LJhi LJd AR1 AR2 FTB SLO SHI SD LNX NX SCA SCB BUD INC MI MU WM APF APA Knext Kexit. subst s.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WS1 in *. pose proof APF as APFu. unfold apart in APFu. pose proof APA as APAu. unfold apart in APAu.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    set (sb := (Z.shiftl ss 8 + j)%Z). assert (Hsb : sb = (256 * ss + j)%Z) by (subst sb; rewrite shl8; reflexivity).
    (* [comment removed for export] *)
    assert (NEXTK : forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z) (v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word) (y0 y4 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y26 y27 y28 y29 y30 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA w40 w48 (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8 y9 y10 y11 (Z_to_bv 64 j) y13 y14 y15 y16
                            (Z_to_bv 64 A1) (Z_to_bv 64 ss) (Z_to_bv 64 A2) (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32) y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x21c84) fc None m' (seg_rom s0segs))).
    { intros m' a1' ft' sl' sh' sd' nl' nh' nd' nx' b' nqs' v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 y0 y4 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y26 y27 y28 y29 y30
             EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' LNX' NX' SCA' SCB' BUD' INC' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD NX SCA SCB BUD INC MI MU WM. unfold WS1 in MU'.
      rewrite (EQ cnt) in Knext, Kexit.
      (* [comment removed for export] *)
      urun. if_cases Kc; zify_cond_z Kc.
      - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss b' nqs' a1' a2 ft' bd cs ce sl' sh' sd' nl' nh' nd' Jlo Jhi Jd nx' w40 w48 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| | | exact OK'| exact A2OK| exact PR'| exact LJlo| exact LJhi| exact LJd| exact AR1'| exact AR2'| exact FTB'
          | exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'| exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU'| exact WM'
          | exact APF| exact APA| | ].
        + intros k Hk. pose proof (S1F (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. cbv zeta in Fk. rewrite (EQ k) in Fk. cbv zeta. rewrite Nat2Z.inj_succ in Fk.
          replace (j + 1 + Z.of_nat k)%Z with (j + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
        + intros k Hk. pose proof (S1N (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. cbv zeta in Fk. rewrite (EQ k) in Fk. cbv zeta. exact Fk.
        + intros until 0. intros EQ2 Hb2. eapply Knext; [exact EQ2| lia].
        + exact Kexit.
      - (* [comment removed for export] *)
        assert (cnt = 0%nat) as -> by lia. cbn [ms_step1] in Knext.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Knext mm a1' ft' sl' sh' sd' nl' nh' nd' nx' b' nqs' v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'
          | exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU'| exact WM']. }
    pose proof (S1F 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [ms_step1] in F0. rewrite Z.add_0_r in F0. unfold step1F in F0.
    cbn [s_ft s_mql s_a1 s_a2 s_budget ml_slo ml_shi ml_sd ml_nlo ml_nhi ml_nd] in F0. fold sb in F0.
    pose proof (S1N 0%nat ltac:(cbn; lia) eq_refl) as N0. cbn [ms_step1 s_nqs] in N0.
    (* [comment removed for export] *)
    urun. if_cases Kc; zify_cond_z Kc.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (NEXTK mm a1 ft sl sh sd nl nh nd nx b nqs w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| intros k; apply ms_step1_skip; lia| lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD
        | exact LNX| exact NX| exact SCA| exact SCB| exact BUD| exact INC| exact MI| exact MU| exact WM]. }
    cps_destruct (F0 ltac:(lia)) as (c0 & c1 & Hc01 & Hc1n & FC0 & FC1 & FQ). clear F0.
    assert (Hc0 : (0 <= c0 < 2097152)%Z) by lia. assert (Hc1 : (0 <= c1 < 2097152)%Z) by lia.
    pose proof (ftcell_cases _ _ Hc0 FC0) as X0. pose proof (ftcell_cases _ _ Hc1 FC1) as X1.
    pose proof (ftcell_clear _ _ Hc0 FC0) as CL0. pose proof (ftcell_clear _ _ Hc1 FC1) as CL1.
    (* [comment removed for export] *)
    assert (SETK : forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z) (v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word) (y0 y4 y5 y6 y8 y9 y10 y13 y14 y15 y16 y26 y27 y28 y29 y30 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 (zset ft sb (Z.lor (zget ft sb) SETMASK)) bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) ->
      (0 <= b' <= b)%Z -> zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA w40 w48 (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 (zget ft sb)) y8 y9 y10 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 j) y13 y14 y15 y16
                            (Z_to_bv 64 A1) (Z_to_bv 64 ss) (Z_to_bv 64 A2) (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32) y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x21c7c) fc None m' (seg_rom s0segs))).
    { intros m' a1' sl' sh' sd' nl' nh' nd' nx' b' nqs' v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 y0 y4 y5 y6 y8 y9 y10 y13 y14 y15 y16 y26 y27 y28 y29 y30
             EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' LNX' NX' SCA' SCB' BUD' INC' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD NX SCA SCB BUD INC MI MU WM. unfold WS1 in MU'. open_sc_in SCA'. open_sc_in SCB'.
      (* [comment removed for export] *)
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm FT _ sb _ FTB' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store FTB' sb (Z.lor (zget ft sb) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (NEXTK mm a1' (zset ft sb (Z.lor (zget ft sb) SETMASK)) sl' sh' sd' nl' nh' nd' nx' b' nqs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'
        | exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU'| exact WM']. }
    open_sc_in SCA. open_sc_in SCB.
    (* [comment removed for export] *)
    urun.
    replace (j + 256 * ss)%Z with sb by lia.
    rd32_at FTB sb.
    urun.
    if_cases Km; [apply slt42_true in Km; [|lia] | apply slt42_false in Km; [|lia]].
    { (* [comment removed for export] *)
      destruct X0 as [E0|E0]; [exfalso; lia|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd nx b nqs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD| exact LNX| exact NX
        | exact SCA| exact SCB| exact BUD| exact INC| exact MI| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. left. fold sb.
      rewrite E0, <- lor_setmask by lia. apply has_setmask_marked. lia. }
    destruct X0 as [E0|E0]; [|exfalso; lia].
    (* [comment removed for export] *)
    urun.
    rd32_at FTB (sb + 1)%Z.
    urun.
    rewrite land_CM64, CL1 by lia. rewrite (swrap32_small (c1 + -1)) by lia. rewrite E0.
    replace (FT + sb * 4)%Z with (FT + 4 * sb)%Z in SCB by lia.
    if_cases Kv; zify_cond_z Kv.
    { (* [comment removed for export] *)
      urun_to 0x21c7c%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd nx b nqs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD| exact LNX| exact NX
        | exact SCA| exact SCB| exact BUD| exact INC| exact MI| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. right. fold sb. rewrite CL0, CL1. lia. }
    (* [comment removed for export] *)
    urun_to 0x20ee0%Z.
    destruct (FQ E0 ltac:(lia)) as [OKv FIN].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (S0_qcall j sb c0 (c1 - 1)%Z b nqs a1 a2 ft sl sh sd nl nh nd Jlo Jhi Jd nx w40 w48 (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) w96
                  w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| lia| lia| exact E0| lia| exact OKv| exact FIN| lia| lia| exact A1OK| exact A2OK| exact PR| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD| exact LNX| exact NX| exact SCA| exact SCB| exact BUD| exact INC| exact MI
      | apply munch_refl| apply wmono_refl| exact APA| |].
    - (* [comment removed for export] *)
      intros *. intros EQl Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' LNX' NX' SCA' SCB' BUD' INC' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD NX SCA SCB BUD INC MI. unfold WS1 in MU'. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1' sl' sh' sd' nl' nh' nd' nx' b' (nqs + (c1 - 1 - c0 + 1))%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'
        | exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU| exact WM].
      intros k. pose proof (ms_step1_q k qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' 0 sl' sh' sd' nl' nh' nd' b' false ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with false in SQ by (symmetry; apply Z.ltb_ge; lia). exact SQ.
    - (* [comment removed for export] *)
      intros *. intros EQl Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' LNX' NX' SCA' SCB' BUD' INC' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD NX SCA SCB BUD INC MI. unfold WS1 in MU'. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kexit mm a1' ft sl' sh' sd' nl' nh' nd' nx' b' (nqs + (c1 - 1 - c0 + 1))%Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'
        | exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU| exact WM].
      pose proof (ms_step1_q cnt qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' qsp' sl' sh' sd' nl' nh' nd' b' true ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with true in SQ by (symmetry; apply Z.ltb_lt; lia). exact SQ.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End S0MS.

End ACeilS1.
