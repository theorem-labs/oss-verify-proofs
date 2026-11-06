(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewC.BzCSewB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs2 BzCLemmasMs3 CmpMsKit2 S0_cmp_msV S0_cmp_msK.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
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

  Definition WS1 : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 16, p + 296); (p + 3624, p + 4824)]%Z.

  (* [comment removed for export] *)
  Lemma S0_qcall : forall (j sb lo hi b : Z) (a1 a2 ft sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte)
      (w48 w56 w64 w88 w96 w104 w152 w168 w176 w184 w192 w216 w224 w232 w240 w248 w256 w264 w288 : word)
      (x0 x4 x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x20 x24 x25 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let q0 := MQS a1 1 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd b false in
    (0 <= lo)%Z -> (lo < hi)%Z -> (hi < n)%Z -> (0 <= b < 2147483648)%Z -> (0 <= sb <= 65535)%Z -> zget ft sb = lo -> (- 2147483648 <= j < 2147483648)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q0 in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop (mqs_fuel lo hi) a2 qo n q0) <= 0 \/ mq_exit (mqs_loop (mqs_fuel lo hi) a2 qo n q0) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u32arr s0segs m (p + 4424) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4024) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3624) (ovw sd Jd 100) ->
    rw_cells s0segs m (p + 16) (sca_cells X (mkSCA w48 w56 w64 w88 w96 w104)) ->
    rw_cells s0segs m (p + 144) (scb_cells X (mkSCB (Z_to_bv 64 hi) w152 w168 w176 w184 w192 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 lo) w216 w224
                                     w232 w240 w248 w256 w264 (Z_to_bv 64 b) w288)) ->
    rw_cells s0segs m (p + 292) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch WS1 me m -> wmono s0segs me m ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (b' : Z) (v152 v168 v176 v184 v192 v232 v240 v248 v256 v264 v288 : word)
            (y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' 0 sl' sh' sd' nl' nh' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u32arr s0segs m' (p + 4424) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4024) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3624) (ovw sd' Jd 100) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA (Z_to_bv 64 j) w56 x24 w88 w96 w104)) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB (Z_to_bv 64 hi) v152 v168 v176 v184 v192 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 lo) w216 (Z_to_bv 64 0)
                                        v232 v240 v248 v256 v264 (Z_to_bv 64 b') v288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 j) (Z_to_bv 64 FT)
                            y9 (Z_to_bv 64 2097152) (Z_to_bv 64 18446744073707454463) w104 y13 y14 y15 y16
                            (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                            y24 w56 (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a278) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (qsp' b' : Z) (v152 v168 v176 v184 v192 v224 v232 v240 v248 v256 v264 v272 v288 : word)
            (y0 y4 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y24 y25 y27 y28 y29 y30 : word),
      mqs_loop (mqs_fuel lo hi) a2 qo n q0 = MQS a1' qsp' sl' sh' sd' nl' nh' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u32arr s0segs m' (p + 4424) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4024) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3624) (ovw sd' Jd 100) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA (Z_to_bv 64 j) w56 x24 w88 w96 w104)) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB (Z_to_bv 64 hi) v152 v168 v176 v184 v192 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 lo) w216 v224
                                        v232 v240 v248 v256 v264 v272 v288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 (Z_to_bv 64 FT)
                            y9 y10 y11 y12 y13 y14 y15 y16
                            y17 y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 n) y22 (Z_to_bv 64 b') y24 y25 (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a554) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 j) (Z_to_bv 64 FT)
                          x9 x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 lo) (Z_to_bv 64 98) (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                          x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x19b80) fc None m (seg_rom s0segs)).
  Proof.
    intros j sb lo hi b a1 a2 ft sl sh sd nl nh nd Jlo Jhi Jd w48 w56 w64 w88 w96 w104 w152 w168 w176 w184 w192 w216 w224 w232 w240 w248 w256 w264 w288
           x0 x4 x5 x6 x9 x10 x11 x12 x13 x14 x15 x16 x20 x24 x25 x27 x28 x29 x30 me m.
    intros q0 Hlo Hlh Hhi Hb Hsb Esb Hj OKv FIN A1OK A2OK PR LJlo LJhi LJd AR1 AR2 FTB SLO SHI SD SCA SCB BUD MI MU WM Kset Kexit. subst q0.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WS1 in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    open_sc_in SCA. open_sc_in SCB.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4424) _ 0 _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO1 end.
    wstep. ovw_store_at SLO 0%Z lo (apply unsigned_lit_mod32).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4024) _ 0 _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
    wstep. ovw_store_at SHI 0%Z hi (apply unsigned_lit_mod32).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 3624) _ 0 _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
    wstep. ovw_store_at SD 0%Z 2%Z (apply unsigned_lit_mod32).
    wstep.
    (* [comment removed for export] *)
    wstep. wstep. lit_store. do 13 wstep.
    wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_qloop X Q XOK XSEP (mqs_fuel lo hi) 1 b a1 a2 (zset sl 0 lo) (zset sh 0 hi) (zset sd 0 2) nl nh nd Jlo Jhi Jd
                    (mkSCB (Z_to_bv 64 hi) w152 w168 w176 w184 w192 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 lo) w216 (Z_to_bv 64 0)
                           w232 w240 w248 w256 w264 (Z_to_bv 64 b) w288)
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| | reflexivity| reflexivity| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact SLO| exact SHI| exact SD| | exact BUD| exact MI| apply munch_refl| apply wmono_refl| |].
    { intros i Hi. replace i with 0%Z by lia. rewrite !zdef_zset_same. CmpFast.tauto_g. }
    { match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end. }
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' b' v152 v168 v176 v184 v192 v232 v240 v248 v256 v264 v272 v288
             y0 y4 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y22 y24 y25 y27 y28 y29 y30.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCB' BUD' MI' MU' WM'. cbn [k144 k200 k208 k216] in SCB'.
      clear AR1 AR2 SLO SHI SD BUD MI SCB.
      unfold WQ in *. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      open_sc_in SCB'.
      (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Kb; [apply bvlts0_true in Kb; [|lia]; exfalso; lia | clear Kb].
      wstep. wstep. wstep.
      rd32_at FTB sb. rewrite Esb.
      do 13 wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (Kset mm a1' slo' shi' sd' nlo' nhi' nd' b' v152 v168 v176 v184 v192 v232 v240 v248 v256 v264 v288 _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact SCA| | exact BUD'| exact MI'| exact MU| exact WM].
      match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' v224 v152 v168 v176 v184 v192 v232 v240 v248 v256 v264 v272 v288
             y0 y4 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y24 y25 y27 y28 y29 y30.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCB' BUD' MI' MU' WM'. cbn [k144 k200 k208 k216 k224] in SCB'.
      clear AR1 AR2 SLO SHI SD BUD MI SCB.
      unfold WQ in *. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      eapply (Kexit m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' v152 v168 v176 v184 v192 v224 v232 v240 v248 v256 v264 v272 v288);
        [exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB| exact SLO'| exact SHI'| exact SD'| exact SCA| exact SCB'| exact BUD'| exact MI'| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_step1 : forall (cnt : nat) (j ss b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd : zarr) (Jlo Jhi Jd : list byte)
      (si w48 w56 w64 w88 w96 w144 w152 w168 w176 w184 w192 w200 w208 w224 w232 w240 w248 w256 w264 w288 : word)
      (x0 x4 x5 x6 x9 x13 x14 x15 x16 x24 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, j + Z.of_nat k < 256 -> let s' := ms_step1 k qo n ss j s in s_exit s' = false -> step1F qo n ss (j + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u32arr s0segs m (p + 4424) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4024) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3624) (ovw sd Jd 100) ->
    rw_cells s0segs m (p + 16) (sca_cells X (mkSCA w48 w56 w64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss)))) ->
    rw_cells s0segs m (p + 144) (scb_cells X (mkSCB w144 w152 w168 w176 w184 w192 w200 w208 (Z_to_bv 64 ss) w224
                                     w232 w240 w248 w256 w264 (Z_to_bv 64 b) w288)) ->
    rw_cells s0segs m (p + 292) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch WS1 me m -> wmono s0segs me m ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (v48 v56 v64 v144 v152 v168 v176 v184 v192 v200 v208 v224 v232 v240 v248 v256 v264 v288 : word)
            (y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u32arr s0segs m' (p + 4424) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4024) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3624) (ovw sd' Jd 100) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA v48 v56 v64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss)))) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB v144 v152 v168 v176 v184 v192 v200 v208 (Z_to_bv 64 ss) v224
                                        v232 v240 v248 v256 v264 (Z_to_bv 64 b') v288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 256) (Z_to_bv 64 FT)
                            y9 (Z_to_bv 64 2097152) (Z_to_bv 64 18446744073707454463) (Z_to_bv 64 (FT + 1024 * ss)) y13 y14 y15 y16
                            (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                            y24 si (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a2b8) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z)
            (v48 v56 v64 v144 v152 v168 v176 v184 v192 v200 v208 v224 v232 v240 v248 v256 v264 v272 v288 : word)
            (y0 y4 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y24 y25 y27 y28 y29 y30 : word),
      ms_step1 cnt qo n ss j s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u32arr s0segs m' (p + 4424) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4024) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3624) (ovw sd' Jd 100) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA v48 v56 v64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss)))) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB v144 v152 v168 v176 v184 v192 v200 v208 (Z_to_bv 64 ss) v224
                                        v232 v240 v248 v256 v264 v272 v288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> munch WS1 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 (Z_to_bv 64 FT)
                            y9 y10 y11 y12 y13 y14 y15 y16
                            y17 y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 n) y22 (Z_to_bv 64 b') y24 y25 (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a554) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 j) (Z_to_bv 64 FT)
                          x9 (Z_to_bv 64 2097152) (Z_to_bv 64 18446744073707454463) (Z_to_bv 64 (FT + 1024 * ss)) x13 x14 x15 x16
                          (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                          x24 si (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x19b38) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH].
    { intros. exfalso. lia. }
    intros j ss b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd Jlo Jhi Jd si w48 w56 w64 w88 w96 w144 w152 w168 w176 w184 w192 w200 w208 w224 w232 w240 w248 w256 w264 w288
           x0 x4 x5 x6 x9 x13 x14 x15 x16 x24 x27 x28 x29 x30 me m.
    intros s Hcnt Hj Hss Hb S1F A1OK A2OK PR LJlo LJhi LJd AR1 AR2 FTB SLO SHI SD SCA SCB BUD MI MU WM Knext Kexit. subst s.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WS1 in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length sl Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length sh Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    set (sb := (Z.shiftl ss 8 + j)%Z). assert (Hsb : sb = (256 * ss + j)%Z) by (subst sb; rewrite shl8; reflexivity).
    (* [comment removed for export] *)
    assert (NEXTK : forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (v48 v56 v64 v144 v152 v168 v176 v184 v192 v200 v208 v224 v232 v240 v248 v256 v264 v288 : word)
                (y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u32arr s0segs m' (p + 4424) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4024) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3624) (ovw sd' Jd 100) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA v48 v56 v64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss)))) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB v144 v152 v168 v176 v184 v192 v200 v208 (Z_to_bv 64 ss) v224
                                        v232 v240 v248 v256 v264 (Z_to_bv 64 b') v288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 16, p + 296); (p + 3624, p + 4824)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 j) (Z_to_bv 64 FT)
                            y9 (Z_to_bv 64 2097152) (Z_to_bv 64 18446744073707454463) (Z_to_bv 64 (FT + 1024 * ss)) y13 y14 y15 y16
                            (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                            y24 si (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a288) fc None m' (seg_rom s0segs))).
    { intros m' a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' v48 v56 v64 v144 v152 v168 v176 v184 v192 v200 v208 v224 v232 v240 v248 v256 v264 v288
             y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30 EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCA' SCB' BUD' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD SCA SCB BUD MI MU WM.
      rewrite (EQ cnt) in Knext, Kexit.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc; zify_cond_z Kc.
      - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss b' nqs' a1' a2 ft' bd cs ce sl' sh' sd' nl' nh' nd' Jlo Jhi Jd si v48 v56 v64 w88 w96 v144 v152 v168 v176 v184 v192 v200 v208 v224 v232 v240 v248 v256 v264 v288
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| lia| lia| | exact OK'| exact A2OK| exact PR'| exact LJlo| exact LJhi| exact LJd| exact AR1'| exact AR2'| exact FTB'
          | exact SLO'| exact SHI'| exact SD'| exact SCA'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| | ].
        + intros k Hk. pose proof (S1F (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. cbv zeta in Fk. rewrite (EQ k) in Fk. cbv zeta. rewrite Nat2Z.inj_succ in Fk.
          replace (j + 1 + Z.of_nat k)%Z with (j + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
        + intros until 0. intros EQ2 Hb2. eapply Knext; [exact EQ2| lia].
        + exact Kexit.
      - (* [comment removed for export] *) wstep.
        assert (cnt = 0%nat) as -> by lia. cbn [ms_step1] in Knext.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Knext mm a1' ft' sl' sh' sd' nl' nh' nd' b' nqs' v48 v56 v64 v144 v152 v168 v176 v184 v192 v200 v208 v224 v232 v240 v248 v256 v264 v288
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact SCA'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM']. }
    pose proof (S1F 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [ms_step1] in F0. rewrite Z.add_0_r in F0. unfold step1F in F0.
    cbn [s_ft s_mql s_a1 s_a2 s_budget ml_slo ml_shi ml_sd ml_nlo ml_nhi ml_nd] in F0. fold sb in F0.
    open_sc_in SCA. open_sc_in SCB.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kc; zify_cond_z Kc.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (NEXTK mm a1 ft sl sh sd nl nh nd b nqs w48 w56 w64 w144 w152 w168 w176 w184 w192 w200 w208 w224 w232 w240 w248 w256 w264 w288
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| intros k; apply ms_step1_skip; lia| lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD
        | exact SCA| exact SCB| exact BUD| exact MI| exact MU| exact WM]. }
    cps_destruct (F0 ltac:(lia)) as (c0 & c1 & Hc01 & Hc1n & FC0 & FC1 & FQ). clear F0.
    assert (Hc0 : (0 <= c0 < 2097152)%Z) by lia. assert (Hc1 : (0 <= c1 < 2097152)%Z) by lia.
    pose proof (ftcell_cases _ _ Hc0 FC0) as X0. pose proof (ftcell_cases _ _ Hc1 FC1) as X1.
    pose proof (ftcell_clear _ _ Hc0 FC0) as CL0. pose proof (ftcell_clear _ _ Hc1 FC1) as CL1.
    (* [comment removed for export] *)
    assert (SETK : forall m' (a1' sl' sh' sd' nl' nh' nd' : zarr) (b' nqs' : Z) (v48 v56 v64 v144 v152 v168 v176 v184 v192 v224 v232 v240 v248 v256 v264 v288 : word)
                (y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30 : word),
      (forall k, ms_step1 (S k) qo n ss j (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false) =
                 ms_step1 k qo n ss (j + 1) (MSS a1' a2 (zset ft sb (Z.lor (zget ft sb) SETMASK)) bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') false)) ->
      (0 <= b' <= b)%Z -> zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u32arr s0segs m' (p + 4424) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4024) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3624) (ovw sd' Jd 100) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA v48 v56 v64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss)))) ->
      rw_cells s0segs m' (p + 144) (scb_cells X (mkSCB v144 v152 v168 v176 v184 v192 (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 (zget ft sb)) (Z_to_bv 64 ss) v224
                                        v232 v240 v248 v256 v264 (Z_to_bv 64 b') v288)) ->
      rw_cells s0segs m' (p + 292) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 16, p + 296); (p + 3624, p + 4824)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 j) (Z_to_bv 64 FT)
                            y9 (Z_to_bv 64 2097152) (Z_to_bv 64 18446744073707454463) (Z_to_bv 64 (FT + 1024 * ss)) y13 y14 y15 y16
                            (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                            y24 si (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a278) fc None m' (seg_rom s0segs))).
    { intros m' a1' sl' sh' sd' nl' nh' nd' b' nqs' v48 v56 v64 v144 v152 v168 v176 v184 v192 v224 v232 v240 v248 v256 v264 v288
             y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30 EQ Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCA' SCB' BUD' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD SCA SCB BUD MI MU WM. open_sc_in SCA'. open_sc_in SCB'.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm FT _ sb _ FTB' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store FTB' sb (Z.lor (zget ft sb) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (NEXTK mm a1' (zset ft sb (Z.lor (zget ft sb) SETMASK)) sl' sh' sd' nl' nh' nd' b' nqs' v48 v56 v64 v144 v152 v168 v176 v184 v192
                      (Z_to_bv 64 (FT + 4 * sb)) (Z_to_bv 64 (zget ft sb)) v224 v232 v240 v248 v256 v264 v288 _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EQ| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'
        | exact SCA'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM']. }
    clear NEXTK.
    (* [comment removed for export] *)
    wstep. wstep. rd32_at FTB sb.
    wstep. wstep. replace (FT + 1024 * ss + j * 4)%Z with (FT + 4 * sb)%Z in SCB by lia. wstep.
    wstep; if_cases Km; [apply slt42_true in Km; [|lia] | apply slt42_false in Km; [|lia]].
    { (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd b nqs w48 w56 w64 w144 w152 w168 w176 w184 w192 w224 w232 w240 w248 w256 w264 w288 _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD| exact SCA| exact SCB| exact BUD| exact MI| exact MU| exact WM].
      intros k. apply ms_step1_noq; [lia|]. left. fold sb.
      destruct X0 as [E0|E0]; [exfalso; lia|]. rewrite E0, <- lor_setmask by lia. apply has_setmask_marked. lia. }
    destruct X0 as [E0|E0]; [|exfalso; lia].
    (* [comment removed for export] *)
    rd32_at FTB (sb + 1)%Z.
    wstep. rewrite land_CM64, CL1 by lia.
    wstep. wstep. rewrite E0.
    wstep; if_cases Kge; zify_cond_z Kge.
    { (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1 sl sh sd nl nh nd b nqs w48 w56 w64 _ w152 w168 w176 w184 w192 w224 w232 w240 w248 w256 w264 w288 _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact A1OK| exact PR| exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD| exact SCA| | exact BUD| exact MI| exact MU| exact WM].
      - intros k. apply ms_step1_noq; [lia|]. right. fold sb. rewrite CL0, CL1. lia.
      - rewrite <- E0. exact SCB. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
    destruct (FQ E0 ltac:(lia)) as [OKv FIN]. rewrite E0 in SCB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (S0_qcall j sb c0 (c1 - 1)%Z b a1 a2 ft sl sh sd nl nh nd Jlo Jhi Jd w48 si w64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss))
                  w152 w168 w176 w184 w192 (Z_to_bv 64 ss) w224 w232 w240 w248 w256 w264 w288 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| lia| lia| exact E0| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact FTB| exact SLO| exact SHI| exact SD| exact SCA| | exact BUD| exact MI| apply munch_refl| apply wmono_refl| |].
    { replace (c1 - 1)%Z with (c1 + -1)%Z by lia. exact SCB. }
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' b' v152 v168 v176 v184 v192 v232 v240 v248 v256 v264 v288 y0 y4 y5 y6 y9 y13 y14 y15 y16 y24 y27 y28 y29 y30.
      intros EQl Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCA' SCB' BUD' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD SCA SCB BUD MI. unfold WS1 in MU'. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      rewrite <- E0 in SCB'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (SETK mm a1' sl' sh' sd' nl' nh' nd' b' (nqs + (c1 - 1 - c0 + 1))%Z (Z_to_bv 64 j) si x24 _ v152 v168 v176 v184 v192 (Z_to_bv 64 0) v232 v240 v248 v256 v264 v288
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact SCA'| exact SCB'| exact BUD'| exact MI'| exact MU| exact WM].
      intros k. pose proof (ms_step1_q k qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' 0 sl' sh' sd' nl' nh' nd' b' false ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with false in SQ by (symmetry; apply Z.ltb_ge; lia). exact SQ.
    - (* [comment removed for export] *)
      intros m' a1' sl' sh' sd' nl' nh' nd' qsp' b' v152 v168 v176 v184 v192 v224 v232 v240 v248 v256 v264 v272 v288
             y0 y4 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y24 y25 y27 y28 y29 y30.
      intros EQl Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' SCA' SCB' BUD' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD SCA SCB BUD MI. unfold WS1 in MU'. transport_after_call s0segs mq m' MU' WM'. clear MU' WM'.
      eapply (Kexit m' a1' ft sl' sh' sd' nl' nh' nd' b' (nqs + (c1 - 1 - c0 + 1))%Z (Z_to_bv 64 j) si x24 _ v152 v168 v176 v184 v192 _ _ v224 v232 v240 v248 v256 v264 v272 v288);
        [| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact FTB'| exact SLO'| exact SHI'| exact SD'| exact SCA'| exact SCB'| exact BUD'| exact MI'| exact MU| exact WM].
      pose proof (ms_step1_q cnt qo n ss j a1 a2 ft bd cs ce b nqs sl sh sd nl nh nd a1' qsp' sl' sh' sd' nl' nh' nd' b' true ltac:(lia)) as SQ.
      cbv zeta in SQ. fold sb in SQ. rewrite CL0, CL1 in SQ. rewrite E0 in SQ at 1.
      specialize (SQ (has_setmask_small c0 Hc0) ltac:(lia) EQl). replace (b' <? 0) with true in SQ by (symmetry; apply Z.ltb_lt; lia). exact SQ.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
