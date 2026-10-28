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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 BzCLemmasMs4 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV BzIncs S0_cmp_msL S0_cmp_msM S0_cmp_msN.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope Z_scope.

Open Scope bv_scope.
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


Definition bigN (qoff nb : Z) (ro : zarr) (i : Z) (s : mss) : Prop :=
  forall k, (k < 256)%nat -> let s' := ms_step1 k qoff nb (zget ro i) 0 s in s_exit s' = false -> (0 <= s_nqs s' /\ s_nqs s' + nb <= 2147483647)%Z.

Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Definition WB : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (p + 8, p + 2644); (p + 3668, p + 4904)]%Z.

  (* [comment removed for export] *)
  Lemma S0_big : forall (i b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd ro : zarr) (Jlo Jhi Jd : list byte) (nx : list word)
      (w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 : word)
      (x0 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in let ss := zget ro i in
    (0 <= i <= 255)%Z -> (0 <= b < 2147483648)%Z -> bigF qo n ro i s -> bigN qo n ro i s ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u8arr s0segs m (p + 2388) (zb8 bd 256) -> u32arr s0segs m (p + 1364) (zw32 cs 256) -> u32arr s0segs m (p + 340) (zw32 ce 256) ->
    u32arr s0segs m (p + 4504) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4104) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx -> u32arr s0segs m (p + 2644) (zw32 ro 256) ->
    rw_cells s0segs m (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 w96 w104 w112)) ->
    rw_cells s0segs m (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)) ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> rw_cells s0segs m 210296 [CB 56 incs_bytes] ->
    mem_inv s0segs m -> munch WB me m -> wmono s0segs me m ->
    apart FT 262148 210296 56 -> apart A1 ARR1_SIZE 210296 56 -> apart A2 ARR2_SIZE 210296 56 ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30 : word),
      (i < 255)%Z ->
      ms_big ro qo n i s = MSS a1' a2' ft' (zset bd ss 1) csF ceB b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 (zset bd ss 1) 256) -> u32arr s0segs m' (p + 1364) (zw32 csF 256) -> u32arr s0segs m' (p + 340) (zw32 ceB 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WB me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            (Z_to_bv 64 (i + 1)) y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                            y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x20dfc) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30 : word),
      (i = 255)%Z ->
      ms_big ro qo n i s = MSS a1' a2' ft' (zset bd ss 1) csF ceB b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 (zset bd ss 1) 256) -> u32arr s0segs m' (p + 1364) (zw32 csF 256) -> u32arr s0segs m' (p + 340) (zw32 ceB 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WB me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                            y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22104) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' ft' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      ms_big ro qo n i s = MSS a1' a2 ft' bd cs ce b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd 256) -> u32arr s0segs m' (p + 1364) (zw32 cs 256) -> u32arr s0segs m' (p + 340) (zw32 ce 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WB me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 b') y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22114) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 i) x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 nqs) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                          x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20dfc) fc None m (seg_rom s0segs)).
  Proof.
    intros i b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro Jlo Jhi Jd nx w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288
           x0 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x26 x27 x28 x29 x30 me m.
    intros s ss Hi Hb BF BN A1OK A2OK BDOK PR LJlo LJhi LJd Lnx AR1 AR2 FTB BD CS CE SLO SHI SD NX RO SCA SCB BUD INC MI MU WM APF APA1 APA2 Kn Kl Kx. subst s.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof alloc_ceiling_ge as ACG.
    pose proof APF as APFu. pose proof APA1 as APA1u. pose proof APA2 as APA2u. unfold apart in APFu, APA1u, APA2u.
    unfold WB in *.
    pose proof (zw32_length ro 256 ltac:(lia)) as Lro.
    cps_destruct BF as (Hss & F1 & F23). fold ss in Hss, F1, F23.
    open_sc_in SCA. open_sc_in SCB.
    (* [comment removed for export] *)
    do 6 wstep.
    pose proof (zw32_read s0segs _ (p + 2644) ro 256 i _ RO ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. wstep. clear RD. fold ss.
    do 5 wstep.
    try replace (ss * 256)%Z with (256 * ss)%Z in SCA by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (S0_step1 X Q XOK XSEP 256 0 ss b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd Jlo Jhi Jd nx (Z_to_bv 64 i) (Z_to_bv 64 ss) w96 w104 w112
                  w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| lia| intros k Hk; apply F1; lia| intros k Hk; apply (BN k); lia| exact A1OK| exact A2OK| exact PR| exact LJlo| exact LJhi| exact LJd| exact AR1| exact AR2| exact FTB
      | exact SLO| exact SHI| exact SD| exact Lnx| exact NX| exact SCA| exact SCB| exact BUD| exact INC| exact MI| apply munch_refl| apply wmono_refl| exact APF| exact APA1| |].
    - (* [comment removed for export] *)
      intros m1 a1' ft' sl' sh' sd' nl' nh' nd' nx' b' nqs' v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
             y0 y4 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y26 y27 y28 y29 y30.
      intros EQ1 Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' Lnx' NX' SCA' SCB' BUD' INC' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD NX SCA SCB BUD INC MI. unfold WS1 in MU'. bz_params. open_sc_in SCB'.
      transport_after_call s0segs mq m1 MU' WM'. clear MU' WM'.
      cps_destruct (F23 ltac:(rewrite EQ1; reflexivity)) as (BD0 & FTV & FWF & FWfin & BWF & BWfin & A1007 & F3). clear F23.
      rewrite EQ1 in BD0, FTV, FWF, FWfin, BWF, BWfin, A1007, F3. cbn [s_ft s_a1 s_a2 s_bd s_cs s_ce] in BD0, FTV, FWF, FWfin, BWF, BWfin, A1007, F3.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mr end.
      enter_with (S0_step2 X Q XOK XSEP i ss a1' a2 ft' bd cs ce (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112
                    (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mr mr);
        [st_eq| lia| lia| exact BD0| exact FTV| exact FWF| exact FWfin| exact BWF| exact BWfin| exact A1007| exact OK'| exact A2OK| exact BDOK| exact PR'
        | exact AR1'| exact AR2'| exact FTB'| exact BD| exact CS| exact CE| exact SCA'| exact SCB'| exact MI'| apply munch_refl| apply wmono_refl|].
      intros last m2 u5 u6 u9 u10 u11 u12 u13 u14 u15 u16 u17 u19. cbv zeta.
      intros Elast OKB PRB FTVm CSR CER AR1'' AR2'' FTB'' BD'' CS'' CE'' SCA'' SCB'' MI2 MU2 WM2.
      clear AR1' AR2' FTB' BD CS CE SCA' SCB' MI'. unfold W2 in MU2.
      transport_after_call s0segs mr m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      pose proof (ms_big_eq ro qo n i (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false)) as EB. cbv zeta in EB. fold ss in EB.
      rewrite EQ1 in EB. cbn [s_exit s_ft s_a1 s_a2 s_bd s_cs s_ce s_budget s_nqs s_mql] in EB.
      destruct (ms_copy_init 256 cs ce ft' ss 0) as [cs0 ce0] eqn:Eci. cbn [fst snd] in *.
      destruct (ms_copy_fwd (S (Z.to_nat n)) a1' cs0 a2 bd n ss (clearmask (zget ft' (Z.shiftl ss 8)))) as [[a1F csF] jF] eqn:Erf. cbn [fst snd] in *.
      destruct (ms_copy_bwd (S (Z.to_nat n)) a1F ce0 a2 bd n ss (clearmask (zget ft' (Z.shiftl (ss + 1) 8)) - 1)) as [[a1B ceB] jB] eqn:Erb. cbn [fst snd] in *.
      destruct (Z.eqb_spec i 255) as [E255|N255].
      + (* [comment removed for export] *)
        subst last. replace (i <? 255) with false in EB by (symmetry; apply Z.ltb_ge; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kl mm a1B a2 (ms_mark 256 ft' ss 0) sl' sh' sd' nl' nh' nd' csF ceB nx' b' nqs'
                        (Z_to_bv 64 i) (Z_to_bv 64 ss) (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112
                        v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact EB| lia| exact OKB| exact A2OK| exact PRB| exact Lnx'| exact AR1''| exact AR2''| exact FTB''| exact BD''| exact CS''| exact CE''
          | exact SLO'| exact SHI'| exact SD'| exact NX'| exact RO| exact SCA''| exact SCB''| exact BUD'| exact INC'| exact MI2| exact MU| exact WM].
      + subst last. replace (i <? 255) with true in EB by (symmetry; apply Z.ltb_lt; lia). cbv zeta in EB.
        destruct (F3 ltac:(lia)) as [Ble Bn].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mt end.
        enter_with (S0_step3 X Q XOK XSEP i ss a1B a2 (ms_mark 256 ft' ss 0)
                      (mkSCA (Z_to_bv 64 i) (Z_to_bv 64 ss) (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112)
                      (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mt mt);
          [st_eq| lia| lia| exact FTVm| exact Ble| exact Bn| reflexivity| exact OKB| exact A2OK| exact PRB| exact AR1''| exact AR2''| exact FTB''| exact SCA''| exact SCB''| exact MI2
          | apply munch_refl| apply wmono_refl|].
        intros m3 z11 z13 z14 z15 z16 z17. cbv zeta. intros OKQ AR1q AR2q FTBq SCAq SCBq MIq MUq WMq.
        clear AR1'' AR2'' FTB'' SCA'' SCB'' MI2.
        transport_after_call s0segs mt m3 MUq WMq. clear MUq WMq.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kn mm a1B _ (ms_mark 256 ft' ss 0) sl' sh' sd' nl' nh' nd' csF ceB nx' b' nqs'
                        (Z_to_bv 64 i) (Z_to_bv 64 ss) (Z_to_bv 64 ss) (Z_to_bv 64 (256 * ss)) v96 v104 v112
                        v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
                        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact EB| lia| exact OKB| exact OKQ| exact PRB| exact Lnx'| exact AR1q| exact AR2q| exact FTBq| exact BD''| exact CS''| exact CE''
          | exact SLO'| exact SHI'| exact SD'| exact NX'| exact RO| exact SCAq| exact SCBq| exact BUD'| exact INC'| exact MIq| exact MU| exact WM].
    - (* [comment removed for export] *)
      intros m1 a1' ft' sl' sh' sd' nl' nh' nd' nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
             y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30.
      intros EQ1 Hb' OK' PR' AR1' AR2' FTB' SLO' SHI' SD' Lnx' NX' SCA' SCB' BUD' INC' MI' MU' WM'.
      clear AR1 AR2 FTB SLO SHI SD NX SCA SCB BUD INC MI. unfold WS1 in MU'. bz_params.
      transport_after_call s0segs mq m1 MU' WM'. clear MU' WM'.
      pose proof (ms_big_eq ro qo n i (MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false)) as EB. cbv zeta in EB. fold ss in EB.
      rewrite EQ1 in EB. cbn [s_exit] in EB.
      eapply (Kx m1 a1' ft' sl' sh' sd' nl' nh' nd' nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288);
        [exact EB| lia| exact OK'| exact PR'| exact Lnx'| exact AR1'| exact AR2'| exact FTB'| exact BD| exact CS| exact CE| exact SLO'| exact SHI'| exact SD'| exact NX'| exact RO
        | exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
  (* [comment removed for export] *)
  Lemma S0_bigs : forall (cnt : nat) (i b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd ro : zarr) (Jlo Jhi Jd : list byte) (nx : list word)
      (w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 : word)
      (x0 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - i)%Z -> (0 <= i <= 255)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, i + Z.of_nat k <= 255 -> let s' := ms_bigs k ro qo n i s in s_exit s' = false -> bigF qo n ro (i + Z.of_nat k) s')%Z ->
    (forall k, i + Z.of_nat k <= 255 -> let s' := ms_bigs k ro qo n i s in s_exit s' = false -> bigN qo n ro (i + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u8arr s0segs m (p + 2388) (zb8 bd 256) -> u32arr s0segs m (p + 1364) (zw32 cs 256) -> u32arr s0segs m (p + 340) (zw32 ce 256) ->
    u32arr s0segs m (p + 4504) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4104) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx -> u32arr s0segs m (p + 2644) (zw32 ro 256) ->
    rw_cells s0segs m (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 w96 w104 w112)) ->
    rw_cells s0segs m (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)) ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> rw_cells s0segs m 210296 [CB 56 incs_bytes] ->
    mem_inv s0segs m -> munch WB me m -> wmono s0segs me m ->
    apart FT 262148 210296 56 -> apart A1 ARR1_SIZE 210296 56 -> apart A2 ARR2_SIZE 210296 56 ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30 : word),
      ms_bigs cnt ro qo n i s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd' 256) -> u32arr s0segs m' (p + 1364) (zw32 cs' 256) -> u32arr s0segs m' (p + 340) (zw32 ce' 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WB me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                            y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22104) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      ms_bigs cnt ro qo n i s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd' 256) -> u32arr s0segs m' (p + 1364) (zw32 cs' 256) -> u32arr s0segs m' (p + 340) (zw32 ce' 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WB me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 b') y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22114) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 i) x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 nqs) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                          x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20dfc) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros i b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro Jlo Jhi Jd nx w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288
           x0 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x26 x27 x28 x29 x30 me m.
    intros s Hcnt Hi Hb BF BN A1OK A2OK BDOK PR LJlo LJhi LJd Lnx AR1 AR2 FTB BD CS CE SLO SHI SD NX RO SCA SCB BUD INC MI MU WM APF APA1 APA2 Klast Kexit. subst s.
    pose proof (BF 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [ms_bigs] in F0. rewrite Z.add_0_r in F0.
    pose proof (BN 0%nat ltac:(cbn; lia) eq_refl) as N0. cbn [ms_bigs] in N0. rewrite Z.add_0_r in N0.
    rewrite ms_bigs_S in Klast, Kexit. cbv zeta in Klast. cbv zeta in Kexit.
    eapply (S0_big i b nqs a1 a2 ft bd cs ce sl sh sd nl nh nd ro Jlo Jhi Jd nx w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288
              x0 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x26 x27 x28 x29 x30 me m);
      [lia| lia| exact F0| exact N0| exact A1OK| exact A2OK| exact BDOK| exact PR| exact LJlo| exact LJhi| exact LJd| exact Lnx| exact AR1| exact AR2| exact FTB| exact BD| exact CS| exact CE
      | exact SLO| exact SHI| exact SD| exact NX| exact RO| exact SCA| exact SCB| exact BUD| exact INC| exact MI| exact MU| exact WM| exact APF| exact APA1| exact APA2| | |].
    - (* [comment removed for export] *)
      intros m' a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
             y0 y4 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30.
      intros Hlt EB Hb' OK1 OK2 PR' Lnx' AR1' AR2' FTB' BD' CS' CE' SLO' SHI' SD' NX' RO' SCA' SCB' BUD' INC' MI' MU' WM'.
      rewrite EB in Klast, Kexit. cbn [s_exit] in Klast, Kexit.
      assert (BDOK' : zbok (zset bd (zget ro i) 1)) by (apply zbok_zset; [exact BDOK| lia]).
      eapply (IH (i + 1)%Z b' nqs' a1' a2' ft' _ csF ceB sl' sh' sd' nl' nh' nd' ro Jlo Jhi Jd nx' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me m');
        [lia| lia| lia| | | exact OK1| exact OK2| exact BDOK'| exact PR'| exact LJlo| exact LJhi| exact LJd| exact Lnx'| exact AR1'| exact AR2'| exact FTB'| exact BD'| exact CS'| exact CE'
        | exact SLO'| exact SHI'| exact SD'| exact NX'| exact RO'| exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU'| exact WM'| exact APF| exact APA1| exact APA2| | ].
      + intros k Hk. pose proof (BF (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Fk. rewrite ms_bigs_S in Fk. cbv zeta in Fk. rewrite EB in Fk. cbn [s_exit] in Fk. cbv zeta.
        rewrite Nat2Z.inj_succ in Fk. replace (i + 1 + Z.of_nat k)%Z with (i + Z.succ (Z.of_nat k))%Z by lia. exact Fk.
      + intros k Hk. pose proof (BN (S k) ltac:(rewrite Nat2Z.inj_succ; lia)) as Nk. rewrite ms_bigs_S in Nk. cbv zeta in Nk. rewrite EB in Nk. cbn [s_exit] in Nk. cbv zeta.
        rewrite Nat2Z.inj_succ in Nk. replace (i + 1 + Z.of_nat k)%Z with (i + Z.succ (Z.of_nat k))%Z by lia. exact Nk.
      + intros *. intros EQ2 Hb2. eapply Klast; [exact EQ2| lia].
      + intros *. intros EQ2 Hb2. eapply Kexit; [exact EQ2| lia].
    - (* [comment removed for export] *)
      intros m' a1' a2' ft' sl' sh' sd' nl' nh' nd' csF ceB nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
             y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30.
      intros E255 EB Hb' OK1 OK2 PR' Lnx' AR1' AR2' FTB' BD' CS' CE' SLO' SHI' SD' NX' RO' SCA' SCB' BUD' INC' MI' MU' WM'.
      rewrite EB in Klast, Kexit. cbn [s_exit] in Klast, Kexit.
      assert (BDOK' : zbok (zset bd (zget ro i) 1)) by (apply zbok_zset; [exact BDOK| lia]).
      assert (cnt = 0%nat) as -> by lia. cbn [ms_bigs] in Klast.
      eapply (Klast m' a1' a2' ft' _ csF ceB sl' sh' sd' nl' nh' nd' nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288);
        [reflexivity| lia| exact OK1| exact OK2| exact BDOK'| exact PR'| exact Lnx'| exact AR1'| exact AR2'| exact FTB'| exact BD'| exact CS'| exact CE'| exact SLO'| exact SHI'| exact SD'
        | exact NX'| exact RO'| exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU'| exact WM'].
    - intros m' a1' ft' sl' sh' sd' nl' nh' nd' nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
             y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30.
      intros EB Hb' OK1 PR' Lnx' AR1' AR2' FTB' BD' CS' CE' SLO' SHI' SD' NX' RO' SCA' SCB' BUD' INC' MI' MU' WM'.
      rewrite EB in Kexit. cbn [s_exit] in Kexit.
      eapply (Kexit m' a1' a2 ft' bd cs ce sl' sh' sd' nl' nh' nd' nx' b' nqs' v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288);
        [reflexivity| lia| exact OK1| exact A2OK| exact BDOK| exact PR'| exact Lnx'| exact AR1'| exact AR2'| exact FTB'| exact BD'| exact CS'| exact CE'| exact SLO'| exact SHI'| exact SD'
        | exact NX'| exact RO'| exact SCA'| exact SCB'| exact BUD'| exact INC'| exact MI'| exact MU'| exact WM'].
  Time Qed.
End S0MS.

End ACeilS1.
