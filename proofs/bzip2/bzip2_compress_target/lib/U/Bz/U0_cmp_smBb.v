(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpCutSmB BzCFactsSmB BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_smBa U0_cmp_smBh.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GGU.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lp len : zarr).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Hypothesis LF : forall t v, (0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z.
  Hypothesis LPF : nG = 6%Z -> forall v j, (0 <= v < A)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * v + j) = true /\ (0 <= zget lp (4 * v + j) < 2097152)%Z.
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation S6 := (Z_to_bv 64 (4 * A)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).

  Notation RG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).

  Notation Wfc := [(SP + 48, SP + 528); (SP + 584, SP + 800); (SP + 832, SP + 888); (SP + 1084, SP + 1096)]%Z.
  Definition FC_spec : Prop :=
    forall (gs : Z) (cb : zarr) (m me : word -> option byte) (J1 J2 J3 : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    nG = 6%Z -> (0 <= gs)%Z -> (gs + 50 <= nMTF)%Z ->
    (forall k, (0 <= k < 50)%Z -> (0 <= QV arr1 gs k < A)%Z) ->
    (forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= PV arr1 lp gs k j < 2097152)%Z) ->
    (forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * QV arr1 gs k + j) = true) ->
    length J1 = 480%nat -> length J2 = 216%nat -> length J3 = 56%nat ->
    u8arr s0segs m (SP + 48) J1 -> u8arr s0segs m (SP + 584) J2 -> u8arr s0segs m (SP + 832) J3 ->
    u8arr s0segs m (SP + 1084) (zb8 cb 12) ->
    mem_inv s0segs m -> munch Wfc me m -> wmono s0segs me m ->
    (forall m', munch Wfc me m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wfc me m' -> u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW s0segs Wfc me (SP + 40) [C8 S6] -> frdW s0segs Wfc me (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW s0segs Wfc me (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] -> frdW s0segs Wfc me (SP + 1008) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wfc me (SP + 1016) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wfc me (SP + 1024) [C8 (Z_to_bv 64 (gs + 50))] ->
    frdW s0segs Wfc me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (S0 S1 S2 : Z) (J1' J2' J3' : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      u8arr s0segs m' (SP + 1084) (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv s0segs m' -> munch Wfc me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19870) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17688) fc None m (seg_rom s0segs)).

  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  Definition FR_spec : Prop :=
    forall (rf0 : zarr) (gs bt B : Z) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= gs)%Z -> (gs + 50 <= nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + 50 <= 2000000000)%Z ->
    (forall k, (0 <= k < 50)%Z -> (0 <= QV arr1 gs k < A)%Z) ->
    u32arr s0segs m (E + 45448) (ovw rf0 (jseg J 45448 6192) 1548) -> RFrow rf0 bt A B ->
    mem_inv s0segs m -> munch Wrf me m -> wmono s0segs me m ->
    (forall m', munch Wrf me m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    frdW s0segs Wrf me (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] -> frdW s0segs Wrf me (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wrf me (SP + 1024) [C8 (Z_to_bv 64 (gs + 50))] -> frdW s0segs Wrf me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (rf' : zarr) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
      u32arr s0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) ->
      rf' = sm_rfreq_inc 50 rf0 arr1 bt gs -> RFrow rf' bt A (B + 50) ->
      mem_inv s0segs m' -> munch Wrf me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b310) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) (Z_to_bv 64 (1032 * bt)) a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x199fc) fc None m (seg_rom s0segs)).

  Hypothesis HFC : FC_spec.
  Hypothesis HFR : FR_spec.

  Definition Wg : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 45448, E + 51640); (SP + 48, SP + 528); (SP + 584, SP + 800); (SP + 832, SP + 888); (SP + 896, SP + 904); (SP + 912, SP + 920);
     (SP + 936, SP + 944); (SP + 976, SP + 984); (SP + 1024, SP + 1032); (SP + 1060, SP + 1096)]%Z.
  Ltac gside MU VAR1 VLEN VLPK :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ A1 _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VAR1; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); u_sub_fp
    | |- forall _, munch _ _ _ -> u8arr _ _ (E + 37708)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VLEN; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); u_sub_fp
    | |- forall _, munch _ _ _ -> u32arr _ _ (E + 51640)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply VLPK; refine (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ _ MU_)); u_sub_fp
    | |- frdW _ ?W' ?mm ?a _ =>
        first [ lazymatch goal with V : frdW _ _ _ a _ |- _ => eapply (frdW_sub s0segs _ W' _ mm); [exact V| exact MU| u_sub_fp] end
              | lazymatch goal with R : rw_cells _ mm a _ |- _ => apply frdW_intro; [exact R| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia] end
              | idtac ]
    | |- (_ <= _)%Z => first [lia | idtac]
    | |- (_ < _)%Z => first [lia | idtac]
    | |- (_ /\ _) => first [lia | idtac]
    | |- (_ \/ _) => first [lia | idtac]
    | |- _ => idtac
    end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_sm_grp : forall (rf sel cost fave : zarr) (gs nSel totc : Z) (J1 J2 J3 jc : list byte) (v896 v936 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> (0 <= nSel < 18001)%Z -> (0 <= totc <= 65535 * nSel)%Z ->
    (forall t, (0 <= t < nG)%Z -> RFrow rf t A gs) -> (forall t, (0 <= t < 6)%Z -> (0 <= zget fave t <= nSel)%Z) ->
    length J1 = 480%nat -> length J2 = 216%nat -> length J3 = 56%nat -> length jc = 12%nat ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (SP + 48) J1 -> u8arr s0segs m (SP + 584) J2 -> u8arr s0segs m (SP + 832) J3 ->
    rw_cells s0segs m (SP + 896) [C8 v896] -> rw_cells s0segs m (SP + 912) [C8 (Z_to_bv 64 totc)] ->
    rw_cells s0segs m (SP + 936) [C8 v936] -> rw_cells s0segs m (SP + 976) [C8 (Z_to_bv 64 nSel)] ->
    rw_cells s0segs m (SP + 1024) [C8 (Z_to_bv 64 gs)] ->
    u32arr s0segs m (SP + 1060) (zw32 fave 6) ->
    u8arr s0segs m (SP + 1084) jc ->
    mem_inv s0segs m -> munch Wg me m -> wmono s0segs me m ->
    (forall m', munch Wg me m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wg me m' -> u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    (forall m', munch Wg me m' -> u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW s0segs Wg me (SP + 40) [C8 S6] ->
    frdW s0segs Wg me (SP + 800) [C8 (Z_to_bv 64 18002)] -> frdW s0segs Wg me (SP + 808) [C8 (NOT (SP + 1060))] ->
    frdW s0segs Wg me (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs Wg me (SP + 824) [C8 (NOT (E + 1704))] ->
    frdW s0segs Wg me (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> frdW s0segs Wg me (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
    frdW s0segs Wg me (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    frdW s0segs Wg me (SP + 944) [C8 (NOT (E + 45448))] -> frdW s0segs Wg me (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    frdW s0segs Wg me (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wg me (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    frdW s0segs Wg me (SP + 1008) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wg me (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wg me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (J1' J2' J3' jc' : list byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s5' s7' s8' s10' s11' t3' t4' t5' t6' : word),
      let ge := GE nMTF gs in let cst := COSTC arr1 len lp nG gs ge cost in let r := sm_best (Z.to_nat nG) cst 0 999999999 (-1) in
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat -> length jc' = 12%nat -> (0 <= snd r < nG)%Z -> (0 <= fst r <= 65535)%Z ->
      u32arr s0segs m' (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 (snd r) gs) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (zset sel nSel (snd r mod 256)) (jseg J 1704 18002) 18002) ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      rw_cells s0segs m' (SP + 896) [C8 (Z_to_bv 64 ge)] -> rw_cells s0segs m' (SP + 912) [C8 (Z_to_bv 64 (totc + fst r))] ->
      rw_cells s0segs m' (SP + 936) [C8 (Z_to_bv 64 (gs + 50))] -> rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (nSel + 1))] ->
      rw_cells s0segs m' (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] ->
      u32arr s0segs m' (SP + 1060) (zw32 (zincr fave (snd r)) 6) ->
      u8arr s0segs m' (SP + 1084) jc' ->
      mem_inv s0segs m' -> munch Wg me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s5' S6 s7' s8' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 (if (ge + 1 <? nMTF)%Z then 0x17600 else 0x1b32c)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17600) fc None m (seg_rom s0segs)).
  Proof.
    intros rf sel cost fave gs nSel totc J1 J2 J3 jc v896 v936 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6
           Hgs HnS Htc RFR FVB LJ1 LJ2 LJ3 Ljc RFQ SEL SP1 SP2 SP3 C896 C912 C936 C976 C1024 FAVE COST MI MU WM VAR1 VLEN VLPK
           V40 V800 V808 V816 V824 V904 V920 V928 V944 V952 V992 V1000 V1008 V1016 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold Wg in *.
    pose proof CEP as CEP'. unfold CEIL in CEP'.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    cbv zeta in K. set (ge := GE nMTF gs) in *.
    (* [comment removed for export] *)
    assert (KT : forall (bc bt : Z) (cst : zarr) (m4 : word -> option byte) (J14 J24 J34 jc4 : list byte) (yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys7 ys8 ys10 ys11 y3 y4 y5 y6 : word),
      cst = COSTC arr1 len lp nG gs ge cost -> sm_best (Z.to_nat nG) cst 0 999999999 (-1) = (bc, bt) -> (0 <= bt < nG)%Z -> (0 <= bc <= 65535)%Z ->
      length J14 = 480%nat -> length J24 = 216%nat -> length J34 = 56%nat -> length jc4 = 12%nat ->
      u32arr s0segs m4 (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 bt gs) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m4 (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      u8arr s0segs m4 (SP + 48) J14 -> u8arr s0segs m4 (SP + 584) J24 -> u8arr s0segs m4 (SP + 832) J34 ->
      rw_cells s0segs m4 (SP + 896) [C8 (Z_to_bv 64 ge)] -> rw_cells s0segs m4 (SP + 912) [C8 (Z_to_bv 64 (totc + bc))] ->
      rw_cells s0segs m4 (SP + 936) [C8 (Z_to_bv 64 (gs + 50))] -> rw_cells s0segs m4 (SP + 976) [C8 (Z_to_bv 64 nSel)] ->
      rw_cells s0segs m4 (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] ->
      u32arr s0segs m4 (SP + 1060) (zw32 (zincr fave bt) 6) -> u8arr s0segs m4 (SP + 1084) jc4 ->
      mem_inv s0segs m4 ->
      munch [(E + 1704, E + 19706); (E + 45448, E + 51640); (SP + 48, SP + 528); (SP + 584, SP + 800); (SP + 832, SP + 888); (SP + 896, SP + 904); (SP + 912, SP + 920);
             (SP + 936, SP + 944); (SP + 976, SP + 984); (SP + 1024, SP + 1032); (SP + 1060, SP + 1096)]%Z me m4 ->
      wmono s0segs me m4 ->
      evt s0segs Q (MS (RG yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 S6 ys7 ys8 ys10 ys11 y3 y4 y5 y6) F (Z_to_bv 64 0x1b310) fc None m4 (seg_rom s0segs))).
    { intros bc bt cst m4 J14 J24 J34 jc4 yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys7 ys8 ys10 ys11 y3 y4 y5 y6 Ecst EB Hbt Hbc LJ14 LJ24 LJ34 Lj4 RFQ4 SEL4 S14 S24 S34 R896 R912 R936 R976 R1024 FAVE4 COST4 MI4 MU4 WM4.
      eapply evt_eq; [| eapply U0_sm_tail with (gs := gs) (nSel := nSel) (me := m4)].
      all: gside MU4 VAR1 VLEN VLPK.
      { st_eq. }
      - (* [comment removed for export] *)
        intros m5 xa0 xa1 Hlt R976' MI5 MU5 WM5. clear R976 MI4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
        pose proof (K m5 J14 J24 J34 jc4 yra y0 y1 y2 xa0 xa1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys7 ys8 ys10 ys11 y3 y4 y5 y6) as K'. rewrite <- Ecst, EB in K'. cbn [fst snd] in K'.
        replace (ge + 1 <? nMTF)%Z with true in K' by (symmetry; apply Z.ltb_lt; lia).
        enter_with K'; [st_eq| exact LJ14| exact LJ24| exact LJ34| exact Lj4| exact Hbt| exact Hbc| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| exact R976'| eassumption| eassumption| eassumption| assumption| assumption| assumption].
      - (* [comment removed for export] *)
        intros m5 xa0 xa1 Hge R976' MI5 MU5 WM5. clear R976 MI4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
        pose proof (K m5 J14 J24 J34 jc4 yra y0 y1 y2 xa0 xa1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys7 ys8 ys10 ys11 y3 y4 y5 y6) as K'. rewrite <- Ecst, EB in K'. cbn [fst snd] in K'.
        replace (ge + 1 <? nMTF)%Z with false in K' by (symmetry; apply Z.ltb_ge; lia).
        enter_with K'; [st_eq| exact LJ14| exact LJ24| exact LJ34| exact Lj4| exact Hbt| exact Hbc| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| exact R976'| eassumption| eassumption| eassumption| assumption| assumption| assumption]. }
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_head with (gs := gs) (jc := jc) (v896 := v896) (v936 := v936) (me := m)].
    all: gside MU VAR1 VLEN VLPK.
    { st_eq. }
    - (* [comment removed for export] *)
      clear COST C1024 C936 C896 MI. intros m1 xa0 xa1 xs6. cbv zeta. fold ge. intros FB COST R1024 R936 R896 MI MU1 WM1.
      transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
      assert (NG6 : nG = 6%Z) by (unfold fastb in FB; destruct (Z.eqb_spec nG 6); [assumption| cbn in FB; discriminate]).
      assert (G49 : (ge - gs = 49)%Z).
      { unfold fastb in FB. fold ge in FB. destruct (Z.eqb_spec (ge - gs) 49); [assumption|]. rewrite NG6 in FB. cbn in FB. discriminate. }
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply (HFC gs znew m1 m1)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { intros k j Hk Hj. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj2 (LPF NG6 _ _ Hq Hj)). }
      { intros k j Hk Hj. unfold QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj1 (LPF NG6 _ _ Hq Hj)). }
      { apply frdW_intro; [replace (gs + 50)%Z with (ge + 1)%Z by lia; exact R1024| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]. }
      clear SP1 SP2 SP3 COST MI.
      intros m2 S0 S1 S2 J12 J22 J32 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya5 ya6 ya7 ys2 ys5 ys7 ys8 ys10 ys11 yt3 yt4 yt5 yt6 ES0 ES1 ES2 LJ12 LJ22 LJ32 SP12 SP22 SP32 COST MI MU2 WM2.
      transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      assert (HS0 : (0 <= S0)%Z). { rewrite ES0. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). lia. }
      assert (HS1 : (0 <= S1)%Z). { rewrite ES1. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). lia. }
      assert (HS2 : (0 <= S2)%Z). { rewrite ES2. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      pose proof (COSTREL_le _ _ 6 nG (COSTREL_fast6 cost S0 S1 S2 HS0 HS1 HS2) ltac:(lia)) as CR.
      pose proof (COSTC_fast arr1 len lp nG nMTF gs cost FB) as CF. rewrite <- ES0, <- ES1, <- ES2 in CF. rewrite <- CF in CR. clear CF. fold ge in CR.
      remember (COSTC arr1 len lp nG gs ge cost) as cst eqn:Ecst.
      assert (HC : forall t, (0 <= t < nG)%Z -> (0 <= zget cst t <= 65535)%Z).
      { destruct CR as [CBOK CREL]. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ (zb8 ?cbx 12) =>
        eapply evt_eq; [| eapply U0_sm_bt with (cb := cbx) (cost := cst)] end.
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      intros za3 za5.
      destruct (U0_cmp_smBa.BEST cst (Z.to_nat nG)) as [bc bt] eqn:EB. unfold U0_cmp_smBa.BEST in EB. cbn [fst snd].
      pose proof (U0_cmp_smBa.BEST_range cst (Z.to_nat nG) ltac:(lia) ltac:(intros t' Ht'; apply HC; lia)) as BR. unfold U0_cmp_smBa.BEST in BR. rewrite EB in BR. cbn [fst snd] in BR. destruct BR as [Hbc Hbt].
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply U0_sm_post with (gs := gs) (bt := bt) (bc := bc) (totc := totc) (nSel := nSel) (fave := fave) (sel := sel) (me := m2)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      2:{ intros; exfalso; congruence. }
      clear FAVE SEL C912 MI. intros m3 wa0 wa1 wa3 _ FAVE SEL R912 MI MU3 WM3.
      transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply (HFR rf gs bt gs m3 m3)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { apply RFR. lia. }
      { apply frdW_intro; [replace (gs + 50)%Z with (ge + 1)%Z by lia; eassumption| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]. }
      clear RFQ MI. intros m4 rf4 zra zt0 zt1 zt2 za0 za1 zza2 zza3 za4 za5' za6 za7 zs2 zs5 zs7 zs8 zs10 zs11 zt3 zt4 zt5 zt6 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
      rewrite ERF4 in RFQ. replace 50%nat with (Z.to_nat (ge - gs + 1)) in RFQ by lia.
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ ?jj =>
        enter_with (KT bc bt cst m4 J12 J22 J32 jj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| first [reflexivity| exact Ecst]| exact EB| lia| exact Hbc| exact LJ12| exact LJ22| exact LJ32| rewrite zb8_length_nat; reflexivity| exact RFQ| exact SEL| exact SP12| exact SP22| exact SP32
          | eassumption| exact R912| eassumption| eassumption| eassumption| exact FAVE| exact COST| exact MI| exact MU| exact WM] end.
    - (* [comment removed for export] *)
      clear COST C1024 C936 C896 MI. intros m1 xa1. cbv zeta. fold ge. intros FB COST R1024 R936 R896 MI MU1 WM1.
      transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
      pose proof (COSTREL_zero cost nG ltac:(lia)) as CR0.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply U0_sm_csg with (gs := gs) (ge := ge) (cb := znew) (cost := zero6 cost) (len := len) (mf := m1)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      clear COST MI. intros m2 cb2 yt0 yt1 ya0 ya1 ya3 ya5 ya6 ya7 COST CR MI MU2 WM2.
      transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      replace (Z.to_nat (ge + 1 - gs)) with (Z.to_nat (ge - gs + 1)) in CR by lia.
      pose proof (COSTC_slow arr1 len lp nG nMTF gs cost FB) as CS. fold ge in CS. rewrite <- CS in CR. clear CS.
      remember (COSTC arr1 len lp nG gs ge cost) as cst eqn:Ecst.
      assert (HC : forall t, (0 <= t < nG)%Z -> (0 <= zget cst t <= 65535)%Z).
      { destruct CR as [CBOK CREL]. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply U0_sm_bt with (cb := cb2) (cost := cst)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      intros za3 za5.
      destruct (U0_cmp_smBa.BEST cst (Z.to_nat nG)) as [bc bt] eqn:EB. unfold U0_cmp_smBa.BEST in EB. cbn [fst snd].
      pose proof (U0_cmp_smBa.BEST_range cst (Z.to_nat nG) ltac:(lia) ltac:(intros t' Ht'; apply HC; lia)) as BR. unfold U0_cmp_smBa.BEST in BR. rewrite EB in BR. cbn [fst snd] in BR. destruct BR as [Hbc Hbt].
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply U0_sm_post with (gs := gs) (bt := bt) (bc := bc) (totc := totc) (nSel := nSel) (fave := fave) (sel := sel) (me := m2)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      1:{ intros; exfalso; congruence. }
      clear FAVE SEL C912 MI. intros m3 wa3 wa5 _ FAVE SEL R912 MI MU3 WM3.
      transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      eapply evt_eq; [| eapply U0_sm_rfsg with (gs := gs) (ge := ge) (bt := bt) (B := gs) (rf := rf) (mf := m3)].
      all: gside MU VAR1 VLEN VLPK.
      { st_eq. }
      { apply RFR. lia. }
      clear RFQ MI. intros m4 rf4 zt0 zt1 za0 za1 zza2 zza3 za4 za5' za6 za7 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
      rewrite ERF4 in RFQ. replace (ge + 1 - gs)%Z with (ge - gs + 1)%Z in RFQ by lia.
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ ?jj =>
        enter_with (KT bc bt cst m4 J1 J2 J3 jj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| first [reflexivity| exact Ecst]| exact EB| lia| exact Hbc| exact LJ1| exact LJ2| exact LJ3| rewrite zb8_length_nat; reflexivity| exact RFQ| exact SEL| exact SP1| exact SP2| exact SP3
          | eassumption| exact R912| eassumption| eassumption| eassumption| exact FAVE| exact COST| exact MI| exact MU| exact WM] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_sm_gloop : forall (n j : nat) (s : sits) (J1 J2 J3 jc : list byte) (v896 v936 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    smB_grp e s -> it_len s = len -> it_lpk e s = lp ->
    (1 <= KSEL e <= 18002)%Z -> (50 * (KSEL e - 1) < nMTF <= 50 * KSEL e)%Z ->
    (Z.of_nat j + Z.of_nat n = KSEL e)%Z -> (1 <= n)%nat ->
    length J1 = 480%nat -> length J2 = 216%nat -> length J3 = 56%nat -> length jc = 12%nat ->
    u32arr s0segs m (E + 45448) (ovw (g_rfreq (Gj e s j)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (g_sel (Gj e s j)) (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (SP + 48) J1 -> u8arr s0segs m (SP + 584) J2 -> u8arr s0segs m (SP + 832) J3 ->
    rw_cells s0segs m (SP + 896) [C8 v896] -> rw_cells s0segs m (SP + 912) [C8 (Z_to_bv 64 (g_totc (Gj e s j)))] ->
    rw_cells s0segs m (SP + 936) [C8 v936] -> rw_cells s0segs m (SP + 976) [C8 (Z_to_bv 64 (g_nSel (Gj e s j)))] ->
    rw_cells s0segs m (SP + 1024) [C8 (Z_to_bv 64 (g_gs (Gj e s j)))] ->
    u32arr s0segs m (SP + 1060) (zw32 (g_fave (Gj e s j)) 6) ->
    u8arr s0segs m (SP + 1084) jc ->
    mem_inv s0segs m -> munch Wg me m -> wmono s0segs me m ->
    (forall m', munch Wg me m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wg me m' -> u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    (forall m', munch Wg me m' -> u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW s0segs Wg me (SP + 40) [C8 S6] ->
    frdW s0segs Wg me (SP + 800) [C8 (Z_to_bv 64 18002)] -> frdW s0segs Wg me (SP + 808) [C8 (NOT (SP + 1060))] ->
    frdW s0segs Wg me (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs Wg me (SP + 824) [C8 (NOT (E + 1704))] ->
    frdW s0segs Wg me (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> frdW s0segs Wg me (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
    frdW s0segs Wg me (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    frdW s0segs Wg me (SP + 944) [C8 (NOT (E + 45448))] -> frdW s0segs Wg me (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    frdW s0segs Wg me (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wg me (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    frdW s0segs Wg me (SP + 1008) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wg me (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wg me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (J1' J2' J3' jc' : list byte) (v896' v936' w1024 : word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s5' s7' s8' s10' s11' t3' t4' t5' t6' : word),
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat -> length jc' = 12%nat ->
      u32arr s0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      rw_cells s0segs m' (SP + 896) [C8 v896'] -> rw_cells s0segs m' (SP + 912) [C8 (Z_to_bv 64 (g_totc (Gend e s)))] ->
      rw_cells s0segs m' (SP + 936) [C8 v936'] -> rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (g_nSel (Gend e s)))] ->
      rw_cells s0segs m' (SP + 1024) [C8 w1024] ->
      u32arr s0segs m' (SP + 1060) (zw32 (g_fave (Gend e s)) 6) ->
      u8arr s0segs m' (SP + 1084) jc' ->
      mem_inv s0segs m' -> munch Wg me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s5' S6 s7' s8' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1b32c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17600) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros j s J1 J2 J3 jc v896 v936 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6
           HGF Elen Elp HK1 HK2 Hj Hn LJ1 LJ2 LJ3 Ljc RFQ SEL SP1 SP2 SP3 C896 C912 C936 C976 C1024 FAVE COST MI MU WM VAR1 VLEN VLPK
           V40 V800 V808 V816 V824 V904 V920 V928 V944 V952 V992 V1000 V1008 V1016 V1032 K.
    destruct HGF as [GF GEND].
    pose proof (GF j ltac:(lia)) as Fj. cbv zeta in Fj. cps_destruct Fj as (Egs & EnS & Htc & RFF & FVB & SLF).
    remember (Gj e s j) as gj eqn:EGJ.
    destruct gj as [rf sel cost fave nSel totc gs]. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in *.
    subst nSel. assert (Egs' : gs = (50 * Z.of_nat j)%Z) by (rewrite Egs; apply Z.min_l; lia).
    eapply (U0_sm_grp rf sel cost fave gs (Z.of_nat j) totc J1 J2 J3 jc v896 v936 m me);
      [lia| lia| lia| | | exact LJ1| exact LJ2| exact LJ3| exact Ljc| exact RFQ| exact SEL| exact SP1| exact SP2| exact SP3| exact C896| exact C912| exact C936| exact C976| exact C1024
      | exact FAVE| exact COST| exact MI| exact MU| exact WM| exact VAR1| exact VLEN| exact VLPK
      | exact V40| exact V800| exact V808| exact V816| exact V824| exact V904| exact V920| exact V928| exact V944| exact V952
      | exact V992| exact V1000| exact V1008| exact V1016| exact V1032|].
    { intros t Ht v Hv. apply RFF; lia. }
    { intros t Ht. apply FVB. lia. }
    clear RFQ SEL SP1 SP2 SP3 C896 C912 C936 C976 C1024 FAVE COST MI MU WM.
    intros m' J1' J2' J3' jc' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s5' s7' s8' s10' s11' t3' t4' t5' t6'. cbv zeta.
    intros LJ1' LJ2' LJ3' Ljc' Hbt Hbc RFQ SEL SP1' SP2' SP3' R896 R912 R936 R976 R1024 FAVE COST MI MU WM.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    (* [comment removed for export] *)
    assert (EG' : Gj e s (S j) = sm_group_iter arr1 len lp nG nMTF (SGS rf sel cost fave (Z.of_nat j) totc gs)).
    { rewrite Gj_S, Elen, Elp, <- EGJ. reflexivity. }
    rewrite sm_group_iter_eq in EG'. cbv zeta in EG'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in EG'.
    destruct (Z.ltb_spec (GE nMTF gs + 1) nMTF) as [LT|GEQ].
    - (* [comment removed for export] *)
      assert (Hj1 : (Z.of_nat (S j) < KSEL e)%Z) by (destruct (Z.lt_ge_cases (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; nia]).
      pose proof (IH (S j) s J1' J2' J3' jc' (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 (gs + 50)) m' me) as IH'. rewrite EG' in IH'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in IH'.
      enter_with IH';
        [st_eq| split; [exact GF| exact GEND]| exact Elen| exact Elp| lia| lia| lia| lia| exact LJ1'| exact LJ2'| exact LJ3'| exact Ljc'
        | exact RFQ| exact SEL| exact SP1'| exact SP2'| exact SP3'| exact R896| exact R912| exact R936| exact R976| exact R1024| exact FAVE| exact COST| exact MI| exact MU| exact WM
        | exact VAR1| exact VLEN| exact VLPK| exact V40| exact V800| exact V808| exact V816| exact V824| exact V904| exact V920| exact V928| exact V944| exact V952
        | exact V992| exact V1000| exact V1008| exact V1016| exact V1032| exact K].
    - (* [comment removed for export] *)
      assert (Hj1 : (Z.of_nat (S j) = KSEL e)%Z) by (destruct (Z.eq_dec (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; nia]).
      assert (EEND : Gend e s = Gj e s (S j)) by (unfold Gend; f_equal; lia).
      pose proof (K m' J1' J2' J3' jc' (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (GE nMTF gs + 1))) as K'. rewrite EEND, EG' in K'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in K'.
      enter_with K';
        [st_eq| exact LJ1'| exact LJ2'| exact LJ3'| exact Ljc'| exact RFQ| exact SEL| exact SP1'| exact SP2'| exact SP3'| exact R896| exact R912| exact R936| exact R976| exact R1024| exact FAVE| exact COST| exact MI| exact MU| exact WM].
  Qed.
End GGU.
End ACeilS1.
