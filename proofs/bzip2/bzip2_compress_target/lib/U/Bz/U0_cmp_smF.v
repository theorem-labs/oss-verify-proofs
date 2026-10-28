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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCHuffF1. Import BzCHuffF1.BzCFactsHm.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut0 CmpSmKit2 CmpSmKit20 CmpHmKit U0_cmp_smB U0_cmp_smBb U0_cmp_smBz U0_sd4K U0_cmp_smP U0_cmp_smSu.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GFI.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv : word).
  Variables (cost0 fave0 heap0 weight0 parent0 : zarr) (lo SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CLO : (CEIL <= lo)%Z. Hypothesis STK : (lo + HM_FRAME <= SP)%Z. Hypothesis AL : (SP mod 16 = 0)%Z.
  Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Hypothesis FACTS : smB_facts e cost0 fave0 heap0 weight0 parent0.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation ITK k := (ITk e cost0 fave0 heap0 weight0 parent0 k).
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  Notation Wmk := [(E + 37708, E + 39256); (SP - 5328, SP)]%Z.

  (* [comment removed for export] *)
  Lemma HMKL : forall (n t : nat) (s : sits) (rfe : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall t', (Z.of_nat t' < nG)%Z ->
       hm_facts (ml_len e s t') rfe (258 * Z.of_nat t') (258 * Z.of_nat t') A /\
       ml_len e s (S t') =
         hs_len (hbMakeCodeLengths (ml_len e s t') rfe znew znew znew (258 * Z.of_nat t') (258 * Z.of_nat t') A 17)) ->
    (forall tt v, (0 <= tt < nG)%Z -> (0 <= v < A)%Z -> zdef rfe (258 * tt + v) = true /\ (0 <= zget rfe (258 * tt + v) <= nMTF)%Z) ->
    u8arr s0segs m (E + 37708) (ovb (ml_len e s t) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 45448) (ovw rfe (jseg J 45448 6192) 1548) ->
    cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo SP ->
    munch Wmk mf m -> wmono s0segs mf m ->
    frdW s0segs Wmk mf (SP + 888) [C8 (Z_to_bv 64 (1032 * nG))] -> frdW s0segs Wmk mf (SP + 944) [C8 (NOT (E + 45448))] ->
    frdW s0segs Wmk mf (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] -> frdW s0segs Wmk mf (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW s0segs Wmk mf (SP + 968) [C8 (Z_to_bv 64 A)] ->
    (forall m' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 : word),
      u8arr s0segs m' (E + 37708) (ovb (ml_len e s (t + n)) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 45448) (ovw rfe (jseg J 45448 6192) 1548) ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo SP ->
      munch Wmk mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 (258 * nG - 1548)) s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b3bc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (1032 * Z.of_nat t)) (Z_to_bv 64 (258 * Z.of_nat t - 1548)) s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b36c) fc None m (seg_rom s0segs)).
  Proof.
    intros n t s rfe m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 Hn Hn1 MLF RFF LEN RFQ CM MI ST MU WM V1 V2 V3 V4 V5 K.
    pose proof (proj1 FACTS) as H0. unfold smB_static in H0. cps_destruct H0 as (HA & HNG & HM & _ & _ & _ & _ & _ & _).
    assert (CEP : (CEIL <= SP)%Z) by (unfold CEIL, HM_FRAME in *; lia).
    eapply (U0_sm_mkl cx e Q gp tp F fc sv SP CX IMG CEP PHI HA HNG HM n t s rfe lo m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6);
      try eassumption.
    intros m' r0 r1 r2 r3 b0 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6. exact (K m' r0 r1 r2 r3 b0 b1 b2 b3 b4 b5 b6 b7 s7 s8 s10 s11 q3 q4 q5 q6).
  Qed.

  Ltac openF :=
    let H := fresh "ST0" in pose proof (proj1 FACTS) as H; unfold smB_static in H;
    cps_destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac cimgT CM MU WM :=
    let H := fresh "CMx" in
    pose proof (cimg_transportK0 S0C _ _ _ _ eq_refl CM MU WM
      ltac:(unfold w_img_apartK, U0_cmp_smBz.Wit, IMG_LO3; repeat (apply Forall_cons; [cbn [fst snd ci_hi S0C]; lia|]); apply Forall_nil)) as H;
    clear CM; rename H into CM.

  (* [comment removed for export] *)
  Definition Wf : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 37708, E + 39256); (E + 45448, E + 51640); (E + 51640, E + 55768); (SP - 5328, SP); (SP + 32, SP + 40); (SP + 48, SP + 528);
     (SP + 584, SP + 800); (SP + 832, SP + 888); (SP + 896, SP + 904); (SP + 912, SP + 928); (SP + 936, SP + 944); (SP + 976, SP + 984);
     (SP + 1024, SP + 1032); (SP + 1060, SP + 1096)]%Z.
  Ltac ro_of R := apply frdW_intro; [exact R| unfold U0_cmp_smBz.Wit; cbn [disjoint_from]; simpl_sizes; Lib.Step.slia].
  Ltac fside :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- frdW _ _ ?mm (SP + ?o)%Z _ => first [ lazymatch goal with R : rw_cells _ mm (SP + o)%Z _ |- _ => ro_of R end | idtac ]
    | |- (_ <= _)%nat => first [lia | idtac]
    | |- (_ < _)%nat => first [lia | idtac]
    | |- (_ <= _)%Z => first [lia | idtac]
    | |- (_ < _)%Z => first [lia | idtac]
    | |- (_ /\ _)%Z => first [lia | idtac]
    | |- (@eq Z _ _) => first [lia | idtac]
    | |- _ => idtac
    end ].
  Ltac show_left := lazymatch goal with |- evt _ _ _ => idtac | |- (MS _ _ _ _ _ _ _ = _) => idtac | |- ?G => idtac "LEFT:" G end.

  Lemma U0_sm_iterk : forall (k : nat) (J1 J2 J3 jc jf : list byte) (w896 w912 w920 w936 w976 w1024 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (k < 4)%nat -> length J1 = 480%nat -> length J2 = 216%nat -> length J3 = 56%nat -> length jc = 12%nat -> length jf = 24%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells s0segs m (SP + 32) [C8 (Z_to_bv 64 (Z.of_nat k))] ->
    u8arr s0segs m (SP + 48) J1 -> u8arr s0segs m (SP + 584) J2 -> u8arr s0segs m (SP + 832) J3 ->
    rw_cells s0segs m (SP + 896) [C8 w896] -> rw_cells s0segs m (SP + 912) [C8 w912] -> rw_cells s0segs m (SP + 920) [C8 w920] ->
    rw_cells s0segs m (SP + 936) [C8 w936] -> rw_cells s0segs m (SP + 976) [C8 w976] -> rw_cells s0segs m (SP + 1024) [C8 w1024] ->
    u8arr s0segs m (SP + 1060) jf -> u8arr s0segs m (SP + 1084) jc ->
    rw_cells s0segs m (SP + 24) [C8 (Z_to_bv 64 (flag6 nG))] -> rw_cells s0segs m (SP + 40) [C8 (Z_to_bv 64 (4 * A))] ->
    rw_cells s0segs m (SP + 528) [C8 (NOT (E + 38740))] -> rw_cells s0segs m (SP + 536) [C8 (NOT (E + 38998))] ->
    rw_cells s0segs m (SP + 544) [C8 (NOT (E + 38224))] -> rw_cells s0segs m (SP + 552) [C8 (NOT (E + 38482))] ->
    rw_cells s0segs m (SP + 560) [C8 (Z_to_bv 64 (E + 38998))] -> rw_cells s0segs m (SP + 568) [C8 (NOT (E + 51640))] ->
    rw_cells s0segs m (SP + 576) [C8 (NOT (E + 37966))] ->
    rw_cells s0segs m (SP + 800) [C8 (Z_to_bv 64 18002)] -> rw_cells s0segs m (SP + 808) [C8 (NOT (SP + 1060))] ->
    rw_cells s0segs m (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> rw_cells s0segs m (SP + 824) [C8 (NOT (E + 1704))] ->
    rw_cells s0segs m (SP + 888) [C8 (Z_to_bv 64 (1032 * nG))] ->
    rw_cells s0segs m (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> rw_cells s0segs m (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    rw_cells s0segs m (SP + 944) [C8 (NOT (E + 45448))] -> rw_cells s0segs m (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    rw_cells s0segs m (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] -> rw_cells s0segs m (SP + 968) [C8 (Z_to_bv 64 A)] ->
    rw_cells s0segs m (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> rw_cells s0segs m (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    rw_cells s0segs m (SP + 1008) [C8 (Z_to_bv 64 1)] -> rw_cells s0segs m (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    rw_cells s0segs m (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo SP ->
    munch Wf me m -> wmono s0segs me m ->
    (forall m' (J1' J2' J3' jc' jf' : list byte) (w896' w912' w936' w1024' : word) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' s8' s10' s11' t3' t4' t5' t6' : word),
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat -> length jc' = 12%nat -> length jf' = 24%nat ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb (it_len (ITK (S k))) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (it_lp (ITK (S k))) (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (it_rfreq (ITK (S k))) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (it_sel (ITK (S k))) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells s0segs m' (SP + 32) [C8 (Z_to_bv 64 (Z.of_nat k + 1))] ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      rw_cells s0segs m' (SP + 896) [C8 w896'] -> rw_cells s0segs m' (SP + 912) [C8 w912'] -> rw_cells s0segs m' (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
      rw_cells s0segs m' (SP + 936) [C8 w936'] -> rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (it_nSel (ITK (S k))))] -> rw_cells s0segs m' (SP + 1024) [C8 w1024'] ->
      u8arr s0segs m' (SP + 1060) jf' -> u8arr s0segs m' (SP + 1084) jc' ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo SP ->
      munch Wf me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIT ra' t0' t1' t2' (Z_to_bv 64 (Z.of_nat k + 1)) (Z_to_bv 64 4) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (SP + 1084)) s5' s7' s8' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 (if (Z.of_nat k + 1 =? 4)%Z then 0x1b434 else 0x1745c)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1745c) fc None m (seg_rom s0segs)).
  Proof.
    intros k J1 J2 J3 jc jf w896 w912 w920 w936 w976 w1024 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6
           Hk LJ1 LJ2 LJ3 Ljc Ljf AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 C896 C912 C920 C936 C976 C1024 FAV COST
           C24 C40 C528 C536 C544 C552 C560 C568 C576 C800 C808 C816 C824 C888 C904 C928 C944 C952 C960 C968 C992 C1000 C1008 C1016 C1032
           CM MI ST MU WM K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb. openF.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold CEIL, HM_FRAME in CLO, STK.
    assert (CEP : (CEIL <= SP)%Z) by (unfold CEIL; lia).
    assert (CE : (alloc_ceiling <= SP)%Z) by lia.
    pose proof SEP as SPx. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SPx. cbv zeta in SPx. destruct SPx as (AEA1 & _).
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3, ESTATE_SIZE in IMG'. cbn [ci_hi S0C] in IMG'. destruct IMG' as (IE & _).
    cps_destruct (proj2 FACTS k Hk) as (BL & BP & BG & BM).
    unfold Wf in MU.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_iterA with (cx := cx) (e := e) (g := g) (cost0 := cost0) (fave0 := fave0) (heap0 := heap0) (weight0 := weight0) (parent0 := parent0)
                       (SP := SP) (k := k) (J1 := J1) (J2 := J2) (J3 := J3) (jc := jc) (jf := jf)
                       (w896 := w896) (w912 := w912) (w920 := w920) (w936 := w936) (w976 := w976) (w1024 := w1024) (m := m) (me := m)].
    all: fside.
    { st_eq. }
    clear AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 C896 C912 C920 C936 C976 C1024 FAV COST MI.
    intros m5 J1' J2' J3' jc' w896' w936' w1024' ra' u0 u1 u2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 us7 us8 us10 us11 u3 u4 u5 u6. cbv zeta.
    intros LJ1' LJ2' LJ3' Ljc' AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 R896 R912 R920 R936 R976 R1024 FAVE COST MI MU5 WM5.
    unfold EHEAD2 in EH2. cimgT CM MU5 WM5. unfold U0_cmp_smBz.Wit in MU5. transport_after_call s0segs m m5 MU5 WM5. clear MU5 WM5.
    remember (ITK k) as s eqn:Es.
    cps_pose (proj1 BG (Z.to_nat (KSEL e)) ltac:(lia)) as GFE. cbv zeta in GFE. change (Gj e s (Z.to_nat (KSEL e))) with (Gend e s) in GFE.
    cps_destruct GFE as (Egs & EnS & Htc & RFF & FVB & SLF).
    assert (EgsN : g_gs (Gend e s) = nMTF) by (rewrite Egs; apply Z.min_r; lia).
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply (HMKL (Z.to_nat nG) 0%nat s (g_rfreq (Gend e s)) m5 m5)].
    all: fside.
    { st_eq. }
    { intros t' Ht'. cps_destruct (proj1 BM t' Ht') as (X1 & X2 & _). exact (conj X1 X2). }
    { intros tt v Htt Hv. destruct (RFF tt v Htt Hv) as [D R]. rewrite EgsN in R. exact (conj D R). }
    clear LEN RFQ CM MI ST. intros m6 wra w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws7 ws8 ws10 ws11 w3 w4 w5 w6 LEN RFQ CM MI ST MU6 WM6.
    transport_after_call s0segs m5 m6 MU6 WM6. clear MU6 WM6.
    (* [comment removed for export] *)
    destruct (MLt e s (Z.to_nat nG)) as [[[l' h'] w'] p'] eqn:EML.
    assert (EIT : ITK (S k) = SITS l' (g_rfreq (Gend e s)) (it_lpk e s) (g_sel (Gend e s)) (g_cost (Gend e s)) (g_fave (Gend e s)) (g_nSel (Gend e s)) h' w' p').
    { rewrite ITk_S, <- Es, (proj2 BM), EML. reflexivity. }
    rewrite EIT in K. cbn [it_len it_lp it_rfreq it_sel it_nSel] in K.
    unfold ml_len in LEN. replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LEN by lia. rewrite EML in LEN. cbn [fst] in LEN.
    apply (proj1 (u32arr_u8arr' s0segs m6 (SP + 1060) _)) in FAVE.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_itail with (cx := cx) (e := e) (SP := SP) (iter := (Z.of_nat k + 1)%Z) (m := m6)].
    all: fside.
    { st_eq. }
    - intros Hlt. replace (if (Z.of_nat k + 1 =? 4)%Z then 0x1b434%Z else 0x1745c%Z) with 0x1745c%Z in K
        by (replace (Z.of_nat k + 1 =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      enter_with (K m6 J1' J2' J3' jc' (u32s (zw32 (g_fave (Gend e s)) 6)) w896' _ w936' w1024');
        [st_eq| exact LJ1'| exact LJ2'| exact LJ3'| exact Ljc'| rewrite u32s_length, zw32_length_nat; reflexivity
        | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact C32| exact SP1| exact SP2| exact SP3
        | exact R896| exact R912| exact R920| exact R936| exact R976| exact R1024| exact FAVE| exact COST
        | exact CM| exact MI| exact ST| exact MU| exact WM].
    - intros Heq. replace (if (Z.of_nat k + 1 =? 4)%Z then 0x1b434%Z else 0x1745c%Z) with 0x1b434%Z in K
        by (replace (Z.of_nat k + 1 =? 4)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      enter_with (K m6 J1' J2' J3' jc' (u32s (zw32 (g_fave (Gend e s)) 6)) w896' _ w936' w1024');
        [st_eq| exact LJ1'| exact LJ2'| exact LJ3'| exact Ljc'| rewrite u32s_length, zw32_length_nat; reflexivity
        | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact C32| exact SP1| exact SP2| exact SP3
        | exact R896| exact R912| exact R920| exact R936| exact R976| exact R1024| exact FAVE| exact COST
        | exact CM| exact MI| exact ST| exact MU| exact WM].
  Qed.
  Lemma U0_sm_loop : forall (n k : nat) (J1 J2 J3 jc jf : list byte) (w896 w912 w920 w936 w976 w1024 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (k + n = 4)%nat -> (1 <= n)%nat -> length J1 = 480%nat -> length J2 = 216%nat -> length J3 = 56%nat -> length jc = 12%nat -> length jf = 24%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells s0segs m (SP + 32) [C8 (Z_to_bv 64 (Z.of_nat k))] ->
    u8arr s0segs m (SP + 48) J1 -> u8arr s0segs m (SP + 584) J2 -> u8arr s0segs m (SP + 832) J3 ->
    rw_cells s0segs m (SP + 896) [C8 w896] -> rw_cells s0segs m (SP + 912) [C8 w912] -> rw_cells s0segs m (SP + 920) [C8 w920] ->
    rw_cells s0segs m (SP + 936) [C8 w936] -> rw_cells s0segs m (SP + 976) [C8 w976] -> rw_cells s0segs m (SP + 1024) [C8 w1024] ->
    u8arr s0segs m (SP + 1060) jf -> u8arr s0segs m (SP + 1084) jc ->
    rw_cells s0segs m (SP + 24) [C8 (Z_to_bv 64 (flag6 nG))] -> rw_cells s0segs m (SP + 40) [C8 (Z_to_bv 64 (4 * A))] ->
    rw_cells s0segs m (SP + 528) [C8 (NOT (E + 38740))] -> rw_cells s0segs m (SP + 536) [C8 (NOT (E + 38998))] ->
    rw_cells s0segs m (SP + 544) [C8 (NOT (E + 38224))] -> rw_cells s0segs m (SP + 552) [C8 (NOT (E + 38482))] ->
    rw_cells s0segs m (SP + 560) [C8 (Z_to_bv 64 (E + 38998))] -> rw_cells s0segs m (SP + 568) [C8 (NOT (E + 51640))] ->
    rw_cells s0segs m (SP + 576) [C8 (NOT (E + 37966))] ->
    rw_cells s0segs m (SP + 800) [C8 (Z_to_bv 64 18002)] -> rw_cells s0segs m (SP + 808) [C8 (NOT (SP + 1060))] ->
    rw_cells s0segs m (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> rw_cells s0segs m (SP + 824) [C8 (NOT (E + 1704))] ->
    rw_cells s0segs m (SP + 888) [C8 (Z_to_bv 64 (1032 * nG))] ->
    rw_cells s0segs m (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> rw_cells s0segs m (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    rw_cells s0segs m (SP + 944) [C8 (NOT (E + 45448))] -> rw_cells s0segs m (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    rw_cells s0segs m (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] -> rw_cells s0segs m (SP + 968) [C8 (Z_to_bv 64 A)] ->
    rw_cells s0segs m (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> rw_cells s0segs m (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    rw_cells s0segs m (SP + 1008) [C8 (Z_to_bv 64 1)] -> rw_cells s0segs m (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    rw_cells s0segs m (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo SP ->
    munch Wf me m -> wmono s0segs me m ->
    (forall m' (J1' J2' J3' jc' jf' : list byte) (w896' w912' w936' w1024' : word) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' s8' s10' s11' t3' t4' t5' t6' : word),
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat -> length jc' = 12%nat -> length jf' = 24%nat ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb (it_len (ITK 4)) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (it_lp (ITK 4)) (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (it_rfreq (ITK 4)) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (it_sel (ITK 4)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells s0segs m' (SP + 32) [C8 (Z_to_bv 64 4)] ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      rw_cells s0segs m' (SP + 896) [C8 w896'] -> rw_cells s0segs m' (SP + 912) [C8 w912'] -> rw_cells s0segs m' (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
      rw_cells s0segs m' (SP + 936) [C8 w936'] -> rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (it_nSel (ITK 4)))] -> rw_cells s0segs m' (SP + 1024) [C8 w1024'] ->
      u8arr s0segs m' (SP + 1060) jf' -> u8arr s0segs m' (SP + 1084) jc' ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo SP ->
      munch Wf me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIT ra' t0' t1' t2' (Z_to_bv 64 4) (Z_to_bv 64 4) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (SP + 1084)) s5' s7' s8' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1b434) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1745c) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros k J1 J2 J3 jc jf w896 w912 w920 w936 w976 w1024 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6
           Hk Hn LJ1 LJ2 LJ3 Ljc Ljf AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 C896 C912 C920 C936 C976 C1024 FAV COST
           C24 C40 C528 C536 C544 C552 C560 C568 C576 C800 C808 C816 C824 C888 C904 C928 C944 C952 C960 C968 C992 C1000 C1008 C1016 C1032
           CM MI ST MU WM K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb.
    pose proof SEP as SPx. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SPx. cbv zeta in SPx. destruct SPx as (AEA1 & _).
    unfold CEIL, HM_FRAME in CLO, STK. unfold Wf in MU. unfold EHEAD2 in EH2.
    eapply (U0_sm_iterk k J1 J2 J3 jc jf w896 w912 w920 w936 w976 w1024 m m); try eassumption; [lia| apply munch_refl| apply wmono_refl|].
    clear AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 C896 C912 C920 C936 C976 C1024 FAV COST CM MI ST.
    intros m1 J1' J2' J3' jc' jf' w896' w912' w936' w1024' ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' s8' s10' s11' t3' t4' t5' t6'
           LJ1' LJ2' LJ3' Ljc' Ljf' AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 C896 C912 C920 C936 C976 C1024 FAV COST CM MI ST MU1 WM1.
    unfold Wf in MU1. unfold EHEAD2 in EH2. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    destruct n as [|n].
    - assert (k = 3)%nat by lia. subst k.
      replace (if (Z.of_nat 3 + 1 =? 4)%Z then 0x1b434%Z else 0x1745c%Z) with 0x1b434%Z by reflexivity.
      replace (Z.of_nat 3 + 1)%Z with 4%Z in * by lia.
      enter_with (K m1 J1' J2' J3' jc' jf' w896' w912' w936' w1024'); [st_eq| eassumption ..].
    - replace (if (Z.of_nat k + 1 =? 4)%Z then 0x1b434%Z else 0x1745c%Z) with 0x1745c%Z
        by (replace (Z.of_nat k + 1 =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) in * by lia.
      enter_with (IH (S k) J1' J2' J3' jc' jf' w896' w912' (Z_to_bv 64 nMTF) w936' (Z_to_bv 64 (it_nSel (ITK (S k)))) w1024' m1 me);
        [st_eq| lia| lia| eassumption ..].
  Qed.
End GFI.


(* [comment removed for export] *)
Definition U0_sm_front_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cx : cctx) (g : eg) (e : est) (lo : Z) (sv : word)
      (Q : machine_state -> Prop),
    let usp := bv_unsigned sp in let SP := (usp - 1200)%Z in
    let E := c_E cx in let A := sm_alpha e in let nG := smA_ng e in let nMTF := sm_nmtf e in
    a0 = Z_to_bv 64 E -> g_mtf g = true ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp ->
    (lo + 6528 <= usp)%Z -> (CEIL <= lo)%Z -> (usp mod 16 = 0)%Z ->
    cctx_ok cx -> cctx_sep cx -> cctx_img S0C cx ->
    smA_facts e -> smB_facts e znew znew znew znew znew ->
    (forall m' (J0 Jm J3 Jx J44 Jf : list byte) (w16 w896 w912 w936 w1024 : word)
            (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' : word),
       emem cx s0segs g (est_B e znew znew znew znew znew) m' -> amem cx s0segs e m' -> cimg_mem S0C m' sv ->
       mem_inv s0segs m' -> stk s0segs m' lo usp ->
       munch [(E, E + ESTATE_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (usp - 6528, usp)]%Z m m' -> wmono s0segs m m' ->
       length J0 = 16%nat -> length Jm = 792%nat -> length J3 = 56%nat -> length Jx = 4%nat -> length J44 = 16%nat -> length Jf = 36%nat ->
       u8arr s0segs m' SP J0 ->
       rw_cells s0segs m' (SP + 16) [C8 w16] ->
       u8arr s0segs m' (SP + 24) Jm ->
       rw_cells s0segs m' (SP + 816) [C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (E + 1704)))] ->
       u8arr s0segs m' (SP + 832) J3 ->
       rw_cells s0segs m' (SP + 888)
         [C8 (Z_to_bv 64 (1032 * nG)); C8 w896; C8 (Z_to_bv 64 (flag6 nG)); C8 w912; C8 (Z_to_bv 64 nMTF); C8 (Z_to_bv 64 nG); C8 w936;
          C8 (Z_to_bv 64 (18446744073709551615 - (E + 45448))); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 A);
          C8 (Z_to_bv 64 (smB_nsel e znew znew znew znew znew)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (E + 51640));
          C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 w1024; C8 (Z_to_bv 64 (c_A1 cx))] ->
       u8arr s0segs m' (SP + 1040) Jx -> u8arr s0segs m' (SP + 1044) J44 -> u8arr s0segs m' (SP + 1060) Jf ->
       rw_cells s0segs m' (SP + 1096) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       evt s0segs Q (MS (mkR ra' (Z_to_bv 64 SP) gp tp t0' t1' t2' (Z_to_bv 64 E) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                              s2' s3' s4' s5' s6' s7' s8' (Z_to_bv 64 (18446744073709551615 - (E + 37708))) s10' s11' t3' t4' t5' t6')
                        F (Z_to_bv 64 0x1b434) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16f4c) fc None m (seg_rom s0segs)).

Lemma u8arr_catF : forall segs (m : word -> option byte) A xs B ys,
  u8arr segs m A xs -> u8arr segs m B ys -> B = (A + Z.of_nat (length xs))%Z -> u8arr segs m A (xs ++ ys).
Proof. intros segs m A xs B ys H1 H2 ->. apply (proj2 (u8arr_app segs m A xs ys)). split; assumption. Qed.
Lemma rw_cells_catF : forall segs (m : word -> option byte) A cs1 B cs2,
  rw_cells segs m A cs1 -> rw_cells segs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A cs1 B cs2 H1 H2 ->. apply (proj2 (rw_cells_app2 segs m A cs1 cs2)). split; assumption. Qed.
Lemma u8arr_cellsF : forall segs (m : word -> option byte) A cs,
  rw_cells segs m A cs -> u8arr segs m A (cells_bytes cs) /\ length (cells_bytes cs) = cells_size cs.
Proof. intros. apply u8arr_of_cells. assumption. Qed.
Lemma u8arr_split3F : forall segs m A bs (i k : nat), (i + k <= length bs)%nat ->
  u8arr segs m A bs ->
  u8arr segs m A (firstn i bs) /\
  u8arr segs m (A + Z.of_nat i) (firstn k (skipn i bs)) /\
  u8arr segs m (A + Z.of_nat (i + k)) (skipn (i + k) bs) /\
  length (firstn i bs) = i /\ length (firstn k (skipn i bs)) = k /\ length (skipn (i + k) bs) = (length bs - (i + k))%nat /\
  bs = firstn i bs ++ firstn k (skipn i bs) ++ skipn (i + k) bs.
Proof.
  intros segs m A bs i k Hik H.
  cps_pose (proj1 (u8arr_window segs m A bs i k Hik) H) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [rewrite firstn_length_le; [reflexivity|lia]|].
  split; [rewrite firstn_length_le; [reflexivity|rewrite skipn_length; lia]|].
  split; [rewrite skipn_length; reflexivity|].
  rewrite <- (firstn_skipn i bs) at 1. f_equal.
  rewrite <- (firstn_skipn k (skipn i bs)) at 1. rewrite skipn_skipn, (Nat.add_comm k i). reflexivity.
Qed.

Ltac fs := first [ eassumption | apply munch_refl | apply wmono_refl
  | lazymatch goal with
    | |- frdW _ _ ?mm ?a [C8 _] => lazymatch goal with R : rw_cells _ mm a _ |- _ => apply frdW_intro; [exact R| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia] end
    | |- (_ <= _)%nat => lia | |- (_ < _)%nat => lia
    | |- (_ <= _)%Z => first [lia | unfold HM_FRAME; lia] | |- (_ < _)%Z => lia
    | |- (@eq nat _ _) => lia | |- (@eq Z _ _) => first [lia | idtac]
    end | idtac ].
Ltac lenZ := rewrite ?length_app; repeat (match goal with H : length ?l = _ |- context [length ?l] => rewrite H end); lia.
Ltac stkF ST H nxt :=
  let S := fresh "STp" in
  first [ pose proof (stk_of_u8arr _ _ _ _ H) as S | pose proof (stk_of_rw_cells _ _ _ _ H) as S ];
  lazymatch type of S with stk _ _ _ ?h => replace h with nxt in S by (cbn [cells_size csize]; lenZ) end;
  let T := fresh "STa" in
  pose proof (stk_merge _ _ _ _ _ ST S ltac:(lia)) as T; clear ST S; rename T into ST.
Ltac cimgF CM MU WM :=
  let H := fresh "CMx" in
  pose proof (cimg_transportK0 S0C _ _ _ _ eq_refl CM MU WM
    ltac:(unfold w_img_apartK, IMG_LO3; repeat (apply Forall_cons; [cbn [fst snd ci_hi S0C]; lia|]); apply Forall_nil)) as H;
  clear CM; rename H into CM.

Lemma U0_sm_front : U0_sm_front_spec.
Proof.
  unfold U0_sm_front_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e lo sv Q.
  cbv zeta. intros EA0 GM EM AM CM MI ST HLO CLO AL CX SEP IMG SFA SFB K.
  destruct (ex_intro (fun z => z = (bv_unsigned sp - 1200)%Z) _ eq_refl) as [SP ESP].
  assert (HSP : bv_unsigned sp = (SP + 1200)%Z) by lia. clear ESP.
  rewrite HSP in ST, HLO, AL, K. replace (SP + 1200 - 1200)%Z with SP in K by lia.
  rewrite <- (Z_to_bv_bv_unsigned sp), HSP. subst a0.
  pose proof ST as STx. destruct STx as (_ & PHI & _).
  assert (CEP : (CEIL <= SP)%Z) by lia.
  pose proof CX as CXL. bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL. cbv zeta in CXL.
  cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LJ & _).
  pose proof SEP as SPx. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SPx. cbv zeta in SPx. cps_destruct SPx as (AEA1 & AEA2 & AEF & _).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3, ESTATE_SIZE in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
  unfold CEIL in CEP, CLO.
  cps_destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). cps_destruct AM as (AR1 & AR2 & FTB).
  destruct (stk_carve s0segs m lo (SP + 1200) 1200 ST ltac:(lia)) as [STlo [junk FR]]. clear ST.
  replace (SP + 1200 - Z.of_nat 1200)%Z with SP in STlo, FR by lia.
  pose proof (u8arr_of_rw_cells s0segs m SP _ _ FR) as UF.
  assert (LJk : length junk = 1200%nat) by (destruct FR as [[[Hn _] _] _]; exact Hn).
  clear FR.
    destruct (u8arr_split3F s0segs m SP junk 0 16 ltac:(lia) UF) as (_ & PJ0 & _ & _ & LJ0 & _ & _).
    set (J0 := firstn 16 (skipn 0 junk)) in PJ0, LJ0.
    change (SP + Z.of_nat 0)%Z with (SP + 0)%Z in PJ0.
    destruct (u8arr_split3F s0segs m SP junk 48 480 ltac:(lia) UF) as (_ & PJ1 & _ & _ & LJ1 & _ & _).
    set (J1 := firstn 480 (skipn 48 junk)) in PJ1, LJ1.
    change (SP + Z.of_nat 48)%Z with (SP + 48)%Z in PJ1.
    destruct (u8arr_split3F s0segs m SP junk 584 216 ltac:(lia) UF) as (_ & PJ2 & _ & _ & LJ2 & _ & _).
    set (J2 := firstn 216 (skipn 584 junk)) in PJ2, LJ2.
    change (SP + Z.of_nat 584)%Z with (SP + 584)%Z in PJ2.
    destruct (u8arr_split3F s0segs m SP junk 832 56 ltac:(lia) UF) as (_ & PJ3 & _ & _ & LJ3 & _ & _).
    set (J3 := firstn 56 (skipn 832 junk)) in PJ3, LJ3.
    change (SP + Z.of_nat 832)%Z with (SP + 832)%Z in PJ3.
    destruct (u8arr_split3F s0segs m SP junk 1040 4 ltac:(lia) UF) as (_ & PJx & _ & _ & LJx & _ & _).
    set (Jx := firstn 4 (skipn 1040 junk)) in PJx, LJx.
    change (SP + Z.of_nat 1040)%Z with (SP + 1040)%Z in PJx.
    destruct (u8arr_split3F s0segs m SP junk 1044 16 ltac:(lia) UF) as (_ & PJ44 & _ & _ & LJ44 & _ & _).
    set (J44 := firstn 16 (skipn 1044 junk)) in PJ44, LJ44.
    change (SP + Z.of_nat 1044)%Z with (SP + 1044)%Z in PJ44.
    destruct (u8arr_split3F s0segs m SP junk 1060 24 ltac:(lia) UF) as (_ & Pjf & _ & _ & Ljf & _ & _).
    set (jf := firstn 24 (skipn 1060 junk)) in Pjf, Ljf.
    change (SP + Z.of_nat 1060)%Z with (SP + 1060)%Z in Pjf.
    destruct (u8arr_split3F s0segs m SP junk 1084 12 ltac:(lia) UF) as (_ & Pjc & _ & _ & Ljc & _ & _).
    set (jc := firstn 12 (skipn 1084 junk)) in Pjc, Ljc.
    change (SP + Z.of_nat 1084)%Z with (SP + 1084)%Z in Pjc.
    destruct (u8arr_split3F s0segs m SP junk 16 8 ltac:(lia) UF) as (_ & Q16 & _ & _ & LQ16 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q16 ltac:(rewrite LQ16; reflexivity)) as (w16 & C16). clear Q16 LQ16.
    cbn [map] in C16. change (SP + Z.of_nat 16)%Z with (SP + 16)%Z in C16.
    destruct (u8arr_split3F s0segs m SP junk 24 8 ltac:(lia) UF) as (_ & Q24 & _ & _ & LQ24 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q24 ltac:(rewrite LQ24; reflexivity)) as (w24 & C24). clear Q24 LQ24.
    cbn [map] in C24. change (SP + Z.of_nat 24)%Z with (SP + 24)%Z in C24.
    destruct (u8arr_split3F s0segs m SP junk 32 8 ltac:(lia) UF) as (_ & Q32 & _ & _ & LQ32 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q32 ltac:(rewrite LQ32; reflexivity)) as (w32 & C32). clear Q32 LQ32.
    cbn [map] in C32. change (SP + Z.of_nat 32)%Z with (SP + 32)%Z in C32.
    destruct (u8arr_split3F s0segs m SP junk 40 8 ltac:(lia) UF) as (_ & Q40 & _ & _ & LQ40 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q40 ltac:(rewrite LQ40; reflexivity)) as (w40 & C40). clear Q40 LQ40.
    cbn [map] in C40. change (SP + Z.of_nat 40)%Z with (SP + 40)%Z in C40.
    destruct (u8arr_split3F s0segs m SP junk 528 8 ltac:(lia) UF) as (_ & Q528 & _ & _ & LQ528 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q528 ltac:(rewrite LQ528; reflexivity)) as (w528 & C528). clear Q528 LQ528.
    cbn [map] in C528. change (SP + Z.of_nat 528)%Z with (SP + 528)%Z in C528.
    destruct (u8arr_split3F s0segs m SP junk 536 8 ltac:(lia) UF) as (_ & Q536 & _ & _ & LQ536 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q536 ltac:(rewrite LQ536; reflexivity)) as (w536 & C536). clear Q536 LQ536.
    cbn [map] in C536. change (SP + Z.of_nat 536)%Z with (SP + 536)%Z in C536.
    destruct (u8arr_split3F s0segs m SP junk 544 8 ltac:(lia) UF) as (_ & Q544 & _ & _ & LQ544 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q544 ltac:(rewrite LQ544; reflexivity)) as (w544 & C544). clear Q544 LQ544.
    cbn [map] in C544. change (SP + Z.of_nat 544)%Z with (SP + 544)%Z in C544.
    destruct (u8arr_split3F s0segs m SP junk 552 8 ltac:(lia) UF) as (_ & Q552 & _ & _ & LQ552 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q552 ltac:(rewrite LQ552; reflexivity)) as (w552 & C552). clear Q552 LQ552.
    cbn [map] in C552. change (SP + Z.of_nat 552)%Z with (SP + 552)%Z in C552.
    destruct (u8arr_split3F s0segs m SP junk 560 8 ltac:(lia) UF) as (_ & Q560 & _ & _ & LQ560 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q560 ltac:(rewrite LQ560; reflexivity)) as (w560 & C560). clear Q560 LQ560.
    cbn [map] in C560. change (SP + Z.of_nat 560)%Z with (SP + 560)%Z in C560.
    destruct (u8arr_split3F s0segs m SP junk 568 8 ltac:(lia) UF) as (_ & Q568 & _ & _ & LQ568 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q568 ltac:(rewrite LQ568; reflexivity)) as (w568 & C568). clear Q568 LQ568.
    cbn [map] in C568. change (SP + Z.of_nat 568)%Z with (SP + 568)%Z in C568.
    destruct (u8arr_split3F s0segs m SP junk 576 8 ltac:(lia) UF) as (_ & Q576 & _ & _ & LQ576 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q576 ltac:(rewrite LQ576; reflexivity)) as (w576 & C576). clear Q576 LQ576.
    cbn [map] in C576. change (SP + Z.of_nat 576)%Z with (SP + 576)%Z in C576.
    destruct (u8arr_split3F s0segs m SP junk 800 8 ltac:(lia) UF) as (_ & Q800 & _ & _ & LQ800 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q800 ltac:(rewrite LQ800; reflexivity)) as (w800 & C800). clear Q800 LQ800.
    cbn [map] in C800. change (SP + Z.of_nat 800)%Z with (SP + 800)%Z in C800.
    destruct (u8arr_split3F s0segs m SP junk 808 8 ltac:(lia) UF) as (_ & Q808 & _ & _ & LQ808 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q808 ltac:(rewrite LQ808; reflexivity)) as (w808 & C808). clear Q808 LQ808.
    cbn [map] in C808. change (SP + Z.of_nat 808)%Z with (SP + 808)%Z in C808.
    destruct (u8arr_split3F s0segs m SP junk 816 8 ltac:(lia) UF) as (_ & Q816 & _ & _ & LQ816 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q816 ltac:(rewrite LQ816; reflexivity)) as (w816 & C816). clear Q816 LQ816.
    cbn [map] in C816. change (SP + Z.of_nat 816)%Z with (SP + 816)%Z in C816.
    destruct (u8arr_split3F s0segs m SP junk 824 8 ltac:(lia) UF) as (_ & Q824 & _ & _ & LQ824 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q824 ltac:(rewrite LQ824; reflexivity)) as (w824 & C824). clear Q824 LQ824.
    cbn [map] in C824. change (SP + Z.of_nat 824)%Z with (SP + 824)%Z in C824.
    destruct (u8arr_split3F s0segs m SP junk 888 8 ltac:(lia) UF) as (_ & Q888 & _ & _ & LQ888 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q888 ltac:(rewrite LQ888; reflexivity)) as (w888 & C888). clear Q888 LQ888.
    cbn [map] in C888. change (SP + Z.of_nat 888)%Z with (SP + 888)%Z in C888.
    destruct (u8arr_split3F s0segs m SP junk 896 8 ltac:(lia) UF) as (_ & Q896 & _ & _ & LQ896 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q896 ltac:(rewrite LQ896; reflexivity)) as (w896 & C896). clear Q896 LQ896.
    cbn [map] in C896. change (SP + Z.of_nat 896)%Z with (SP + 896)%Z in C896.
    destruct (u8arr_split3F s0segs m SP junk 904 8 ltac:(lia) UF) as (_ & Q904 & _ & _ & LQ904 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q904 ltac:(rewrite LQ904; reflexivity)) as (w904 & C904). clear Q904 LQ904.
    cbn [map] in C904. change (SP + Z.of_nat 904)%Z with (SP + 904)%Z in C904.
    destruct (u8arr_split3F s0segs m SP junk 912 8 ltac:(lia) UF) as (_ & Q912 & _ & _ & LQ912 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q912 ltac:(rewrite LQ912; reflexivity)) as (w912 & C912). clear Q912 LQ912.
    cbn [map] in C912. change (SP + Z.of_nat 912)%Z with (SP + 912)%Z in C912.
    destruct (u8arr_split3F s0segs m SP junk 920 8 ltac:(lia) UF) as (_ & Q920 & _ & _ & LQ920 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q920 ltac:(rewrite LQ920; reflexivity)) as (w920 & C920). clear Q920 LQ920.
    cbn [map] in C920. change (SP + Z.of_nat 920)%Z with (SP + 920)%Z in C920.
    destruct (u8arr_split3F s0segs m SP junk 928 8 ltac:(lia) UF) as (_ & Q928 & _ & _ & LQ928 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q928 ltac:(rewrite LQ928; reflexivity)) as (w928 & C928). clear Q928 LQ928.
    cbn [map] in C928. change (SP + Z.of_nat 928)%Z with (SP + 928)%Z in C928.
    destruct (u8arr_split3F s0segs m SP junk 936 8 ltac:(lia) UF) as (_ & Q936 & _ & _ & LQ936 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q936 ltac:(rewrite LQ936; reflexivity)) as (w936 & C936). clear Q936 LQ936.
    cbn [map] in C936. change (SP + Z.of_nat 936)%Z with (SP + 936)%Z in C936.
    destruct (u8arr_split3F s0segs m SP junk 944 8 ltac:(lia) UF) as (_ & Q944 & _ & _ & LQ944 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q944 ltac:(rewrite LQ944; reflexivity)) as (w944 & C944). clear Q944 LQ944.
    cbn [map] in C944. change (SP + Z.of_nat 944)%Z with (SP + 944)%Z in C944.
    destruct (u8arr_split3F s0segs m SP junk 952 8 ltac:(lia) UF) as (_ & Q952 & _ & _ & LQ952 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q952 ltac:(rewrite LQ952; reflexivity)) as (w952 & C952). clear Q952 LQ952.
    cbn [map] in C952. change (SP + Z.of_nat 952)%Z with (SP + 952)%Z in C952.
    destruct (u8arr_split3F s0segs m SP junk 960 8 ltac:(lia) UF) as (_ & Q960 & _ & _ & LQ960 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q960 ltac:(rewrite LQ960; reflexivity)) as (w960 & C960). clear Q960 LQ960.
    cbn [map] in C960. change (SP + Z.of_nat 960)%Z with (SP + 960)%Z in C960.
    destruct (u8arr_split3F s0segs m SP junk 968 8 ltac:(lia) UF) as (_ & Q968 & _ & _ & LQ968 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q968 ltac:(rewrite LQ968; reflexivity)) as (w968 & C968). clear Q968 LQ968.
    cbn [map] in C968. change (SP + Z.of_nat 968)%Z with (SP + 968)%Z in C968.
    destruct (u8arr_split3F s0segs m SP junk 976 8 ltac:(lia) UF) as (_ & Q976 & _ & _ & LQ976 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q976 ltac:(rewrite LQ976; reflexivity)) as (w976 & C976). clear Q976 LQ976.
    cbn [map] in C976. change (SP + Z.of_nat 976)%Z with (SP + 976)%Z in C976.
    destruct (u8arr_split3F s0segs m SP junk 984 8 ltac:(lia) UF) as (_ & Q984 & _ & _ & LQ984 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q984 ltac:(rewrite LQ984; reflexivity)) as (w984 & C984). clear Q984 LQ984.
    cbn [map] in C984. change (SP + Z.of_nat 984)%Z with (SP + 984)%Z in C984.
    destruct (u8arr_split3F s0segs m SP junk 992 8 ltac:(lia) UF) as (_ & Q992 & _ & _ & LQ992 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q992 ltac:(rewrite LQ992; reflexivity)) as (w992 & C992). clear Q992 LQ992.
    cbn [map] in C992. change (SP + Z.of_nat 992)%Z with (SP + 992)%Z in C992.
    destruct (u8arr_split3F s0segs m SP junk 1000 8 ltac:(lia) UF) as (_ & Q1000 & _ & _ & LQ1000 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q1000 ltac:(rewrite LQ1000; reflexivity)) as (w1000 & C1000). clear Q1000 LQ1000.
    cbn [map] in C1000. change (SP + Z.of_nat 1000)%Z with (SP + 1000)%Z in C1000.
    destruct (u8arr_split3F s0segs m SP junk 1008 8 ltac:(lia) UF) as (_ & Q1008 & _ & _ & LQ1008 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q1008 ltac:(rewrite LQ1008; reflexivity)) as (w1008 & C1008). clear Q1008 LQ1008.
    cbn [map] in C1008. change (SP + Z.of_nat 1008)%Z with (SP + 1008)%Z in C1008.
    destruct (u8arr_split3F s0segs m SP junk 1016 8 ltac:(lia) UF) as (_ & Q1016 & _ & _ & LQ1016 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q1016 ltac:(rewrite LQ1016; reflexivity)) as (w1016 & C1016). clear Q1016 LQ1016.
    cbn [map] in C1016. change (SP + Z.of_nat 1016)%Z with (SP + 1016)%Z in C1016.
    destruct (u8arr_split3F s0segs m SP junk 1024 8 ltac:(lia) UF) as (_ & Q1024 & _ & _ & LQ1024 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q1024 ltac:(rewrite LQ1024; reflexivity)) as (w1024 & C1024). clear Q1024 LQ1024.
    cbn [map] in C1024. change (SP + Z.of_nat 1024)%Z with (SP + 1024)%Z in C1024.
    destruct (u8arr_split3F s0segs m SP junk 1032 8 ltac:(lia) UF) as (_ & Q1032 & _ & _ & LQ1032 & _ & _).
    destruct (u8arr_C8s 1 s0segs m _ _ Q1032 ltac:(rewrite LQ1032; reflexivity)) as (w1032 & C1032). clear Q1032 LQ1032.
    cbn [map] in C1032. change (SP + Z.of_nat 1032)%Z with (SP + 1032)%Z in C1032.
    destruct (u8arr_split3F s0segs m SP junk 1096 104 ltac:(lia) UF) as (_ & QS & _ & _ & LQS & _ & _).
    destruct (u8arr_C8s 13 s0segs m _ _ QS ltac:(rewrite LQS; reflexivity)) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & CSV). clear QS LQS.
    cbn [map] in CSV. change (SP + Z.of_nat 1096)%Z with (SP + 1096)%Z in CSV.
    clear UF.
  eapply evt_eq; [| eapply U0_smA_head with (cx := cx) (g := g) (e := e) (ra := ra) (gp := gp) (tp := tp) (F := F) (fc := fc) (SP := SP) (sv := sv) (me := m) (m := m)].
  all: try eassumption.
  1: st_eq.
  all: try (apply munch_refl || apply wmono_refl).
  intros m1 x0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs5 xs6 EH1' EH2' MTF' LEN' CM' H16 H904 H928 H960 H968 H984 H1000 H1008 H1016 H1032 HSV MI1 MU1 WM1.

  clear EH1 EH2 MTF LEN CM C16 C904 C928 C960 C968 C984 C1000 C1008 C1016 C1032 CSV MI.
  rename EH1' into EH1, EH2' into EH2, MTF' into MTF, LEN' into LEN, CM' into CM.
  unfold EHEAD1 in EH1. unfold FTAB_WORDS in AR2, FTB.
  transport_after_call s0segs m m1 MU1 WM1.
  assert (MUB : munch [(c_E cx, c_E cx + ESTATE_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (SP + 1200 - 6528, SP + 1200)]%Z m m1)
    by (eapply munch_weaken; [| exact MU1]; unfold sub_fp, ESTATE_SIZE; cbn [outside]; intros; Lib.Step.slia).
  unfold ESTATE_SIZE in MUB. clear MU1.
  pose proof SFA as SFL. unfold smA_facts in SFL. cbv zeta in SFL. cps_destruct SFL as (NI & NM & MFD & IPK & IPT).
  pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with (smA_ng e) in NGR.
  eapply evt_eq; [| eapply U0_smA_iloop with (cx := cx) (g := g) (e := e) (ra := ra) (gp := gp) (tp := tp) (F := F) (fc := fc) (SP := SP)
                       (n := Z.to_nat (smA_ng e)) (k := 0%nat) (me := m1) (m := m1)].
  1: st_eq.
  all: fs.
  all: try (change (ip_nPart (sip_k e 0)) with (smA_ng e); lia).
  intros m2 y0 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys4 ys5 ys6. cbv zeta. intros LEN2 MTF2 EH22 MI2 MU2 WM2.
  unfold EHEAD2 in EH22.
  clear LEN MTF EH2 MI1.
  cimgF CM MU2 WM2. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
  replace (0 + Z.to_nat (smA_ng e))%nat with (Z.to_nat (smA_ng e)) in LEN2 by lia. rewrite <- IPT in LEN2.
  change (sm_init_tables 8 (e_mtfFreq e) (smA_ng e) (sm_alpha e) (sip0 e)) with (smA_ip e) in LEN2.
  eapply evt_eq; [| eapply U0_smA_setup with (cx := cx) (e := e) (ra := ra) (gp := gp) (tp := tp) (F := F) (fc := fc) (SP := SP) (me := m2) (m := m2)].
  1: st_eq.
  all: fs.
  intros m3 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zs5 zs7 zs8 zs10 zs11 z3 z4 z5 z6
         S24 S32 S40 S528 S536 S544 S552 S560 S568 S576 S800 S808 S816 S824 S888 S944 S952 S992 S1000 S1008 S1016 MI3 MU3 WM3.
  clear C24 C32 C40 C528 C536 C544 C552 C560 C568 C576 C800 C808 C816 C824 C888 C944 C952 C992 H1000 H1008 H1016 MI2.
  cimgF CM MU3 WM3. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
  assert (AL' : (SP mod 16 = 0)%Z) by (rewrite <- (Z.mod_add SP 75 16) by lia; replace (SP + 75 * 16)%Z with (SP + 1200)%Z by lia; exact AL).
  eapply evt_eq; [| eapply U0_sm_loop with (cx := cx) (e := e) (g := g) (gp := gp) (tp := tp) (F := F) (fc := fc) (sv := sv)
                       (cost0 := znew) (fave0 := znew) (heap0 := znew) (weight0 := znew) (parent0 := znew) (lo := lo) (SP := SP)
                       (n := 4%nat) (k := 0%nat) (J1 := J1) (J2 := J2) (J3 := J3) (jc := jc) (jf := jf)
                       (w896 := w896) (w912 := w912) (w920 := w920) (w936 := w936) (w976 := w976) (w1024 := w1024) (m := m3) (me := m3)].
  1: st_eq.
  all: fs.
  intros m4 J1' J2' J3' jc' jf' w896' w912' w936' w1024' ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' s5' s7' s8' s10' s11' t3' t4' t5' t6'
         LJ1' LJ2' LJ3' Ljc' Ljf' AR14 LEN4 LPK4 RFQ4 SEL4 EH24 C324 SJ14 SJ24 SJ34 C8964 C9124 C9204 C9364 C9764 C10244 FAV4 COST4 CM4 MI4 ST4 MU4 WM4.
  clear AR1 LEN2 LPK RFQ SEL EH22 S32 PJ1 PJ2 PJ3 C896 C912 C920 C936 C976 C1024 Pjf Pjc CM MI3 STlo.
  pose proof MU4 as MU4u. unfold Wf in MU4u. transport_after_call s0segs m3 m4 MU4u WM4. clear MU4 MU4u WM4.
  pose proof (smB_it_eq e znew znew znew znew znew) as EIT.
  rewrite <- EIT in C9764.
  destruct (u8arr_cellsF _ _ _ _ S24) as [US24 LUS24]. cbn [cells_size csize] in LUS24. clear S24.
  destruct (u8arr_cellsF _ _ _ _ C324) as [UC324 LUC324]. cbn [cells_size csize] in LUC324. clear C324.
  destruct (u8arr_cellsF _ _ _ _ S40) as [US40 LUS40]. cbn [cells_size csize] in LUS40. clear S40.
  destruct (u8arr_cellsF _ _ _ _ S528) as [US528 LUS528]. cbn [cells_size csize] in LUS528. clear S528.
  destruct (u8arr_cellsF _ _ _ _ S536) as [US536 LUS536]. cbn [cells_size csize] in LUS536. clear S536.
  destruct (u8arr_cellsF _ _ _ _ S544) as [US544 LUS544]. cbn [cells_size csize] in LUS544. clear S544.
  destruct (u8arr_cellsF _ _ _ _ S552) as [US552 LUS552]. cbn [cells_size csize] in LUS552. clear S552.
  destruct (u8arr_cellsF _ _ _ _ S560) as [US560 LUS560]. cbn [cells_size csize] in LUS560. clear S560.
  destruct (u8arr_cellsF _ _ _ _ S568) as [US568 LUS568]. cbn [cells_size csize] in LUS568. clear S568.
  destruct (u8arr_cellsF _ _ _ _ S576) as [US576 LUS576]. cbn [cells_size csize] in LUS576. clear S576.
  destruct (u8arr_cellsF _ _ _ _ S800) as [US800 LUS800]. cbn [cells_size csize] in LUS800. clear S800.
  destruct (u8arr_cellsF _ _ _ _ S808) as [US808 LUS808]. cbn [cells_size csize] in LUS808. clear S808.
  pose proof US24 as UJm. clear US24.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm UC324 ltac:(lenZ)) as UJm2. clear UJm UC324. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US40 ltac:(lenZ)) as UJm2. clear UJm US40. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm SJ14 ltac:(lenZ)) as UJm2. clear UJm SJ14. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US528 ltac:(lenZ)) as UJm2. clear UJm US528. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US536 ltac:(lenZ)) as UJm2. clear UJm US536. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US544 ltac:(lenZ)) as UJm2. clear UJm US544. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US552 ltac:(lenZ)) as UJm2. clear UJm US552. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US560 ltac:(lenZ)) as UJm2. clear UJm US560. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US568 ltac:(lenZ)) as UJm2. clear UJm US568. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US576 ltac:(lenZ)) as UJm2. clear UJm US576. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm SJ24 ltac:(lenZ)) as UJm2. clear UJm SJ24. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US800 ltac:(lenZ)) as UJm2. clear UJm US800. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ UJm US808 ltac:(lenZ)) as UJm2. clear UJm US808. rename UJm2 into UJm.
  pose proof (u8arr_catF s0segs m4 _ _ _ _ FAV4 COST4 ltac:(lenZ)) as UJf. clear FAV4 COST4.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S816 S824 ltac:(cbn [cells_size csize]; lia)) as R816. cbn [app] in R816. clear S816 S824.
  pose proof H1032 as BLK. clear H1032.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ C10244 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK C10244. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S1016 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S1016. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S1008 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S1008. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S1000 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S1000. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S992 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S992. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ H984 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK H984. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ C9764 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK C9764. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ H968 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK H968. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ H960 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK H960. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S952 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S952. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S944 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S944. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ C9364 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK C9364. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ H928 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK H928. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ C9204 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK C9204. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ C9124 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK C9124. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ H904 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK H904. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ C8964 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK C8964. rename BLK2 into BLK.
  pose proof (rw_cells_catF s0segs m4 _ _ _ _ S888 BLK ltac:(cbn [cells_size csize]; lia)) as BLK2. cbn [app] in BLK2. clear BLK S888. rename BLK2 into BLK.
  pose proof ST4 as STF. replace (SP + 0)%Z with SP in PJ0 by lia.
  stkF STF PJ0 (SP + 16)%Z.
  stkF STF H16 (SP + 24)%Z.
  stkF STF UJm (SP + 816)%Z.
  stkF STF R816 (SP + 832)%Z.
  stkF STF SJ34 (SP + 888)%Z.
  stkF STF BLK (SP + 1040)%Z.
  stkF STF PJx (SP + 1044)%Z.
  stkF STF PJ44 (SP + 1060)%Z.
  stkF STF UJf (SP + 1096)%Z.
  stkF STF HSV (SP + 1200)%Z.
  lazymatch type of UJm with u8arr _ _ _ ?lm => lazymatch type of UJf with u8arr _ _ _ ?lf =>
    eapply (K m4 J0 lm J3' Jx J44 lf sv w896' w912' w936' w1024') end end.
  { unfold emem, est_B. rewrite EIT. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
    split; [unfold EHEAD1; exact EH1|]; split; [exact INU|]; split; [exact UNS|]; split; [exact EH24|]; split; [exact MTF2|];
    split; [exact SEL4|]; split; [exact SELM|]; split; [exact LEN4|]; split; [exact CODE|]; split; [exact RFQ4| exact LPK4]. }
  { split; [exact AR14|]; split; [exact AR2| exact FTB]. }
  all: first [ eassumption | lenZ ].
Qed.

End ACeilS1.
