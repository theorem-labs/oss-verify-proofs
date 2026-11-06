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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV B0_cmp_sdV B0_cmp_smV B0_cmp_smBc B0_cmp_smBa B0_cmp_smBb B0_cmp_smK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GZB.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis COL : (0 < CO)%Z. Hypothesis COH : (CO + 12 <= CEIL)%Z. Hypothesis FVL : (0 < FV)%Z. Hypothesis FVH : (FV + 24 <= CEIL)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.

  Notation ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) s4 (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
         (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
  Notation HIT v32 v48 v56 v88 v20 v28 :=
    (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
  Ltac openHI H := unfold sd_hi in H; cbv zeta in H; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in H.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wm := [(P + 32, P + 136)]%Z.
  Lemma B0_sm_mid : forall (iter : Z) (w64 w72 v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 : word),
    (0 <= iter < 4)%Z ->
    rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m (P + 32) (sd_loA cx FB SHF SHE w64 w72 (Z_to_bv 64 iter)) ->
    mem_inv b0segs m -> munch Wm mf m -> wmono b0segs mf m ->
    shzW b0segs Wm mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wm mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' (a0 a1 a2 a3 : word),
      rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells b0segs m' (P + 32) (sd_loA cx FB SHF SHE w64 w72 (Z_to_bv 64 (iter + 1))) ->
      mem_inv b0segs m' -> munch Wm mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1548)) (Z_to_bv 64 0) t3 t4)
                       F (Z_to_bv 64 0x9399c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4)
                     F (Z_to_bv 64 0x9394c) fc None m (seg_rom b0segs)).
  Proof.
    intros iter w64 w72 v32 v48 v56 v88 v20 v28 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 HIT EH2 LOW MI MU WM SHe VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold sd_loA in LOW. cbv zeta in LOW. unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. wstep. clear RO. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    brun_to 0x93984%Z.
    wstep; if_cases Kv; zify_cond_z Kv; [exfalso; revert Kv; rewrite ?signed_lit by lia; lia|].
    (* [comment removed for export] *)
    wstep. wstep. wstep. try rewrite (sx32_of_Z (iter + 1)) by lia. wstep; lit_store. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _); [st_eq| unfold EHEAD2; rewrite GM; assumption| unfold sd_loA; cbv zeta; assumption| assumption| assumption| assumption] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_itail : forall (iter : Z) (w72 : word) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 : word),
    (1 <= iter <= 4)%Z ->
    rw_cells b0segs m (P + 32) (sd_loA cx FB SHF SHE (Z_to_bv 64 (FV + 24)) w72 (Z_to_bv 64 iter)) ->
    ((iter < 4)%Z ->
      evt b0segs Q (MS (ITR ra t0 t1 t2 (Z_to_bv 64 iter) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FV + 24)) s10 t3 t4)
                       F (Z_to_bv 64 0x8c480) fc None m (seg_rom b0segs))) ->
    ((iter = 4)%Z ->
      evt b0segs Q (MS (ITR ra t0 t1 t2 (Z_to_bv 64 iter) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FV + 24)) s10 t3 t4)
                       F (Z_to_bv 64 0x93afc) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4)
                     F (Z_to_bv 64 0x939fc) fc None m (seg_rom b0segs)).
  Proof.
    intros iter w72 m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 HIT LOW KN KX.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    unfold sd_loA in LOW. cbv zeta in LOW.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases Kx; zify_cond_z Kx.
    - enter_with (KX ltac:(lia)); [st_eq].
    - wstep. enter_with (KN ltac:(lia)); [st_eq].
  Qed.
End GZB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GZI.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (cost0 fave0 heap0 weight0 parent0 : zarr).
  Variables (P SHE FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z.
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 20 <= SH_HI)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE. Hypothesis AF : sanchor FB SHF.
  (* [comment removed for export] *)
  Hypothesis SEFB : id ((c_E cx + 55768 <= FB)%Z \/ (FB + 160 <= c_E cx)%Z).
  Hypothesis SA1FB : id ((c_A1 cx + ARR1_SIZE <= FB)%Z \/ (FB + 160 <= c_A1 cx)%Z).
  Hypothesis SESH : id ((c_E cx + 55768 <= SHF)%Z \/ (SHF + 20 <= c_E cx)%Z).
  Hypothesis SA1SH : id ((c_A1 cx + ARR1_SIZE <= SHF)%Z \/ (SHF + 20 <= c_A1 cx)%Z).
  Hypothesis SFSH : id ((FB + 160 <= SHF)%Z \/ (SHF + 20 <= FB)%Z).
  Hypothesis SPSH : id ((SHF + 20 <= P)%Z \/ (P + 1712 <= SHF)%Z).
  (* [comment removed for export] *)
  Hypothesis OFFE : id ((c_E cx + 55768 <= SH_LO)%Z \/ (SH_HI <= c_E cx)%Z).
  Hypothesis OFFF : id ((FB + 160 <= SH_LO)%Z \/ (SH_HI <= FB)%Z).
  Hypothesis OFFP : (SH_HI <= P)%Z.
  Hypothesis FACTS : smB_facts e cost0 fave0 heap0 weight0 parent0.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation CO := (FB + 32)%Z. Notation FV := (FB + 64)%Z.
  Notation ITK k := (ITk e cost0 fave0 heap0 weight0 parent0 k).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openF :=
    let H := fresh "ST0" in pose proof (proj1 FACTS) as H; unfold smB_static in H;
    cps_destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)

  Notation ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) s4 (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
         (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
  Notation HIT v32 v48 v56 v88 v20 v28 :=
    (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
  Notation LOWk w104 := (sd_loA cx FB SHF SHE (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 (flag6 nG)) w104).

  (* [comment removed for export] *)
  Lemma fave_reader : forall (W : list (Z * Z)) (m : word -> option byte),
    rw_cells b0segs m SHF sm_shadow -> app_fp W -> shzW b0segs W m FV (FV + 24).
  Proof.
    intros W m SHD AW. pose proof AF as [AF1 AF2]. bz_ceil. pose proof FBH as FBH'. unfold CEIL in FBH'.
    destruct (rw_cells_cutS b0segs m SHF sm_shadow 8%nat SHD) as [_ T]. cbn [firstn skipn cells_size csize Nat.add sm_shadow] in T.
    destruct (rw_cells_cutS b0segs m _ _ 3%nat T) as [T3 _]. cbn [firstn skipn] in T3.
    assert (B : bytes_at b0segs m (shad FV) (ushadow 24)).
    { unfold shad, SHB. rewrite (sanchor_addr_lit FB SHF 64 8 AF eq_refl). destruct T3 as [[_ B] _]. cbn [cells_bytes cbytes app] in B. exact B. }
    replace (FV + 24)%Z with (FV + 8 * (24 / 8))%Z by (change (24 / 8)%Z with 3%Z; lia).
    refine (proj1 (sh_of_ushadow b0segs W m FV 24 B _ ltac:(lia) ltac:(lia) _ AW)).
    - clear - AF1. Z.div_mod_to_equations. lia.
    - change (2^47)%Z with 140737488355328%Z. lia.
  Qed.
  Lemma cost_reader : forall (W : list (Z * Z)) (m : word -> option byte),
    rw_cells b0segs m SHF sm_shadow -> app_fp W -> shpW b0segs W m CO (CO + 12).
  Proof.
    intros W m SHD AW. pose proof AF as [AF1 AF2]. bz_ceil. pose proof FBH as FBH'. unfold CEIL in FBH'.
    destruct (rw_cells_cutS b0segs m SHF sm_shadow 4%nat SHD) as [_ T]. cbn [firstn skipn cells_size csize Nat.add sm_shadow] in T.
    destruct (rw_cells_cutS b0segs m _ _ 2%nat T) as [T2 _]. cbn [firstn skipn] in T2.
    assert (B : bytes_at b0segs m (shad CO) (ushadow 12)).
    { unfold shad, SHB. rewrite (sanchor_addr_lit FB SHF 32 4 AF eq_refl). destruct T2 as [[_ B] _]. cbn [cells_bytes cbytes app] in B. exact B. }
    refine (proj2 (sh_of_ushadow b0segs W m CO 12 B _ ltac:(lia) ltac:(lia) _ AW)).
    - clear - AF1. Z.div_mod_to_equations. lia.
    - change (2^47)%Z with 140737488355328%Z. lia.
  Qed.
  Lemma app_fp_Wg : app_fp (B0_cmp_smBb.Wg cx P CO FV).
  Proof.
    pose proof OFFE as O1. pose proof OFFF as O2. unfold id in O1, O2. pose proof OFFP as O3. unfold B0_cmp_smBb.Wg. cbn [app_fp]. unfold SH_LO, SH_HI in *. repeat split; lia.
  Qed.

  Local Ltac simpl_sizes ::=
    rewrite ?length_app;
    cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ EHEAD2 sd_hi sd_loA sm_set sm_shadow];
    rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length].
  (* [comment removed for export] *)
  Definition Wit : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 45448, E + 51640); (E + 51640, E + 55768); (P + 32, P + 136); (P + 136, P + 1264); (P + 1384, P + 1568); (FV, FV + 24); (CO, CO + 12)]%Z.
  Ltac hidisj := cbn [disjoint_from]; unfold sd_hi, sd_loA, sm_set; cbv zeta; simpl_sizes; Lib.Step.slia.
  Ltac vdisj := cbn [disjoint_from]; rewrite ?ovw_length_nat, ?ovb_length_nat, ?zw32_length_nat, ?zb8_length_nat; rewrite ?Z2Nat.id by (bz_params; lia); Lib.Step.slia.
  Ltac boxed H := let X := fresh "X_" in pose proof H as X; unfold id in X |- *; clear - X; lia.
  (* [comment removed for export] *)
  Ltac iside MU AR1 LEN LPK LOW SETc HI SHa SHe :=
    first [ eassumption |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ A1 _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply (u8arr_munch b0segs _ _ m_ _ _ AR1 MU_); unfold B0_cmp_smBb.Wg; vdisj
    | |- forall _, munch _ _ _ -> u8arr _ _ (E + 37708)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply (u8arr_munch b0segs _ _ m_ _ _ LEN MU_); unfold B0_cmp_smBb.Wg; vdisj
    | |- forall _, munch _ _ _ -> u32arr _ _ (E + 51640)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply (u32arr_munch b0segs _ _ m_ _ _ LPK MU_); unfold B0_cmp_smBb.Wg; vdisj
    | |- shzW _ _ _ A1 _ => eapply (shzW_sub b0segs Wit); [exact SHa| exact MU| unfold Wit, B0_cmp_smBb.Wg; a_sub_fp| lia| lia]
    | |- shzW _ _ _ E _ => eapply (shzW_sub b0segs Wit); [exact SHe| exact MU| unfold Wit, B0_cmp_smBb.Wg; a_sub_fp| lia| lia]
    | |- frdW _ _ _ (P + 1264)%Z _ => apply frdW_intro; [exact SETc| unfold B0_cmp_smBb.Wg; hidisj]
    | |- frdW _ _ _ (P + 1384)%Z _ => apply frdW_intro; [exact HI| unfold B0_cmp_smBb.Wg; hidisj]
    | |- frdW _ _ _ (P + ?o)%Z _ =>
        let k := eval vm_compute in (Z.to_nat (o - 32)) in
        eapply (frdW_cell_at b0segs _ _ (P + 32)%Z _ k); [apply frdW_intro; [exact LOW| unfold B0_cmp_smBb.Wg; hidisj]| reflexivity| lia]
    | |- id (_ \/ _) => first [ boxed SEFB | boxed SA1FB | unfold id; lia ]
    | |- (_ <= _)%nat => first [lia | idtac]
    | |- (_ < _)%nat => first [lia | idtac]
    | |- (_ <= _)%Z => first [lia | idtac]
    | |- (_ < _)%Z => first [lia | idtac]
    | |- (_ /\ _) => first [lia | idtac]
    | |- (_ \/ _) => first [lia | idtac]
    | |- (@eq Z _ _) => first [lia | idtac]
    | |- _ => idtac
    end ].

  Lemma B0_sm_iterA : forall (k : nat) (Jsp jc jf : list byte) (v32 v48 v56 v88 v20 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    (k < 4)%nat -> length Jsp = 1128%nat -> length jc = 12%nat -> length jf = 24%nat ->
    u8arr b0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr b0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr b0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr b0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m (P + 32) (LOWk (Z_to_bv 64 (Z.of_nat k))) ->
    u8arr b0segs m (P + 136) Jsp ->
    rw_cells b0segs m (P + 1264) (sm_set cx FV) ->
    rw_cells b0segs m (P + 1384) (HIT v32 v48 v56 v88 v20 (Z_to_bv 64 (E + 37708))) ->
    u8arr b0segs m FV jf -> u8arr b0segs m CO jc ->
    rw_cells b0segs m SHF sm_shadow ->
    mem_inv b0segs m -> munch Wit me m -> wmono b0segs me m ->
    shzW b0segs Wit me A1 (A1 + ARR1_SIZE) -> shzW b0segs Wit me E (E + ESTATE_SIZE) ->
    (forall m' (Jsp' jc' : list byte) (v32' v88' : word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' : word),
      let s := ITK k in
      length Jsp' = 1128%nat -> length jc' = 12%nat ->
      u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr b0segs m' (E + 37708) (ovb (it_len s) (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 51640) (ovw (it_lpk e s) (jseg J 51640 4128) 1032) ->
      u32arr b0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr b0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells b0segs m' (P + 32) (LOWk (Z_to_bv 64 (Z.of_nat k + 1))) ->
      u8arr b0segs m' (P + 136) Jsp' ->
      rw_cells b0segs m' (P + 1264) (sm_set cx FV) ->
      rw_cells b0segs m' (P + 1384) (HIT v32' (Z_to_bv 64 (g_totc (Gend e s))) (Z_to_bv 64 nMTF) v88' (Z_to_bv 64 (g_nSel (Gend e s))) (Z_to_bv 64 (E + 37708))) ->
      u32arr b0segs m' FV (zw32 (g_fave (Gend e s)) 6) -> u8arr b0segs m' CO jc' ->
      rw_cells b0segs m' SHF sm_shadow ->
      mem_inv b0segs m' -> munch Wit me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (ITR ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1548)) (Z_to_bv 64 0) t3' t4')
                       F (Z_to_bv 64 0x9399c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FB + 88)) s10 t3 t4)
                     F (Z_to_bv 64 0x8c480) fc None m (seg_rom b0segs)).
  Proof.
    intros k Jsp jc jf v32 v48 v56 v88 v20 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4
           Hk LJsp Ljc Ljf AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAV COST SHD MI MU WM SHa SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openF.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. pose proof FBH as FBH'. unfold CEIL in CEP', FBH'. pose proof SHL as SHL'. pose proof SHH as SHH'. unfold SH_LO, SH_HI in SHL', SHH'.
    pose proof SEP as SP. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP. cbv zeta in SP. destruct SP as (AEA1 & _).
    assert (HIT4 : (0 <= Z.of_nat k < 4)%Z) by lia.
    cps_destruct (proj2 FACTS k Hk) as (BL & BP & BG & BM).
    cbv zeta in K. remember (ITK k) as s eqn:Es.
    unfold Wit in MU.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply B0_sm_ihead with (f := it_fave s) (jf := jf) (mf := m) (P := P) (CO := CO) (FV := FV)].
    all: iside MU AR1 LEN LPK LOW SETc HI SHa SHe.
    { st_eq. }
    clear FAV MI. intros m1 FAVE MI MU1 WM1.
    transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply B0_sm_rfzo with (n := Z.to_nat nG) (t := 0%Z) (rf := it_rfreq s) (mf := m1) (P := P) (CO := CO) (FV := FV)].
    all: iside MU AR1 LEN LPK LOW SETc HI SHa SHe.
    { st_eq. }
    clear RFQ MI. intros m2 ya0 ya4 ya5 ya6 RFQ MI MU2 WM2.
    transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0) with (it_rf0 e s) in RFQ.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply B0_sm_pre1 with (lp := it_lp s) (len := it_len s) (mf := m2) (P := P) (CO := CO) (FV := FV)].
    all: iside MU AR1 LEN LPK LOW SETc HI SHa SHe.
    { st_eq. }
    clear LEN LPK MI. intros m3 za0 za1 za2 za3 za4 za5 za6 za7 LEN LPK MI MU3 WM3.
    transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
    change (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) (it_lp s) (it_len s) 0 else it_lp s) with (it_lpk e s) in LPK.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply B0_sm_pre2 with (mf := m3) (g := g) (P := P) (SHE := SHE) (CO := CO) (FV := FV)].
    all: iside MU AR1 LEN LPK LOW SETc HI SHa SHe.
    { st_eq. }
    clear EH2 HI MI. intros m4 EH2 HI MI MU4 WM4.
    transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    assert (LPF : nG = 6%Z -> forall v j, (0 <= v < A)%Z -> (0 <= j < 3)%Z -> zdef (it_lpk e s) (4 * v + j) = true /\ (0 <= zget (it_lpk e s) (4 * v + j) < 2097152)%Z).
    { intros H6 v j Hv Hj. cps_destruct (BP H6 v j Hv Hj) as (D & _ & R). exact (conj D R). }
    pose proof (fave_reader (B0_cmp_smBb.Wg cx P CO FV) m4 SHD app_fp_Wg) as SHf.
    pose proof (cost_reader (B0_cmp_smBb.Wg cx P CO FV) m4 SHD app_fp_Wg) as SHc.
    eapply evt_eq; [| eapply B0_sm_gloop with (n := Z.to_nat (KSEL e)) (j := 0%nat) (s := s) (Jsp := Jsp) (jc := jc) (lp := it_lpk e s) (len := it_len s) (me := m4)
                                             (P := P) (CO := CO) (FV := FV)].
    all: iside MU AR1 LEN LPK LOW SETc HI SHa SHe.
    { st_eq. }
    all: try reflexivity.
    clear RFQ SEL SPL HI FAVE COST MI.
    intros m5 Jsp' jc' v32' v88' u0 u1 u2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 us10 u3 u4 LJsp' Ljc' RFQ SEL SPL HI FAVE COST MI MU5 WM5.
    unfold B0_cmp_smBb.Wg in MU5. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply B0_sm_mid with (iter := Z.of_nat k) (mf := m5) (g := g) (P := P) (SHE := SHE) (CO := CO) (FV := FV) (FB := FB) (SHF := SHF)].
    all: iside MU AR1 LEN LPK LOW SETc HI SHa SHe.
    { st_eq. }
    clear EH2 LOW MI. intros m6 va0 va1 va2 va3 EH2 LOW MI MU6 WM6.
    transport_after_call b0segs m5 m6 MU6 WM6. clear MU6 WM6.
    enter_with (K m6 Jsp' jc' v32' v88' _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact LJsp'| exact Ljc'| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact LOW| exact SPL| exact SETc| exact HI| exact FAVE| exact COST| exact SHD| exact MI| exact MU| exact WM].
  Qed.
End GZI.
End ACeilS1.
