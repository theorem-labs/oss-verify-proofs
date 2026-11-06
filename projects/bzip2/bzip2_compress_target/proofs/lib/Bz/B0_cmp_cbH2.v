(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 DecTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut BzCNumZ CmpLaws CmpCutCB CmpCutCBw CmpArith CmpArith2 CmpSdTac BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT BzWalkArith4 CmpCutBsw CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV CmpSmKit CmpHmKit B0_cmp_cbV B0_cmp_cbWc.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Section B0CBH2.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation n := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis Hnb : (0 <= n)%Z.
  (* [comment removed for export] *)
  Definition g3 : eg := EG (g_aie g) (g_sort g) (g_mtf g) true (Z_to_bv 64 (A2 + n)).
  (* [comment removed for export] *)
  Definition cbH_W : list (Z * Z) := [(E + 80, E + 88); (E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P - 48, P + 184)]%Z.

  (* [comment removed for export] *)
  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         cSB s3 s4 (Z_to_bv 64 FB) s6 s7 (Z_to_bv 64 FB) s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6).
  Notation sl2 sl := (bset56 (bset64 (bset40 sl (Z_to_bv 64 (E + 652))) (Z_to_bv 64 (E + 80))) (Z_to_bv 64 (SHE + 10))).
  Notation bswcall := (B0_bsw8_call X Y g3 e Q XOK YOK eq_refl eq_refl Hnb).

  Ltac csh_sub MU :=
    let CSH := ident:(CSH) in
    lazymatch type of MU with munch _ ?m0 ?mc => eapply (cctx_sh_sub b0segs cx cbH_W _ m0 mc CSH MU); unfold cbH_W, cbW_W; a_sub_fp end.
  Ltac after_call8 mprev mnew :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let AR2 := ident:(AR2) in let MI := ident:(MI) in let ST := ident:(ST) in
    let MUc := ident:(MUc) in let WMc := ident:(WMc) in
    intros mnew ?t0 ?t1 ?t2 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?t3 ?t4 ?t5 ?t6; cbv zeta; intros EH1 EH2 AR2 MI ST MUc WMc;
    unfold cbW_W in MUc; transport_after_call b0segs mprev mnew MUc WMc; clear MUc WMc.
  Ltac retpc rp := replace (ret_pc (Z_to_bv 64 rp)) with (Z_to_bv 64 rp) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  Lemma B0_cb_H2 : forall (m : word -> option byte) (sl : cbslB)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 s4 s7 t3 t4 t5 t6 : word),
    bw_numZ (e_bw e) = 0%Z -> (1 <= e_blockNo e < 2147483647)%Z -> (e_blockNo e = 1%Z \/ (g_bs g = true /\ bw_ok (e_bw e))) ->
    (n <= (NBLOCKMAX + 19))%Z ->
    q88 sl = Z_to_bv 64 E -> q144 sl = Z_to_bv 64 (SHE + 13) ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) -> u8arr b0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    rw_cells b0segs m P (cbslB_cells sl) -> mem_inv b0segs m -> stk b0segs m lo P ->
    acoW cbH_W m -> cctx_sh b0segs cx cbH_W m ->
    (forall (m' : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word),
      let bS := cb_hdr e in
      rw_cells b0segs m' E (EHEAD1 cx g3 (est_set_bw e bS)) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g3 (est_set_bw e bS)) ->
      u8arr b0segs m' A2 (zb8 (zbl (e_arr2 e) n bS) ARR2_SIZE) ->
      rw_cells b0segs m' P (cbslB_cells (sl2 sl)) -> mem_inv b0segs m' -> stk b0segs m' lo P -> munch cbH_W m m' -> wmono b0segs m m' ->
      bw_ok bS -> (bw_numZ bS <= 16)%Z ->
      evt b0segs Q (MS (RW ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13)) (il_w (ce_il X)) s4 (Z_to_bv 64 (E + 108)) s7
                           (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x89d5c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13)) (il_w (ce_il X)) s4 (Z_to_bv 64 (E + 108)) s7
                         (Z_to_bv 64 (E + 660)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x89c20) fc None m (seg_rom b0segs)).
  Proof.
    intros m sl ra t0 t1 t2 a0 a1 a2 a3 a4 a5 s4 s7 t3 t4 t5 t6 NZ BN ALT NB H88 H144 EH1 EH2 AR2 SL MI ST ACW CSH K.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _); box_ors.
    pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2. pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl cbH_W m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof CSH as CSH'. destruct CSH' as (SHe & _ & SH2 & _). unfold cbH_W, ESTATE_SIZE in MU, SHe, SH2.
    unfold EHEAD1 in EH1. cbn_est_in EH1. unfold EHEAD2 in EH2. cbn_est_in EH2. rewrite NZ in EH1.
    unfold cbslB_cells in SL. rewrite H88, H144 in SL.
    rename m into m0. bz_params.
    (* [comment removed for export] *)
    brun_to 0x89c84%Z. sh_norm.
    (* [comment removed for export] *)
    brun_to 0x89c90%Z. wstep. wstep. brun_to 0x89cbc%Z. wstep. wstep.
    try rewrite (sx32_of_Z n) by lia. try rewrite (sx32_of_Z (e_blockNo e)) by lia.
    try (replace (n + A2)%Z with (A2 + n)%Z in EH1 by lia).
    (* [comment removed for export] *)
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      destruct ALT as [A1e|[Gbs OKb]]; [exfalso; lia|]. rewrite Gbs in EH2.
      pose proof (proj2 (cb_hdr_cases e) ltac:(lia)) as HB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end; cbv zeta; rewrite ?HB;
        [ st_eq
        | unfold EHEAD1, g3; cbn_est; rewrite NZ; exact EH1
        | unfold EHEAD2, g3; cbn_est; exact EH2
        | rewrite zbl_numZ0 by exact NZ; exact AR2
        | slB_cbn; rewrite ?H88, ?H144; exact SL| exact MI| exact ST| unfold cbH_W; exact MU| exact WM| exact OKb| lia].
    - (* [comment removed for export] *)
      assert (B1 : e_blockNo e = 1%Z) by lia. try clear Kb.
      (* [comment removed for export] *)
      brun_to 0x89cdc%Z. wstep; lit_store. brun_to 0x89cf4%Z. wstep; lit_store.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      set (Bz0 := BW 0 0 0 (bw_zb (e_bw e))).
      assert (OK0 : bw_ok Bz0) by (unfold bw_ok, Bz0; cbn; lia).
      assert (EH1b0 : EH1b X g3 e m1 Bz0) by (unfold EH1b, EHEAD1, g3, Bz0; cbn_est; exact EH1). clear EH1.
      assert (EH2b0 : EH2b X g3 e m1 Bz0) by (unfold EH2b, EHEAD2, g3, Bz0; cbn_est; exact EH2). clear EH2.
      assert (AR2b0 : AR2b X e m1 Bz0) by (unfold AR2b; rewrite zbl_numZ0 by reflexivity; exact AR2). clear AR2.
      pose proof (proj1 (cb_hdr_cases e) B1) as HB. rewrite NZ in HB. fold Bz0 in HB. rewrite HB, bz_hdr4_eq in K.
      pose proof (Z.le_refl (bw_numZ Bz0)) as NZ0. cbn [Bz0 bw_numZ] in NZ0.
      (* [comment removed for export] *)
      brun_to 0x8b19c%Z.
      eapply (bswcall Bz0 66 m1); [lia| exact OK0| bz_params; cbn [Bz0 bw_numZ]; lia| exact EH1b0| exact EH2b0| exact AR2b0| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|].
      clear EH1b0 EH2b0 AR2b0 MI ST. after_call8 m1 m2. retpc 0x89d04%Z.
      pose proof (bsW8_growth Bz0 66 OK0 ltac:(lia)) as G1.
      revert EH1 EH2 AR2 G1 K. generalize (bsW Bz0 8 66) as B1'. intros B1' EH1 EH2 AR2 G1 K. cps_destruct G1 as (OK1 & NZ1 & LV1). cbn [Bz0 bw_numZ] in NZ1.
      (* [comment removed for export] *)
      brun_to 0x89d08%Z. wstep. brun_to 0x8b19c%Z.
      eapply (bswcall B1' 90 m2); [lia| exact OK1| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|].
      clear EH1 EH2 AR2 MI ST. after_call8 m2 m3. retpc 0x89d10%Z.
      pose proof (bsW8_growth B1' 90 OK1 ltac:(lia)) as G2.
      revert EH1 EH2 AR2 G2 K. generalize (bsW B1' 8 90) as B2. intros B2 EH1 EH2 AR2 G2 K. cps_destruct G2 as (OK2 & NZ2 & LV2).
      (* [comment removed for export] *)
      brun_to 0x89d14%Z. wstep. brun_to 0x8b19c%Z.
      eapply (bswcall B2 104 m3); [lia| exact OK2| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|].
      clear EH1 EH2 AR2 MI ST. after_call8 m3 m4. retpc 0x89d1c%Z.
      pose proof (bsW8_growth B2 104 OK2 ltac:(lia)) as G3.
      revert EH1 EH2 AR2 G3 K. generalize (bsW B2 8 104) as B3. intros B3 EH1 EH2 AR2 G3 K. cps_destruct G3 as (OK3 & NZ3 & LV3).
      (* [comment removed for export] *)
      pose proof EH2 as EH2r. unfold EH2b, EHEAD2, g3 in EH2r. cbn_est_in EH2r.
      wstep. brun_to 0x89d38%Z. wstep. clear EH2r. brun_to 0x8b19c%Z.
      lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace v with (48 + BLOCKSIZE100K)%Z end.
      2:{ rewrite hdr_digit_land; lia. }
      eapply (bswcall B3 (48 + BLOCKSIZE100K)%Z m4); [lia| exact OK3| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|].
      clear EH1 EH2 AR2 MI ST. after_call8 m4 m5. retpc 0x89d54%Z.
      pose proof (bsW8_growth B3 (48 + BLOCKSIZE100K) OK3 ltac:(bz_params; lia)) as G4.
      revert EH1 EH2 AR2 G4 K. generalize (bsW B3 8 (48 + BLOCKSIZE100K)) as B4. intros B4 EH1 EH2 AR2 G4 K. cps_destruct G4 as (OK4 & NZ4 & LV4).
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end; cbv zeta;
        [st_eq| exact EH1| exact EH2| exact AR2| slB_cbn; rewrite ?H88, ?H144; exact SL| exact MI| exact ST| unfold cbH_W; exact MU| exact WM| exact OK4| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_cb_H2r : forall (m : word -> option byte) (sl : cbslB)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 : word),
    bw_numZ (e_bw e) = 0%Z -> (1 <= e_blockNo e < 2147483647)%Z -> (e_blockNo e = 1%Z \/ (g_bs g = true /\ bw_ok (e_bw e))) ->
    (n <= (NBLOCKMAX + 19))%Z ->
    q88 sl = Z_to_bv 64 E -> q144 sl = Z_to_bv 64 (SHE + 13) ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) -> u8arr b0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    rw_cells b0segs m P (cbslB_cells sl) -> mem_inv b0segs m -> stk b0segs m lo P ->
    acoW cbH_W m -> cctx_sh b0segs cx cbH_W m ->
    (forall (m' : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' t3' t4' t5' t6' : word),
      let bS := cb_hdr e in
      rw_cells b0segs m' E (EHEAD1 cx g3 (est_set_bw e bS)) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g3 (est_set_bw e bS)) ->
      u8arr b0segs m' A2 (zb8 (zbl (e_arr2 e) n bS) ARR2_SIZE) ->
      rw_cells b0segs m' P (cbslB_cells (sl2 sl)) -> mem_inv b0segs m' -> stk b0segs m' lo P -> munch cbH_W m m' -> wmono b0segs m m' ->
      bw_ok bS -> (bw_numZ bS <= 16)%Z ->
      evt b0segs Q (MS (RW ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13)) (il_w (ce_il X)) s4 (Z_to_bv 64 (E + 108)) s7
                           (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x89d5c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (il_w (ce_il X)) s4 (Z_to_bv 64 (E + 108)) s7
                         (Z_to_bv 64 (E + 660)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x89c18) fc None m (seg_rom b0segs)).
  Proof.
    intros m sl ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 NZ BN ALT NB H88 H144 EH1 EH2 AR2 SL MI ST ACW CSH K.
    pose proof SL as SLr. unfold cbslB_cells in SLr. rewrite H88, H144 in SLr.
    acenv_open YOK.
    wstep. wstep. clear SLr.
    eapply (B0_cb_H2 m sl); [exact NZ| exact BN| exact ALT| exact NB| exact H88| exact H144| exact EH1| exact EH2| exact AR2| exact SL| exact MI| exact ST| exact ACW| exact CSH| exact K].
  Qed.

End B0CBH2.

End ACeilS1.
