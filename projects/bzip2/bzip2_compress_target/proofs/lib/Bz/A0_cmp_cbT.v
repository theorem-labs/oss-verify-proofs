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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 DecTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut BzCNumZ CmpLaws CmpCutCB CmpCutCBw CmpArith CmpArith2 CmpSdTac BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT BzWalkArith4 CmpCutBsw CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_cmp_cbW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCEmit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Section A0CBT.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y. Hypothesis YSEP : acenv_sep X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation nblock := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Notation EH1b := (EH1b X g e). Notation EH2b := (EH2b X g e). Notation AR2b := (AR2b X e).
  (* [comment removed for export] *)
  Definition cbT_W : list (Z * Z) := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P - 32, P); (FB, FB + 8)]%Z.

  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 cSB (Z_to_bv 64 E) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Notation bswcall := (A0_bsw8_call X Y g e Q XOK YOK Gbs Gzb Hnb).
  Notation bsxcall := (A0_bsput32_call X Y g e Q XOK YOK Gbs Gzb Hnb).

  Ltac csh_sub MU :=
    let CSH := ident:(CSH) in
    lazymatch type of MU with munch _ ?m0 ?mc => eapply (cctx_sh_sub a0segs cx cbT_W _ m0 mc CSH MU); unfold cbT_W, cbW_W; a_sub_fp end.
  Ltac after_call8 mprev mnew :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let AR2 := ident:(AR2) in let MI := ident:(MI) in let ST := ident:(ST) in
    let MUc := ident:(MUc) in let WMc := ident:(WMc) in
    intros mnew ?t0 ?t1 ?t2 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?t3 ?t4 ?t5 ?t6; cbv zeta; intros EH1 EH2 AR2 MI ST MUc WMc;
    unfold cbW_W in MUc; transport_after_call a0segs mprev mnew MUc WMc; clear MUc WMc.
  Ltac call8 B OKB v mc mn rp Bn OKn NZn LVn :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let AR2 := ident:(AR2) in let MI := ident:(MI) in let ST := ident:(ST) in
    let ACW := ident:(ACW) in let MU := ident:(MU) in let K := ident:(EXIT) in
    arun_to 0x89c74%Z;
    eapply (bswcall B v mc); [lia| exact OKB| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|];
    clear EH1 EH2 AR2 MI ST; after_call8 mc mn;
    replace (ret_pc (Z_to_bv 64 rp)) with (Z_to_bv 64 rp) by (symmetry; apply ret_pc_even; [lia| reflexivity]);
    let G := fresh "G" in
    pose proof (bsW8_growth B v OKB ltac:(lia)) as G;
    revert EH1 EH2 AR2 G K; generalize (bsW B 8 v) as Bn; intros Bn EH1 EH2 AR2 G K; cps_destruct G as (OKn & NZn & LVn).

  Lemma A0_cb_T : forall (b : bw) (m : word -> option byte) (sl : cbsl) (h0 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    bw_ok b -> (nblock + bw_numZ b + 40 <= ARR2_SIZE)%Z -> (0 <= e_combinedCRC e < 4294967296)%Z ->
    k48 sl = Z_to_bv 64 (E + 656) -> k56 sl = Z_to_bv 64 (E + 80) -> k80 sl = Z_to_bv 64 (SHE + 10) ->
    EH1b m b -> EH2b m b -> AR2b m b -> rw_cells a0segs m P (cbsl_cells sl) -> rw_cells a0segs m FB [C8 h0] -> mem_inv a0segs m -> stk a0segs m lo P ->
    acoW cbT_W m -> cctx_sh a0segs cx cbT_W m ->
    (forall m' (t0' t1' t2' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word),
        let b' := cb_trailer (ce_il X) b (e_combinedCRC e) in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> rw_cells a0segs m' P (cbsl_cells sl) -> rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x45e0360e)] ->
        mem_inv a0segs m' -> stk a0segs m' lo P -> munch cbT_W m m' -> wmono a0segs m m' -> (bw_numZ b <= bw_numZ b' <= bw_numZ b + 36)%Z ->
        evt a0segs Q (MS (RW (Z_to_bv 64 0x89818) t0' t1' t2' (Z_to_bv 64 SHF) (Z_to_bv 64 64) a2' a3' a4' a5' a6' a7' s2' (Z_to_bv 64 (E + 80)) (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB)
                             (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 652)) t3' t4' t5' t6')
                          F (Z_to_bv 64 0x559cc) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (il_w (ce_il X)) s5 (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB)
                         (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                      F (Z_to_bv 64 0x8968c) fc None m (seg_rom a0segs)).
  Proof.
    intros b m sl h0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 OK ROOM HCC H48 H56 H80 EH1 EH2 AR2 SL HD MI ST ACW CSH K.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _).
    pose proof YSEP as YS; unfold acenv_sep, apartv, ESTATE_SIZE in YS; cbv zeta in YS; destruct YS as (FE & _ & F2).
    box_ors.
    cps_pose OK as (OKb & OKl & OKn). pose proof ROOM as RM. bz_params.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl cbT_W m) as MU. pose proof (wmono_refl a0segs m) as WM.
    pose proof CSH as CSH'. destruct CSH' as (SHe & _ & SH2 & _). unfold cbT_W, ESTATE_SIZE in MU, SHe, SH2.
    unfold cbsl_cells in SL. rewrite H48, H56, H80 in SL.
    rename m into m0. rename b into B0. pose proof OK as OK0. pose proof (Z.le_refl (bw_numZ B0)) as NZ0.
    (* [comment removed for export] *)
    assert (EXIT : forall (bf : bw) (m9 : word -> option byte) (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      (bw_numZ B0 <= bw_numZ bf <= bw_numZ B0 + 36)%Z -> bf = cb_trailer (ce_il X) B0 (e_combinedCRC e) ->
      EH1b m9 bf -> EH2b m9 bf -> AR2b m9 bf -> rw_cells a0segs m9 P (cbsl_cells sl) -> rw_cells a0segs m9 FB [C8 h0] -> mem_inv a0segs m9 -> stk a0segs m9 lo P ->
      munch cbT_W m0 m9 -> wmono a0segs m0 m9 ->
      evt a0segs Q (MS (RW xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (E + 80)) (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB)
                           (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 652)) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x897fc) fc None m9 (seg_rom a0segs))).
    { clear EH1 EH2 AR2 SL HD MI ST MU WM. intros bf m9 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 NZf Ebf EH1 EH2 AR2 SL HD MI ST MU WM.
      unfold cbT_W in MU.
      unfold A0_cmp_cbW.EH1b, EHEAD1 in EH1. unfold A0_cmp_cbW.EH2b, EHEAD2 in EH2. unfold A0_cmp_cbW.AR2b in AR2.
      pose proof (zb8_length (zbl (e_arr2 e) nblock bf) ARR2_SIZE ltac:(lia)) as LA2.
      (* [comment removed for export] *)
      wstep. wstep. wstep. lit_store.
      (* [comment removed for export] *)
      wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end; cbv zeta; rewrite <- ?Ebf;
        [st_eq| unfold A0_cmp_cbW.EH1b, EHEAD1; exact EH1| unfold A0_cmp_cbW.EH2b, EHEAD2; exact EH2| unfold A0_cmp_cbW.AR2b; exact AR2| exact SL| exact HD| exact MI| exact ST| unfold cbT_W; exact MU| exact WM| exact NZf]. }
    (* [comment removed for export] *)
    wstep.
    destruct (ce_il X) eqn:EIL; unfold il_w.
    2:{ (* [comment removed for export] *)
        wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (EXIT B0 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| rewrite BzCEmit.cb_trailer_false; reflexivity| exact EH1| exact EH2| exact AR2| unfold cbsl_cells; rewrite H48, H56, H80; exact SL| exact HD| exact MI| exact ST| exact MU| exact WM]. }
    wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    rewrite cb_trailer_true, bz_fin6_eq in EXIT.
    call8 B0 OK0 23%Z m0 m1 0x896a0%Z B1 OK1 NZ1 LV1.
    call8 B1 OK1 114%Z m1 m2 0x896ac%Z B2 OK2 NZ2 LV2.
    call8 B2 OK2 69%Z m2 m3 0x896b8%Z B3 OK3 NZ3 LV3.
    call8 B3 OK3 56%Z m3 m4 0x896c4%Z B4 OK4 NZ4 LV4.
    call8 B4 OK4 80%Z m4 m5 0x896d0%Z B5 OK5 NZ5 LV5.
    call8 B5 OK5 144%Z m5 m6 0x896dc%Z B6 OK6 NZ6 LV6.
    (* [comment removed for export] *)
    pose proof EH2 as EH2r. unfold A0_cmp_cbW.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
    arun_to 0x89e30%Z. clear EH2r.
    eapply (bsxcall B6 (e_combinedCRC e) m6); [exact HCC| exact OK6| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|].
    clear EH1 EH2 AR2 MI ST. after_call8 m6 m7.
    replace (ret_pc (Z_to_bv 64 0x896f8)) with (Z_to_bv 64 0x896f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsPutUInt32_growth B6 (e_combinedCRC e) OK6 ltac:(lia)) as G7.
    revert EH1 EH2 AR2 G7 EXIT. generalize (bsPutUInt32 B6 (e_combinedCRC e)) as B7. intros B7 EH1 EH2 AR2 G7 EXIT.
    cps_destruct G7 as (OK7 & NZ7 & LV7). cps_pose OK7 as (OK7b & OK7l & OK7n).
    (* [comment removed for export] *)
    pose proof EH1 as EH1r. unfold A0_cmp_cbW.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r. rewrite Gzb in EH1r.
    pose proof EH2 as EH2r. unfold A0_cmp_cbW.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
    arun_to 0x8972c%Z. clear EH1r EH2r. try rewrite (sx32_of_Z (bw_live B7)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kl; zify_cond_z Kl.
    - (* [comment removed for export] *)
      assert (FBe : bs_finish BS_FUEL B7 = B7) by (unfold BS_FUEL; cbn [bs_finish]; replace (0 <? bw_live B7)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (EXIT B7 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| lia| rewrite FBe; reflexivity| exact EH1| exact EH2| exact AR2| unfold cbsl_cells; rewrite H48, H56, H80; exact SL| exact HD| exact MI| exact ST| exact MU| exact WM].
    - (* [comment removed for export] *)
      arun_to 0x89760%Z. sh_norm.
      assert (V80 : frdW a0segs (cbF_W X) m7 (P + 80) [C8 (Z_to_bv 64 (SHE + 10))]).
      { eapply (frdW_cell_at a0segs _ _ P _ 80 _ (P + 80)%Z); [apply frdW_intro; [exact SL| unfold cbF_W; cbn [disjoint_from cells_size csize Nat.add]; lia]| reflexivity| lia]. }
      enter_with (A0_cb_finish X Y g e Q XOK YOK AE Gbs Gzb Hnb BS_FUEL B7 m7 m7);
        [st_eq| lia| lia| lia| unfold BS_FUEL; change (8 * Z.of_nat 5)%Z with 40%Z; lia| unfold BS_FUEL; change (Z.of_nat 5) with 5%Z; bz_params; lia
        | exact EH1| exact EH2| exact AR2| exact MI| apply munch_refl| apply wmono_refl| exact V80
        | eapply (shzW_sub a0segs _ _ m0 m7); [exact SHe| exact MU| unfold cbF_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
        | eapply (shzW_sub a0segs _ _ m0 m7); [exact SH2| exact MU| unfold cbF_W; a_sub_fp| lia| lia] |].
      clear EH1 EH2 AR2 MI V80.
      intros m8 a1_8 t1_8 t2_8. cbv zeta. intros EH1 EH2 AR2 MI MU78 WM78 NZ8.
      unfold cbF_W in MU78. transport_after_call a0segs m7 m8 MU78 WM78. clear MU78 WM78.
      pose proof (bs_finish_growth B7 OK7) as G8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (EXIT (bs_finish BS_FUEL B7) mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| lia| reflexivity| exact EH1| exact EH2| exact AR2| unfold cbsl_cells; rewrite H48, H56, H80; exact SL| exact HD| exact MI| exact ST| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0CBT.

End ACeilS1.
