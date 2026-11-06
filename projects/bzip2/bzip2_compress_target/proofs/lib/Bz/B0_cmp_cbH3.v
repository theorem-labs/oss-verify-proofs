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
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV CmpSmKit CmpHmKit B0_cmp_cbV B0_cmp_cbWc B0_cmp_cbWf.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpMsKit2.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slB_cbn_in H := unfold cbslB_cells in H; cbn [bset0 bset8 bset16 bset24 bset32 bset40 bset48 bset56 bset64 bset72 bset80 bset88 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152 bset160 bset168 bset176 q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q128 q136 q144 q152 q160 q168 q176] in H.

Section B0CBH3.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation nblock := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis Gsort : g_sort g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Notation EH1b := (EH1b X g e). Notation EH2b := (EH2b X g e). Notation AR2b := (AR2b X e).
  Notation ILW := (il_w (ce_il X)).
  (* [comment removed for export] *)
  Definition cbH3_W : list (Z * Z) := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P - 48, P + 184)]%Z.
  Notation WW := cbH3_W.

  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         cSB s3 s4 (Z_to_bv 64 FB) s6 s7 (Z_to_bv 64 FB) s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6).
  Notation bswcall := (B0_bsw8_call X Y g e Q XOK YOK Gbs Gzb Hnb).
  Notation bsxcall := (B0_bsput32_call X Y g e Q XOK YOK Gbs Gzb Hnb).

  (* [comment removed for export] *)
  Lemma bsW1_0_fields : forall b, let b1 := bs_needw BS_FUEL b in
    bw_buff (bsW b 1 0) = bw_buff b1 /\ bw_live (bsW b 1 0) = (bw_live b1 + 1)%Z /\ bw_numZ (bsW b 1 0) = bw_numZ b1 /\ bw_zb (bsW b 1 0) = bw_zb b1.
  Proof. intros b. unfold bsW. cbn [bw_buff bw_live bw_numZ bw_zb]. rewrite Z.shiftl_0_l, Z.mod_0_l, Z.lor_0_r by lia. repeat split; reflexivity. Qed.
  Lemma bsW24_fields : forall b v, let b1 := bs_needw BS_FUEL b in
    bw_buff (bsW b 24 v) = Z.lor (bw_buff b1) ((Z.shiftl v (8 - bw_live b1)) mod 4294967296) /\ bw_live (bsW b 24 v) = (bw_live b1 + 24)%Z /\
    bw_numZ (bsW b 24 v) = bw_numZ b1 /\ bw_zb (bsW b 24 v) = bw_zb b1.
  Proof. intros b v. unfold bsW. cbn [bw_buff bw_live bw_numZ bw_zb]. replace (32 - bw_live (bs_needw BS_FUEL b) - 24)%Z with (8 - bw_live (bs_needw BS_FUEL b))%Z by lia. repeat split; reflexivity. Qed.

  Ltac csh_sub MU :=
    let CSH := ident:(CSH) in
    lazymatch type of MU with munch _ ?m0 ?mc => eapply (cctx_sh_sub b0segs cx WW _ m0 mc CSH MU); unfold cbH3_W, cbW_W; a_sub_fp end.
  Ltac after_call8 mprev mnew :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let AR2 := ident:(AR2) in let MI := ident:(MI) in let ST := ident:(ST) in
    let MUc := ident:(MUc) in let WMc := ident:(WMc) in
    intros mnew ?t0 ?t1 ?t2 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?t3 ?t4 ?t5 ?t6; cbv zeta; intros EH1 EH2 AR2 MI ST MUc WMc;
    unfold cbW_W in MUc; transport_after_call b0segs mprev mnew MUc WMc; clear MUc WMc.
  Ltac retpc rp := replace (ret_pc (Z_to_bv 64 rp)) with (Z_to_bv 64 rp) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  Ltac call8 B OKB v mc mn rp Bn OKn NZn LVn :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let AR2 := ident:(AR2) in let MI := ident:(MI) in let ST := ident:(ST) in
    let ACW := ident:(ACW) in let MU := ident:(MU) in let K := ident:(Kpos) in
    brun_to 0x8b19c%Z;
    eapply (bswcall B v mc); [lia| exact OKB| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|];
    clear EH1 EH2 AR2 MI ST; after_call8 mc mn; retpc rp;
    let G := fresh "G" in
    pose proof (bsW8_growth B v OKB ltac:(lia)) as G;
    revert EH1 EH2 AR2 G K; generalize (bsW B 8 v) as Bn; intros Bn EH1 EH2 AR2 G K; cps_destruct G as (OKn & NZn & LVn).

  Lemma B0_cb_H3 : forall (b : bw) (m : word -> option byte) (sl : cbslB)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word),
    bw_ok b -> (nblock + bw_numZ b + 64 <= ARR2_SIZE)%Z -> (0 <= e_blockCRC e < 4294967296)%Z -> (0 <= e_origPtr e < 16777216)%Z ->
    (nblock <= NBLOCKMAX + 19)%Z ->
    q56 sl = Z_to_bv 64 (SHE + 10) -> q64 sl = Z_to_bv 64 (E + 80) -> q88 sl = Z_to_bv 64 E -> q144 sl = Z_to_bv 64 (SHE + 13) ->
    EH1b m b -> EH2b m b -> AR2b m b -> rw_cells b0segs m P (cbslB_cells sl) -> mem_inv b0segs m -> stk b0segs m lo P ->
    acoW WW m -> cctx_sh b0segs cx WW m ->
    ((0 < nblock)%Z -> forall m' (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' : word),
      let bH := cb_bhdr b e in
      EH1b m' bH -> EH2b m' bH -> AR2b m' bH -> rw_cells b0segs m' P (cbslB_cells (bset32 sl ILW)) -> mem_inv b0segs m' -> stk b0segs m' lo P ->
      munch WW m m' -> wmono b0segs m m' -> bw_ok bH -> (bw_numZ b <= bw_numZ bH <= bw_numZ b + 48)%Z ->
      evt b0segs Q (MS (RW ra' t0' t1' t2' (Z_to_bv 64 (E + 56)) (Z_to_bv 64 (SHE + 80)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116))
                           (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3' t4' t5' (Z_to_bv 64 (E + 80)))
                       F (Z_to_bv 64 0x8a11c) fc None m' (seg_rom b0segs))) ->
    (nblock = 0%Z -> forall (a0' : word),
      evt b0segs Q (MS (RW ra t0 t1 t2 a0' a1 a2 a3 a4 a5 (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13)) ILW (Z_to_bv 64 (E + 116))
                           (Z_to_bv 64 (E + 108)) (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8aa58) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13)) ILW (Z_to_bv 64 (E + 116))
                         (Z_to_bv 64 (E + 108)) (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x89d5c) fc None m (seg_rom b0segs)).
  Proof.
    intros b m sl ra t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 OK ROOM HBC HOP NB H56 H64 H88 H144 EH1 EH2 AR2 SL MI ST ACW CSH Kpos Kz.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _); box_ors.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
    assert (EL640 : Z.land (E + 640) 7 = 0%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    assert (EL116 : Z.land (E + 116) 7 = 4%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    assert (EL644 : Z.land (E + 644) 7 = 4%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    pose proof ROOM as RM. bz_params.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl WW m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof CSH as CSH'. destruct CSH' as (SHe & _ & SH2 & _). unfold cbH3_W, ESTATE_SIZE in MU, SHe, SH2.
    unfold cbslB_cells in SL. rewrite H56, H64, H88, H144 in SL.
    rename m into m0. rename b into Bz0. pose proof OK as OK0. pose proof (Z.le_refl (bw_numZ Bz0)) as NZ0.
    (* [comment removed for export] *)
    pose proof EH1 as EH1r. unfold B0_cmp_cbWc.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r. rewrite Gsort, Gzb in EH1r.
    brun_to 0x89d6c%Z. clear EH1r. try rewrite (sx32_of_Z nblock) by lia.
    (wstep; if_cases Kn; [apply CmpMsKit2.blez_taken in Kn; [|lia] | apply CmpMsKit2.blez_not_taken in Kn; [|lia]]).
    { assert (N0 : nblock = 0%Z) by lia. enter_with (Kz N0 _). replace (Z_to_bv 64 nblock) with (Z_to_bv 64 0) by (rewrite N0; reflexivity). st_eq. }
    assert (POS : (0 < nblock)%Z) by lia. try clear Kn. specialize (Kpos POS). clear Kz.
    rewrite cb_bhdr_eq, bz_magic6_eq in Kpos.
    (* [comment removed for export] *)
    pose proof EH1 as EH1r. unfold B0_cmp_cbWc.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r.
    pose proof EH2 as EH2r. unfold B0_cmp_cbWc.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. unfold B0_cmp_cbWc.AR2b in AR2. clear EH1 EH2.
    wstep. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0s end.
    assert (EH1 : EH1b m0s Bz0) by (unfold B0_cmp_cbWc.EH1b, EHEAD1; cbn_est; exact EH1r).
    assert (EH2 : EH2b m0s Bz0) by (unfold B0_cmp_cbWc.EH2b, EHEAD2; cbn_est; exact EH2r).
    assert (AR2' : AR2b m0s Bz0) by exact AR2. clear EH1r EH2r AR2. rename AR2' into AR2.
    call8 Bz0 OK0 49%Z m0s m1 0x89d84%Z B1 OK1 NZ1 LV1.
    call8 B1 OK1 65%Z m1 m2 0x89d90%Z B2 OK2 NZ2 LV2.
    call8 B2 OK2 89%Z m2 m3 0x89d9c%Z B3 OK3 NZ3 LV3.
    call8 B3 OK3 38%Z m3 m4 0x89da8%Z B4 OK4 NZ4 LV4.
    call8 B4 OK4 83%Z m4 m5 0x89db4%Z B5 OK5 NZ5 LV5.
    call8 B5 OK5 89%Z m5 m6 0x89dc0%Z B6 OK6 NZ6 LV6.
    (* [comment removed for export] *)
    pose proof EH2 as EH2r. unfold B0_cmp_cbWc.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
    brun_to 0x8b418%Z. clear EH2r.
    eapply (bsxcall B6 (e_blockCRC e) m6); [exact HBC| exact OK6| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (ACW _ MU)| csh_sub MU|].
    clear EH1 EH2 AR2 MI ST. after_call8 m6 m7. retpc 0x89de0%Z.
    pose proof (bsPutUInt32_growth B6 (e_blockCRC e) OK6 ltac:(lia)) as G7.
    revert EH1 EH2 AR2 G7 Kpos. generalize (bsPutUInt32 B6 (e_blockCRC e)) as B7.
    intros B7 EH1 EH2 AR2 G7 Kpos. cps_destruct G7 as (OK7 & NZ7 & LV7). cps_pose OK7 as (OK7b & OK7l & OK7n).
    (* [comment removed for export] *)
    pose proof (bsW1_0_fields B7) as F8. cbv zeta in F8.
    assert (LF7 : (bw_live B7 < 40)%Z) by lia. pose proof (bs_needw_post BS_FUEL B7 OK7 LF7) as NP.
    set (B7' := bs_needw BS_FUEL B7) in *.
    assert (JN : forall (m8 : word -> option byte) (xra x7 x10 x12 x13 x14 x15 x16 x17 x5 x6 x28 x29 x30 : word),
      (bw_numZ B7' <= bw_numZ B7 + 5)%Z ->
      EH1b m8 B7' -> EH2b m8 B7' -> AR2b m8 B7' -> mem_inv b0segs m8 -> stk b0segs m8 lo P ->
      rw_cells b0segs m8 P (cbslB_cells (bset32 sl ILW)) -> munch WW m0 m8 -> wmono b0segs m0 m8 ->
      evt b0segs Q (MS (RW xra (Z_to_bv 64 (bw_live B7')) x5 x6 x10 (Z_to_bv 64 (SHE + 80)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116))
                           (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) x28 x29 x30 (Z_to_bv 64 (E + 80)))
                       F (Z_to_bv 64 0x89f40) fc None m8 (seg_rom b0segs))).
    { clear EH1 EH2 AR2 MI ST SL MU WM. intros m8 xra x7 x10 x12 x13 x14 x15 x16 x17 x5 x6 x28 x29 x30 NZB EH1 EH2 AR2 MI ST SL MU WM. unfold cbH3_W in MU.
      slB_cbn_in SL. rewrite H56, H64, H88, H144 in SL.
      cps_destruct NP as (OK7' & LVE & NZ7'). cps_pose OK7' as (OK7'b & OK7'l & OK7'n).
      assert (LV7' : (0 <= bw_live B7' < 8)%Z) by (rewrite LVE; Z.div_mod_to_equations; lia).
      pose proof EH1 as EH1r. unfold B0_cmp_cbWc.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r. rewrite Gsort, Gzb in EH1r.
      pose proof EH2 as EH2r. unfold B0_cmp_cbWc.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r. clear EH1 EH2.
      unfold B0_cmp_cbWc.AR2b in AR2.
      (* [comment removed for export] *)
      brun_to 0x89f90%Z.
      try rewrite (sx32_of_Z (bw_live B7' + 1)) in * by lia.
      (* [comment removed for export] *)
      cps_destruct F8 as (F8b & F8l & F8n & F8z).
      replace (bw_buff B7') with (bw_buff (bsW B7 1 0)) in EH2r by (rewrite F8b; reflexivity).
      replace (bw_live B7' + 1)%Z with (bw_live (bsW B7 1 0)) in EH2r by (rewrite F8l; reflexivity).
      replace (bw_numZ B7') with (bw_numZ (bsW B7 1 0)) in EH1r by (rewrite F8n; reflexivity).
      rewrite <- (zbl_same_bytes (e_arr2 e) nblock B7' (bsW B7 1 0) F8n F8z) in AR2.
      pose proof (bsW_growth B7 1 0 OK7 ltac:(lia) ltac:(lia)) as G8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8s end.
      assert (EH1b8 : EH1b m8s (bsW B7 1 0)) by (unfold B0_cmp_cbWc.EH1b, EHEAD1; cbn_est; rewrite Gsort, Gzb; exact EH1r). clear EH1r.
      assert (EH2b8 : EH2b m8s (bsW B7 1 0)) by (unfold B0_cmp_cbWc.EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2r). clear EH2r.
      assert (AR2b8 : AR2b m8s (bsW B7 1 0)) by (unfold B0_cmp_cbWc.AR2b; exact AR2). clear AR2.
      assert (L78 : (bw_live B7' = bw_live (bsW B7 1 0) - 1)%Z) by (rewrite F8l; lia).
      revert EH1b8 EH2b8 AR2b8 G8 F8b F8l F8n F8z L78 Kpos. generalize (bsW B7 1 0) as B8. intros B8 EH1 EH2 AR2 G8 F8b F8l F8n F8z L78 Kpos.
      cps_destruct G8 as (OK8 & NZ8 & LV8). cps_pose OK8 as (OK8b & OK8l & OK8n).
      pose proof (bsW24_fields B8 (e_origPtr e)) as F9. cbv zeta in F9.
      assert (LF8 : (bw_live B8 < 40)%Z) by lia. pose proof (bs_needw_post BS_FUEL B8 OK8 LF8) as NP8.
      set (B8' := bs_needw BS_FUEL B8) in *.
      (* [comment removed for export] *)
      assert (JN2 : forall (m9 : word -> option byte) (yra y5 y7 y10 y13 y14 y15 y16 y17 y28 y29 y30 : word),
        (bw_numZ B8' <= bw_numZ B8 + 5)%Z ->
        EH1b m9 B8' -> EH2b m9 B8' -> AR2b m9 B8' -> mem_inv b0segs m9 -> stk b0segs m9 lo P ->
        rw_cells b0segs m9 P (cbslB_cells (bset32 sl ILW)) -> munch WW m0 m9 -> wmono b0segs m0 m9 ->
        evt b0segs Q (MS (RW yra y5 (Z_to_bv 64 (bw_live B8')) y7 y10 (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (e_origPtr e)) y13 y14 y15 y16 y17
                             (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 108)) (Z_to_bv 64 E) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) y28 y29 y30 (Z_to_bv 64 (E + 80)))
                         F (Z_to_bv 64 0x8a0c4) fc None m9 (seg_rom b0segs))).
      { clear EH1 EH2 AR2 MI ST SL MU WM. intros m9 yra y5 y7 y10 y13 y14 y15 y16 y17 y28 y29 y30 NZB2 EH1 EH2 AR2 MI ST SL MU WM. unfold cbH3_W in MU.
        slB_cbn_in SL. rewrite H56, H64, H88, H144 in SL.
        cps_destruct NP8 as (OK8' & LVE8 & NZ8'). cps_pose OK8' as (OK8'b & OK8'l & OK8'n).
        assert (LV8' : (0 <= bw_live B8' < 8)%Z) by (rewrite LVE8; Z.div_mod_to_equations; lia).
        pose proof EH1 as EH1r. unfold B0_cmp_cbWc.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r. rewrite Gsort, Gzb in EH1r.
        pose proof EH2 as EH2r. unfold B0_cmp_cbWc.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r. clear EH1 EH2.
        unfold B0_cmp_cbWc.AR2b in AR2.
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        brun_to 0x8a11c%Z.
        replace ((32 - bw_live B8' + -24) mod 32)%Z with (8 - bw_live B8')%Z in EH2r by (rewrite Z.mod_small; lia).
        cps_destruct F9 as (F9b & F9l & F9n & F9z).
        pose proof (bsW_growth B8 24 (e_origPtr e) OK8 ltac:(lia) ltac:(lia)) as G9. cps_destruct G9 as (OK9 & NZ9 & LV9).
        assert (XB2 : (bv_unsigned (sx32 (Z_to_bv 64 (bw_buff B8'))) mod 4294967296 = bw_buff B8')%Z).
        { rewrite low32_sx32, low32_lit. apply low32_small. lia. }
        reword_C4 EH2r 0%nat (bw_buff (bsW B8 24 (e_origPtr e))).
        { rewrite F9b, low32_lit, low32_lor. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
          change (2 ^ 64)%Z with 18446744073709551616%Z. rewrite mod64_mod32, swrap32_mod32, XB2.
          symmetry. apply low32_small.
          pose proof (Z.mod_pos_bound (Z.shiftl (e_origPtr e) (8 - bw_live B8')) 4294967296 ltac:(lia)) as MB.
          pose proof (BzLemmasT.lor_lt_pow2 (bw_buff B8') ((Z.shiftl (e_origPtr e) (8 - bw_live B8')) mod 4294967296) 32) as LB.
          change (2 ^ 32)%Z with 4294967296%Z in LB. lia. }
        replace (bw_live B8' + 24)%Z with (bw_live (bsW B8 24 (e_origPtr e))) in EH2r by (rewrite F9l; reflexivity).
        replace (bw_numZ B8') with (bw_numZ (bsW B8 24 (e_origPtr e))) in EH1r by (rewrite F9n; reflexivity).
        rewrite <- (zbl_same_bytes (e_arr2 e) nblock B8' (bsW B8 24 (e_origPtr e)) F9n F9z) in AR2.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kpos mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end; cbv zeta;
          [ st_eq
          | unfold B0_cmp_cbWc.EH1b, EHEAD1; cbn_est; rewrite Gsort, Gzb; exact EH1r
          | unfold B0_cmp_cbWc.EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2r
          | unfold B0_cmp_cbWc.AR2b; exact AR2
          | slB_cbn; rewrite H56, H64, H88, H144; exact SL
          | exact MI| exact ST| unfold cbH3_W; exact MU| exact WM| exact OK9| lia]. }
      (* [comment removed for export] *)
      wstep; if_cases Kg; zify_cond_z Kg.
      - assert (E8 : B8' = B8).
        { subst B8'. unfold BS_FUEL. rewrite bs_needw_S. replace (8 <=? bw_live B8)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN2 mm _ _ _ _ _ _ _ _ _ _ _ _) end; rewrite ?E8;
          [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| slB_cbn; rewrite H56, H64, H88, H144; exact SL| exact MU| exact WM].
      - (* [comment removed for export] *)
        brun_to 0x89fbc%Z. sh_norm. rewrite ?EL640, ?EL116, ?EL644.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8t end.
        replace (bw_live B7' + 1)%Z with (bw_live B8) by lia.
        enter_with (B0_cb_flush2 X Y g e Q XOK YOK AE Gbs Gzb Hnb BS_FUEL B8 m8t m8t);
          [st_eq| exact OK8| lia| change (Z.of_nat BS_FUEL) with 5%Z; lia| bz_params; change (Z.of_nat BS_FUEL) with 5%Z; lia
          | exact EH1| exact EH2| exact AR2| exact MI| apply munch_refl| apply wmono_refl
          | eapply (shzW_sub b0segs WW _ m0 m8t); [exact SHe| exact MU| unfold cbF_W, cbH3_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
          | eapply (shzW_sub b0segs WW _ m0 m8t); [exact SH2| exact MU| unfold cbF_W, cbH3_W; a_sub_fp| lia| lia] |].
        clear EH1 EH2 AR2 MI.
        intros b1 m9 a0' t2' t3' t4' t5' Eb1 EH1 EH2 AR2 MI MU9 WM9 LVb OKb' NZb'. change (Z.of_nat BS_FUEL) with 5%Z in NZb'. fold B8' in Eb1. subst b1.
        unfold cbF_W in MU9. transport_after_call b0segs m8t m9 MU9 WM9. clear MU9 WM9.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN2 mm _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| slB_cbn; rewrite H56, H64, H88, H144; exact SL| exact MU| exact WM]. }
    (* [comment removed for export] *)
    pose proof EH2 as EH2r. unfold B0_cmp_cbWc.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
    brun_to 0x89e08%Z. clear EH2r. sh_norm. try rewrite (sx32_of_Z (bw_live B7)) by lia.
    wstep; if_cases Kf; zify_cond_z Kf.
    - (* [comment removed for export] *)
      assert (E7 : B7' = B7).
      { subst B7'. unfold BS_FUEL. rewrite bs_needw_S. replace (8 <=? bw_live B7)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end; rewrite ?E7;
        [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| slB_cbn; rewrite H56, H64, H88, H144; exact SL| exact MU| exact WM].
    - (* [comment removed for export] *)
      brun_to 0x89e38%Z. sh_norm. rewrite ?EL640, ?EL116, ?EL644.
      enter_with (B0_cb_flush1 X Y g e Q XOK YOK AE Gbs Gzb Hnb BS_FUEL B7 m7 m7);
        [st_eq| exact OK7| lia| change (Z.of_nat BS_FUEL) with 5%Z; lia| bz_params; change (Z.of_nat BS_FUEL) with 5%Z; lia
        | exact EH1| exact EH2| exact AR2| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs WW _ m0 m7); [exact SHe| exact MU| unfold cbF_W, cbH3_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
        | eapply (shzW_sub b0segs WW _ m0 m7); [exact SH2| exact MU| unfold cbF_W, cbH3_W; a_sub_fp| lia| lia] |].
      clear EH1 EH2 AR2 MI.
      intros b1 m8 a0' t1' t2' t3' t4' Eb1 EH1 EH2 AR2 MI MU8 WM8 LV' OK' NZ'. change (Z.of_nat BS_FUEL) with 5%Z in NZ'. fold B7' in Eb1. subst b1.
      unfold cbF_W in MU8. transport_after_call b0segs m7 m8 MU8 WM8. clear MU8 WM8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| slB_cbn; rewrite H56, H64, H88, H144; exact SL| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End B0CBH3.

End ACeilS1.
