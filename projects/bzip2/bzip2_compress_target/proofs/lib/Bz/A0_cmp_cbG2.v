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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem CmpCut CmpCutMtf BzCFactsGm CmpFsKit CmpHmKit CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV A0_cmp_gmA.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section A0CBG2.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y. Hypothesis YSEP : acenv_sep X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Hypothesis GF : gm_facts e.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation nb := (e_nblock e).
  Notation EOB := (gp_EOB e). Notation nInUse := (gp_nInUse e). Notation unseq := (gp_unseq e).
  Definition cbG2_W : list (Z * Z) := [(E + 668, E + 1704); (A1, A1 + ARR1_SIZE); (FB + 32, FB + 288)]%Z.

  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 cSB (Z_to_bv 64 E) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  Ltac open_EH1 H := unfold EHEAD1n, EHEAD1 in H; cbn [removelast app] in H.
  Ltac fold_EH1 H v := lazymatch type of H with rw_cells ?sg ?mm ?A _ => change (rw_cells sg mm A (EHEAD1n cx g e v)) in H end.
  (* [comment removed for export] *)
  Ltac zb8_store2 ARR i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le2 ?w)) _) =>
      lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zb8_write2 segs m A a n i w ARR ltac:(lia) ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end end.

  #[local] Opaque gp_maps gp_nInUse gp_unseq.
  Lemma gm_e_spec : forall e0 arr1a mfa wra,
    (let s := gp_st e0 (Z.to_nat (e_nblock e0)) in
     if (0 <? gm_zPend s)%Z then mtf_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) = (arr1a, mfa, wra) ->
    gm_e e0 = EST (e_mode e0) (e_state e0) (e_avail_in_expect e0) (wr16 arr1a (2 * wra) (gp_EOB e0)) (e_arr2 e0) (e_ftab e0) (e_origPtr e0)
          (e_state_in_ch e0) (e_state_in_len e0) (e_nblock e0) (e_state_out_pos e0) (gp_nInUse e0) (e_inUse e0) (gp_unseq e0)
          (e_bw e0) (e_blockCRC e0) (e_combinedCRC e0) (e_blockNo e0) (wra + 1)%Z (zincr mfa (gp_EOB e0)) (e_selector e0) (e_selectorMtf e0)
          (e_len e0) (e_code e0) (e_rfreq e0) (e_len_pack e0).
  Proof. intros e0 arr1a mfa wra H. unfold gm_e. rewrite generateMTFValues_eq. unfold gp_fin. cbv zeta in H. rewrite H. cbn [mtf_emit fst]. reflexivity. Qed.

  Lemma A0_cb_G2 : forall (m : word -> option byte) (sl : cbsl) (Jy : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    let e' := gm_e e in
    (0 < nb)%Z ->
    k8 sl = Z_to_bv 64 (E + 652) -> k16 sl = il_w (ce_il X) -> k24 sl = Z_to_bv 64 FB -> k32 sl = Z_to_bv 64 FB -> k40 sl = Z_to_bv 64 nInUse ->
    k64 sl = Z_to_bv 64 (E + 108) -> k72 sl = Z_to_bv 64 A1 -> k88 sl = Z_to_bv 64 (SHE + 13) ->
    rw_cells a0segs m E (EHEAD1n cx g e nInUse) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    u8arr a0segs m (E + 384) (ovb unseq (jseg J 384 256) 256) -> u32arr a0segs m (E + 672) (ovw (gp_mtf0 e) (jseg J 672 1032) 258) ->
    u8arr a0segs m A1 (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr a0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    u8arr a0segs m (FB + 32) Jy -> Z.of_nat (length Jy) = 256%Z ->
    rw_cells a0segs m P (cbsl_cells sl) -> mem_inv a0segs m ->
    shzW a0segs cbG2_W m E (E + ESTATE_SIZE) -> shzW a0segs cbG2_W m A1 (A1 + ARR1_SIZE) -> shzW a0segs cbG2_W m A2 (A2 + ARR2_SIZE) ->
    shzW a0segs cbG2_W m (FB + 32) (FB + 288) ->
    (forall m' (Jy' : list byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' : word),
      rw_cells a0segs m' E (EHEAD1 cx (g_mtf_on g) e') -> rw_cells a0segs m' (E + 640) (EHEAD2 cx (g_mtf_on g) e') ->
      u8arr a0segs m' (E + 384) (ovb (e_unseqToSeq e') (jseg J 384 256) 256) -> u32arr a0segs m' (E + 672) (ovw (e_mtfFreq e') (jseg J 672 1032) 258) ->
      u8arr a0segs m' A1 (zb8 (e_arr1 e') ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 (e_arr2 e') ARR2_SIZE) ->
      u8arr a0segs m' (FB + 32) Jy' -> Z.of_nat (length Jy') = 256%Z ->
      rw_cells a0segs m' P (cbsl_cells sl) -> mem_inv a0segs m' -> munch cbG2_W m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (RW ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (il_w (ce_il X)) s5' (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB)
                           (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 652)) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x89600) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A1) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 SHF) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (E + 384))
                         (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 A2) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x891c8) fc None m (seg_rom a0segs)).
  Proof.
    intros m sl Jy ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 e' POS H8 H16 H24 H32 H40 H64 H72 H88 EH1 EH2 UNS MTF AR1 AR2 YYu LJy SL MI SHe SH1 SH2 SHy K. subst e'.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof YSEP as YS; unfold acenv_sep, apartv, ESTATE_SIZE in YS; cbv zeta in YS; destruct YS as (FE & F1 & F2).
    pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct (maps_facts e GF) as (NI & UB & UJ). pose proof (gp_EOB_eq e) as EE.
    assert (HF0 : (0 < FB)%Z) by lia. assert (HFC : (FB + 352 <= CEIL)%Z) by (unfold CEIL; lia).
    assert (FfE : (FB + 352 <= E \/ E + ESTATE_SIZE <= FB)%Z) by (unfold ESTATE_SIZE; lia).
    assert (Ff1 : (FB + 352 <= A1 \/ A1 + ARR1_SIZE <= FB)%Z) by lia.
    assert (Ff2 : (FB + 352 <= A2 \/ A2 + ARR2_SIZE <= FB)%Z) by lia.
    assert (PC : (CEIL <= P)%Z) by (unfold CEIL; lia). assert (PB : (P + 96 <= 18446744073709551616)%Z) by lia.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (AEA1 & AEA2 & _ & _ & _ & AA12 & _).
    box_ors.
    pose proof (zb8_length (e_arr1 e) ARR1_SIZE ltac:(lia)) as LA1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (munch_refl cbG2_W m) as MU0. pose proof (wmono_refl a0segs m) as WM0. unfold cbG2_W, ESTATE_SIZE in MU0, SHe, SH1, SH2, SHy.
    unfold cbsl_cells in SL. rewrite H8, H16, H24, H32, H40, H64, H72, H88 in SL.
    open_EH1 EH1.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kn1; zify_cond_z Kn1; [exfalso; lia|]. wstep. wstep. wstep. wstep.
    pose proof (rw_cells_of_u8arr a0segs _ _ _ YYu) as YYc. replace (length Jy) with (Z.to_nat 256) in YYc by lia.
    pose proof (ovb_init a0segs m (FB + 32) 256 Jy YYc ltac:(lia)) as YY. clear YYc YYu.
    enter_with (A0_gm_yyinit cx Q (Z_to_bv 64 P) gp tp (ce_sp X) (Z_to_bv 64 SHF) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) F fc P FB
                  (Z.to_nat nInUse) 0 nInUse znew Jy m m);
      [st_eq| lia| lia| lia| lia| exact LJy| exact HF0| exact HFC| exact YY| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub a0segs _ _ m m); [exact SHy| apply munch_refl| a_sub_fp| lia| unfold ESTATE_SIZE; lia] |].
    intros m3 ya0 ya1 ya2 ya3 ya4 YY3 MI3 MU3 WM3.
    assert (EH2_3 : id (rw_cells a0segs m3 (E + 640) (EHEAD2 cx g e))).
    { unfold id. eapply rw_cells_transport; [exact EH2| exact MU3| exact WM3|]. cbv [disjoint_from fst snd]. unfold EHEAD2. cbn [cells_size csize Nat.add].
      split; [| exact I]. clear - FfE. unfold id, ESTATE_SIZE in FfE. lia. }
    clear YY MI EH2. transport_after_call a0segs m m3 MU3 WM3. clear MU3 WM3.
    change (yy_init (Z.to_nat nInUse) znew 0) with (gp_yy0 e) in YY3.
    (* [comment removed for export] *)
    pose proof EH1 as EH1r.
    arun_to 0x8922c%Z. clear EH1r. try rewrite (sx32_of_Z nb) by lia.
    wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|].
    (* [comment removed for export] *)
    arun_to 0x89254%Z.
    (* [comment removed for export] *)
    destruct (rw_cells_cutZ a0segs _ P _ 8%nat SL) as [SLa R1]. cbn [firstn skipn cells_size csize Nat.add] in SLa, R1. change (Z.of_nat 64) with 64%Z in R1.
    destruct (rw_cells_cutZ a0segs _ _ _ 4%nat R1) as [SLb SLc]. cbn [firstn skipn cells_size csize Nat.add] in SLb, SLc. change (Z.of_nat 32) with 32%Z in SLc.
    replace (P + 64 + 32)%Z with (P + 96)%Z in SLc by lia. clear SL R1.
    fold_EH1 EH1 (gp_nInUse e).
    pose proof (A0_gm_loop cx g e Q (Z_to_bv 64 P) gp tp (ce_sp X) (Z_to_bv 64 SHF) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) F fc P FB SHE CX SEP GF AE
                  HF0 HFC FfE Ff1 Ff2 PC PB (Z.to_nat nb) 0 Jy (k80 sl) m3 m3) as LOOP. cbv zeta in LOOP.
    change (Z.to_nat 0) with 0%nat in LOOP. rewrite gp_st_0 in LOOP.
    cbn [gm_wr gm_yy gm_zPend gm_arr1 gm_mtfFreq gp_s0] in LOOP.
    enter_with LOOP;
      [st_eq| lia| lia| lia| exact LJy| exact EH1| exact AR1| exact AR2| exact UNS| exact MTF| exact YY3| exact SLb| exact MI3
      | apply munch_refl| apply wmono_refl
      | eapply (shzW_sub a0segs _ _ m m3); [exact SHe| exact MU0| a_sub_fp| lia| unfold ESTATE_SIZE; lia]
      | eapply (shzW_sub a0segs _ _ m m3); [exact SH1| exact MU0| a_sub_fp| lia| unfold ESTATE_SIZE; lia]
      | eapply (shzW_sub a0segs _ _ m m3); [exact SH2| exact MU0| a_sub_fp| lia| unfold ESTATE_SIZE; lia]
      | eapply (shzW_sub a0segs _ _ m m3); [exact SHy| exact MU0| a_sub_fp| lia| unfold ESTATE_SIZE; lia] |].
    clear LOOP. intros m4 y11 y28 y29 y31 EH1_4 AR1_4 AR2_4 UNS4 MTF4 YY4 SLb4 MI4 MU4 WM4.
    assert (EH2_4 : rw_cells a0segs m4 (E + 640) (EHEAD2 cx g e)).
    { unfold id in EH2_3. eapply rw_cells_transport; [exact EH2_3| exact MU4| exact WM4|]. cbv [disjoint_from fst snd]. unfold EHEAD2. cbn [cells_size csize Nat.add].
      split; [clear; lia|]. split; [clear - AEA1; unfold id in AEA1; lia|]. split; [| exact I]. clear - FfE. unfold id, ESTATE_SIZE in FfE. lia. }
    clear EH1 EH2_3 AR1 AR2 UNS MTF YY3 SLb MI3. transport_after_call a0segs m3 m4 MU4 WM4. clear MU4 WM4.
    unfold EHEAD2 in EH2_4.
    pose proof (gp_fin_ok e GF) as FO. cbv zeta in FO.
    pose proof (gp_st_GI e GF (Z.to_nat nb) ltac:(lia)) as G. replace (Z.of_nat (Z.to_nat nb)) with nb in G by lia.
    set (sN := gp_st e (Z.to_nat nb)) in *.
    pose proof G as G'. cps_destruct G' as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    assert (TAIL : forall arr1a mfa wra m5 (xra x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
      (if 0 <? gm_zPend sN then mtf_zrun 64%nat (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) (gm_zPend sN - 1) else (gm_arr1 sN, gm_mtfFreq sN, gm_wr sN))%Z = (arr1a, mfa, wra) ->
      EMI e arr1a mfa wra -> (gm_wr sN <= wra <= gm_wr sN + gm_zPend sN)%Z ->
      u8arr a0segs m5 A1 (zb8 arr1a ARR1_SIZE) -> u32arr a0segs m5 (E + 672) (ovw mfa (jseg J 672 1032) 258) -> mem_inv a0segs m5 ->
      munch [(E + 672, E + 1704); (A1, A1 + ARR1_SIZE)]%Z m4 m5 -> wmono a0segs m4 m5 ->
      evt a0segs Q (MS (RW xra x5 x6 x7 x10 x11 (Z_to_bv 64 wra) x13 x14 x15 x16 x17 (il_w (ce_il X)) x21 (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB)
                           (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 652)) x28 x29 x30 x31)
                         F (Z_to_bv 64 0x8957c) fc None m5 (seg_rom a0segs))).
    { intros arr1a mfa wra m5 xra x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 E1 EMa Hwra AR1_5 MTF5 MI5 MU5 WM5.
      clear AR1_4 MTF4 MI4. open_EH1 EH1_4. unfold SLOTS in SLb4. transport_after_call a0segs m4 m5 MU5 WM5. clear MU5 WM5.
      pose proof (zb8_length arr1a ARR1_SIZE ltac:(lia)) as LA5. pose proof (ovw_length mfa (jseg J 672 1032) 258 ltac:(lia)) as LM5.
      pose proof FO as FO'. fold sN in FO'. unfold gp_fin in FO'. rewrite E1 in FO'. cbn [mtf_emit] in FO'.
      cps_destruct FO' as (_ & WRN & EMf & EOBc).
      pose proof (EMI_get e arr1a mfa wra (gp_EOB e) EMa ltac:(lia)) as [Dm Rm].
      (* [comment removed for export] *)
      arun_to 0x895b8%Z. try rewrite (sx32_of_Z (nInUse + 1)) by lia.
      (* [comment removed for export] *)
      pose proof (u8arr_storeN_ok a0segs m5 A1 _ (2 * wra) 2%nat _ AR1_5 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1.
      wstep. store_addr (A1 + 2 * wra)%Z. zb8_store2 AR1_5 (2 * wra)%Z.
      lazymatch type of AR1_5 with context [wr16 _ _ (bv_unsigned ?w)] =>
        replace (bv_unsigned w) with (gp_EOB e) in AR1_5 by (rewrite ?swrap32_small by (rewrite ?swrap32_small by lia; lia); rewrite unsigned_lit by lia; lia) end.
      (* [comment removed for export] *)
      arun_to 0x895c8%Z.
      replace (E + (nInUse + 1) * 4 + 672)%Z with (E + 672 + 4 * gp_EOB e)%Z by lia.
      arun_to 0x895d8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read a0segs mm (E + 672) mfa (jseg J 672 1032) 258 (gp_EOB e) _ MTF5 ltac:(lia) Dm ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mfa (gp_EOB e))) by lia.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm (E + 672) _ (gp_EOB e) _ MTF5 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * gp_EOB e)%Z. ovw_store MTF5 (gp_EOB e) (zget mfa (gp_EOB e) + 1)%Z wval_lit.
      (* [comment removed for export] *)
      arun_to 0x89600%Z.
      (* [comment removed for export] *)
      pose proof (gm_e_spec e arr1a mfa wra E1) as Ee. rewrite Ee in K.
      unfold EHEAD1, EHEAD2 in K.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
           g_aie g_sort g_bs g_zbits g_mtf g_mtf_on] in K.
      pose proof (rw_cells_glue a0segs _ _ _ _ _ SLb4 SLc ltac:(cbn [cells_size csize Nat.add]; lia)) as SLbc.
      pose proof (rw_cells_glue a0segs _ _ _ _ _ SLa SLbc ltac:(cbn [cells_size csize Nat.add]; lia)) as SL. cbn [app] in SL.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm (ovb (gm_yy sN) Jy 256) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq
        | exact EH1_4
        | exact EH2_4
        | exact UNS4
        | unfold zincr; exact MTF5
        | exact AR1_5
        | exact AR2_4
        | exact YY4
        | rewrite ovb_length_nat; reflexivity
        | unfold cbsl_cells; rewrite H8, H16, H24, H32, H40, H64, H72, H88; exact SL
        | assumption
        | unfold cbG2_W; exact MU0
        | exact WM0 ] end. }
    (* [comment removed for export] *)
    wstep; if_cases Kz; zify_cond_z Kz.
    - (* [comment removed for export] *)
      enter_with (TAIL (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | exact (GI_EMI e nb sN G)
        | lia
        | exact AR1_4| exact MTF4| exact MI4| apply munch_refl| apply wmono_refl].
    - (* [comment removed for export] *)
      pose proof SLb4 as SLr. unfold SLOTS in SLr.
      arun_to 0x894f0%Z. clear SLr.
      try rewrite (sx32_of_Z_signed (gm_zPend sN + -1)) by lia. try rewrite (sx32_of_Z (gm_zPend sN + -1)) by lia. try rewrite (sx32_of_Z (gm_wr sN + 1)) by lia.
      enter_with (A0_gm_zrun2 cx e Q (Z_to_bv 64 P) gp tp (ce_sp X) (Z_to_bv 64 SHF) (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640)) F fc P SHE CX SEP GF AE
                    64%nat (gm_zPend sN - 1) (gm_wr sN) (gm_arr1 sN) (gm_mtfFreq sN) m4 m4);
        [ st_eq| lia| cbn; lia| lia| exact (GI_EMI e nb sN G)| exact AR1_4| exact MTF4| exact MI4| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub a0segs _ _ m m4); [exact SHe| exact MU0| a_sub_fp| lia| unfold ESTATE_SIZE; lia]
        | eapply (shzW_sub a0segs _ _ m m4); [exact SH1| exact MU0| a_sub_fp| lia| lia] |].
      intros arr1' mf' wr' m5 zt2 za1 za4 za7 zt3 Ez EM' Hwr' AR1_5 MTF5 MI5 MU5 WM5.
      pose proof (zr_cnt_bound 64 (gm_zPend sN - 1) ltac:(lia)) as ZB.
      enter_with (TAIL arr1' mf' wr' m5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with true by (symmetry; apply Z.ltb_lt; lia); exact Ez
        | exact EM'
        | lia
        | exact AR1_5| exact MTF5| exact MI5| exact MU5| exact WM5].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0CBG2.

End ACeilS1.
