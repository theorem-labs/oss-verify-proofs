(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem CmpCut CmpCutMtf BzCFactsGm CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
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
(* [comment removed for export] *)
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpMsKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_cbV B0_cmp_gmA.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac box_ors := repeat match goal with H : ?a \/ ?b |- _ => change (a \/ b) with (id (a \/ b)) in H end.

Section B0CBG.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y. Hypothesis YSEP : acenv_sep X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Hypothesis GF : gm_facts e.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation nb := (e_nblock e).
  Notation EOB := (gp_EOB e). Notation nInUse := (gp_nInUse e). Notation unseq := (gp_unseq e).
  Notation ILW := (il_w (ce_il X)).
  (* [comment removed for export] *)
  Definition cbG_W : list (Z * Z) := [(E, E + 1704); (A1, A1 + ARR1_SIZE); (FB + 32, FB + 288); (P, P + 184)]%Z.
  (* [comment removed for export] *)
  Definition slG (sl : cbslB) : cbslB :=
    bset136 (bset144 (bset112 (bset128 (bset120 (bset80 (bset104 (bset96 (bset72 (bset24 (bset16 (bset152 sl
      (Z_to_bv 64 (E + 384))) (Z_to_bv 64 FB)) (Z_to_bv 64 FB)) (Z_to_bv 64 EOB)) (NOT (E + 672))) (Z_to_bv 64 (FB + 33))) (Z_to_bv 64 (FB + 34)))
      (Z_to_bv 64 1)) (Z_to_bv 64 nb)) (Z_to_bv 64 nb)) (Z_to_bv 64 1)) (Z_to_bv 64 1).

  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         cSB s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  Ltac open_EH1 H := unfold EHEAD1n, EHEAD1 in H; cbn [removelast app] in H.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac zb8_store2 ARR i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le2 ?w)) _) =>
      lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zb8_write2 segs m A a n i w ARR ltac:(lia) ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end end.

  #[local] Transparent gp_maps gp_nInUse gp_unseq.
  Lemma gp_maps_surj : forall e0 uns k, mk_maps 256 (e_inUse e0) (e_unseqToSeq e0) 0 0 = (uns, k) -> uns = gp_unseq e0 /\ k = gp_nInUse e0.
  Proof. intros e0 uns k H. unfold gp_unseq, gp_nInUse, gp_maps. rewrite H. split; reflexivity. Qed.
  #[local] Opaque gp_maps gp_nInUse gp_unseq.
  Lemma gm_e_spec : forall e0 arr1a mfa wra,
    (let s := gp_st e0 (Z.to_nat (e_nblock e0)) in
     if (0 <? gm_zPend s)%Z then mtf_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) = (arr1a, mfa, wra) ->
    gm_e e0 = EST (e_mode e0) (e_state e0) (e_avail_in_expect e0) (wr16 arr1a (2 * wra) (gp_EOB e0)) (e_arr2 e0) (e_ftab e0) (e_origPtr e0)
          (e_state_in_ch e0) (e_state_in_len e0) (e_nblock e0) (e_state_out_pos e0) (gp_nInUse e0) (e_inUse e0) (gp_unseq e0)
          (e_bw e0) (e_blockCRC e0) (e_combinedCRC e0) (e_blockNo e0) (wra + 1)%Z (zincr mfa (gp_EOB e0)) (e_selector e0) (e_selectorMtf e0)
          (e_len e0) (e_code e0) (e_rfreq e0) (e_len_pack e0).
  Proof. intros e0 arr1a mfa wra H. unfold gm_e. rewrite generateMTFValues_eq. unfold gp_fin. cbv zeta in H. rewrite H. cbn [mtf_emit fst]. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_cb_G : forall (m : word -> option byte) (sl : cbslB) (Jy : list byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s9 s10 s11 t3 t4 t5 t6 : word),
    let e' := gm_e e in
    (0 < nb)%Z ->
    q32 sl = ILW -> q88 sl = Z_to_bv 64 E -> q144 sl = Z_to_bv 64 (SHE + 13) ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> u8arr b0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
    u8arr b0segs m (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    u32arr b0segs m (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) ->
    u8arr b0segs m A1 (zb8 (e_arr1 e) ARR1_SIZE) -> u8arr b0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    u8arr b0segs m (FB + 32) Jy -> Z.of_nat (length Jy) = 256%Z ->
    rw_cells b0segs m P (cbslB_cells sl) -> mem_inv b0segs m ->
    shzW b0segs cbG_W m E (E + ESTATE_SIZE) -> shzW b0segs cbG_W m A1 (A1 + ARR1_SIZE) -> shzW b0segs cbG_W m A2 (A2 + ARR2_SIZE) ->
    shzW b0segs cbG_W m (FB + 32) (FB + 288) ->
    (forall m' (Jy' : list byte) (ra' t0' t1' t2' a0' a1' a2' a3' a5' a6' a7' s6' s7' t3' t4' t5' t6' : word),
      rw_cells b0segs m' E (EHEAD1 cx (g_mtf_on g) e') -> u8arr b0segs m' (E + 128) (ovb (e_inUse e') (jseg J 128 256) 256) ->
      u8arr b0segs m' (E + 384) (ovb (e_unseqToSeq e') (jseg J 384 256) 256) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx (g_mtf_on g) e') ->
      u32arr b0segs m' (E + 672) (ovw (e_mtfFreq e') (jseg J 672 1032) 258) ->
      u8arr b0segs m' A1 (zb8 (e_arr1 e') ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 (e_arr2 e') ARR2_SIZE) ->
      u8arr b0segs m' (FB + 32) Jy' -> Z.of_nat (length Jy') = 256%Z ->
      rw_cells b0segs m' P (cbslB_cells (slG sl)) -> mem_inv b0segs m' -> munch cbG_W m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RW ra' t0' t1' t2' a0' a1' a2' a3' (Z_to_bv 64 E) a5' a6' a7' ILW s4 (Z_to_bv 64 FB) s6' s7' (Z_to_bv 64 FB) s9 s10 s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x8a9c8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RW ra t0 t1 t2 (Z_to_bv 64 (E + 56)) a1 a2 a3 a4 a5 a6 a7 s3 s4 (Z_to_bv 64 FB) s6 (Z_to_bv 64 E) (Z_to_bv 64 FB) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a19c) fc None m (seg_rom b0segs)).
  Proof.
    intros m sl Jy ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s9 s10 s11 t3 t4 t5 t6 e' POS H32 H88 H144 EH1 INU UNS EH2 MTF AR1 AR2 YYu LJy SL MI SHe SH1 SH2 SHy K. subst e'.
    cbenv_open XOK. acenv_open YOK. cb_ranges CX.
    pose proof YSEP as YS; unfold acenv_sep, CmpFsKit.apartv, CmpFsKit0.apartv, ESTATE_SIZE in YS; cbv zeta in YS; destruct YS as (FE & F1 & F2).
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & MA16 & _).
    assert (EL124 : Z.land (E + 124) 7 = 4%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    assert (EL672 : Z.land (E + 672) 7 = 0%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    assert (EL676 : Z.land (E + 676) 7 = 4%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    assert (AL3 : Z.land A1 3 = 0%Z). { change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. clear - MA16. Z.div_mod_to_equations. lia. }
    pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct (maps_facts e GF) as (NI & UB & UJ). pose proof (gp_EOB_eq e) as EE.
    assert (HF0 : (0 < FB)%Z) by lia. assert (HFC : (FB + 352 <= CEIL)%Z) by (unfold CEIL; lia).
    assert (FfE : (FB + 352 <= E \/ E + ESTATE_SIZE <= FB)%Z) by (unfold ESTATE_SIZE; lia).
    assert (Ff1 : (FB + 352 <= A1 \/ A1 + ARR1_SIZE <= FB)%Z) by lia.
    assert (Ff2 : (FB + 352 <= A2 \/ A2 + ARR2_SIZE <= FB)%Z) by lia.
    assert (PC : (CEIL <= P)%Z) by (unfold CEIL; lia). assert (PB : (P + 184 <= 18446744073709551616)%Z) by lia.
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (AEA1 & AEA2 & _ & _ & _ & AA12 & _).
    box_ors.
    pose proof (zb8_length (e_arr1 e) ARR1_SIZE ltac:(lia)) as LA1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (ovb_length (e_inUse e) (jseg J 128 256) 256 ltac:(lia)) as LI. pose proof (ovb_length (e_unseqToSeq e) (jseg J 384 256) 256 ltac:(lia)) as LU.
    pose proof (ovw_length (e_mtfFreq e) (jseg J 672 1032) 258 ltac:(lia)) as LM.
    pose proof (munch_refl cbG_W m) as MU0. pose proof (wmono_refl b0segs m) as WM0. unfold cbG_W, ESTATE_SIZE in MU0, SHe, SH1, SH2, SHy.
    unfold cbslB_cells in SL. rewrite H32, H88, H144 in SL.
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2.
    (* [comment removed for export] *)
    brun_to 0x8a20c%Z. sh_norm. rewrite ?EL124.
    (* [comment removed for export] *)
    wstep; lit_store.
    (* [comment removed for export] *)
    brun_to 0x8a22c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (EH1n : rw_cells b0segs m1 E (EHEAD1n cx g e 0)) by (unfold EHEAD1n, EHEAD1; cbn [removelast app]; exact EH1). clear EH1.
    (* [comment removed for export] *)
    enter_with ((B0_gm_maps cx g e Q gp tp (ce_sp X) s4 s9 s10 s11 F fc P SHE CX SEP GF AE s3 (Z_to_bv 64 FB) s6 (Z_to_bv 64 FB)) 256%nat 0 0 (e_unseqToSeq e) m1 m1);
      [st_eq| lia| lia| lia| lia| exact EH1n| exact INU| exact UNS| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs cbG_W _ m m1); [exact SHe| exact MU0| unfold cbG_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia] |].
    intros uns' k' m2 xa1 xt4 xt5 xt6 MK Hk' EH1 INU1 UNS1 MI1 MU1 WM1.
    clear EH1n INU UNS MI. transport_after_call b0segs m1 m2 MU1 WM1. clear MU1 WM1.
    destruct (gp_maps_surj e _ _ MK) as [-> ->]. clear MK Hk'.
    open_EH1 EH1.
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (nInUse + 1)) by lia.
    if_cases Kn; zify_cond_z Kn; [exfalso; lia|].
    (* [comment removed for export] *)
    brun_to 0x8a308%Z.
    replace ((nInUse + 2) * 4294967296 / 1073741824)%Z with (4 * (nInUse + 2))%Z.
    2:{ replace ((nInUse + 2) * 4294967296)%Z with ((4 * (nInUse + 2)) * 1073741824)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with ((B0_gm_mfzero cx Q gp tp (ce_sp X) s4 s9 s10 s11 F fc P CX SEP s3 (Z_to_bv 64 FB) s6 (Z_to_bv 64 FB)) (Z.to_nat (nInUse + 2)) 0 (nInUse + 2) (e_mtfFreq e) mm mm);
      [st_eq| lia| lia| lia| lia| exact MTF| exact MI1| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs cbG_W _ m mm); [exact SHe| exact MU0| unfold cbG_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia] |];
      intros m3 ya1 yt4 MTF3 MI3 MU3 WM3; clear MTF MI1; transport_after_call b0segs mm m3 MU3 WM3; clear MU3 WM3 end.
    replace (Z.to_nat (nInUse + 2)) with (Z.to_nat (gp_EOB e + 1)) in MTF3 by (rewrite EE; lia).
    change (zfill0 (Z.to_nat (gp_EOB e + 1)) (e_mtfFreq e) 0) with (gp_mtf0 e) in MTF3.
    (* [comment removed for export] *)
    brun; if_cases Kn1; [ first [ apply CmpMsKit2.blez_taken in Kn1; [|lia] | zify_cond_z Kn1 ]; exfalso; lia
                        | first [ apply CmpMsKit2.blez_not_taken in Kn1; [|lia] | zify_cond_z Kn1 ] ].
    brun_to 0x8a35c%Z.
    pose proof (rw_cells_of_u8arr b0segs _ _ _ YYu) as YYc. replace (length Jy) with (Z.to_nat 256) in YYc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovb_init b0segs mm (FB + 32) 256 Jy YYc ltac:(lia)) as YY; clear YYc YYu;
      enter_with ((B0_gm_yyinit cx Q gp tp (ce_sp X) s4 s9 s10 s11 F fc P FB s3 (Z_to_bv 64 FB) s6 (Z_to_bv 64 FB)) (Z.to_nat nInUse) 0 nInUse znew Jy mm mm);
      [st_eq| lia| lia| lia| lia| exact LJy| exact HF0| exact HFC| exact YY| exact MI3| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs cbG_W _ m mm); [exact SHy| exact MU0| unfold cbG_W; a_sub_fp| lia| lia] |];
      intros m4 yt3 YY4 MI4 MU4 WM4; clear YY MI3; transport_after_call b0segs mm m4 MU4 WM4; clear MU4 WM4 end.
    change (yy_init (Z.to_nat nInUse) znew 0) with (gp_yy0 e) in YY4.
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z nb) by lia.
    if_cases Knb; [ first [ apply CmpMsKit2.blez_taken in Knb; [|lia] | zify_cond_z Knb ]; exfalso; lia
                  | first [ apply CmpMsKit2.blez_not_taken in Knb; [|lia] | zify_cond_z Knb ] ].
    (* [comment removed for export] *)
    rewrite ?AL3.
    (* [comment removed for export] *)
    brun_to 0x8a3ec%Z. wstep; lit_store.
    brun_to 0x8a410%Z. wstep; lit_store.
    brun_to 0x8a418%Z. wstep; lit_store.
    rewrite ?AL3 in *.
    try replace (Z.land 18446744073709551615 nb) with nb in * by (rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    try replace (Z.land (-1) nb) with nb in * by (rewrite Z.land_m1_l; reflexivity).
    (* [comment removed for export] *)
    destruct (rw_cells_cutZ b0segs _ P _ 10%nat SL) as [SLa R1]. cbn [firstn skipn cells_size csize Nat.add Nat.mul] in SLa, R1. change (Z.of_nat 80) with 80%Z in R1.
    destruct (rw_cells_cutZ b0segs _ _ _ 10%nat R1) as [SLb SLc]. cbn [firstn skipn cells_size csize Nat.add Nat.mul] in SLb, SLc. change (Z.of_nat 80) with 80%Z in SLc.
    replace (P + 80 + 80)%Z with (P + 160)%Z in SLc by lia. clear SL R1.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
    pose proof ((B0_gm_loop cx e Q gp tp (ce_sp X) s4 s9 s10 s11 F fc P FB SHE CX SEP GF AE HF0 HFC FfE Ff1 Ff2 PC PB) (Z.to_nat nb) 0 Jy m5 m5) as LOOP. cbv zeta in LOOP.
    change (Z.to_nat 0) with 0%nat in LOOP. rewrite gp_st_0 in LOOP.
    cbn [gm_wr gm_yy gm_zPend gm_arr1 gm_mtfFreq gp_s0] in LOOP.
    enter_with LOOP;
      [st_eq| lia| lia| lia| exact LJy| exact AR1| exact AR2| exact UNS1| exact MTF3| exact YY4| unfold SLOTS; exact SLb| exact MI4
      | apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs cbG_W _ m m5); [exact SHe| exact MU0| unfold cbG_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
      | eapply (shzW_sub b0segs cbG_W _ m m5); [exact SH1| exact MU0| unfold cbG_W; a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs cbG_W _ m m5); [exact SH2| exact MU0| unfold cbG_W; a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs cbG_W _ m m5); [exact SHy| exact MU0| unfold cbG_W; a_sub_fp| lia| lia] |].
    clear LOOP. intros m6 zs3 zs5 zs8 zt3 zt6 AR1_6 AR2_6 UNS6 MTF6 YY6 SLb6 MI6 MU6 WM6.
    clear AR1 AR2 UNS1 MTF3 YY4 SLb MI4. transport_after_call b0segs m5 m6 MU6 WM6. clear MU6 WM6.
    unfold SLOTS in SLb6.
    pose proof (gp_fin_ok e GF) as FO. cbv zeta in FO.
    pose proof (gp_st_GI e GF (Z.to_nat nb) ltac:(lia)) as G. replace (Z.of_nat (Z.to_nat nb)) with nb in G by lia.
    set (sN := gp_st e (Z.to_nat nb)) in *.
    pose proof G as G'. cps_destruct G' as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV).
    (* [comment removed for export] *)
    assert (TAIL : forall arr1a mfa wra m7 (x5 x6 x7 x12 x14 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 : word),
      (if 0 <? gm_zPend sN then mtf_zrun 64%nat (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) (gm_zPend sN - 1) else (gm_arr1 sN, gm_mtfFreq sN, gm_wr sN))%Z = (arr1a, mfa, wra) ->
      EMI e arr1a mfa wra -> (gm_wr sN <= wra <= gm_wr sN + gm_zPend sN)%Z ->
      u8arr b0segs m7 A1 (zb8 arr1a ARR1_SIZE) -> u32arr b0segs m7 (E + 672) (ovw mfa (jseg J 672 1032) 258) -> mem_inv b0segs m7 ->
      munch [(E + 672, E + 1704); (A1, A1 + ARR1_SIZE)]%Z m6 m7 -> wmono b0segs m6 m7 ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 2) (Z_to_bv 64 P) gp tp x5 x6 x7 (ce_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 (E + 676)) x12 (Z_to_bv 64 A1) x14 (Z_to_bv 64 wra) x16 x17
                              cSB x19 s4 x21 (Z_to_bv 64 (-1)) x23 x24 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x8a904) fc None m7 (seg_rom b0segs))).
    { intros arr1a mfa wra m7 x5 x6 x7 x12 x14 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 E1 EMa Hwra AR1_7 MTF7 MI7 MU7 WM7.
      clear AR1_6 MTF6 MI6. transport_after_call b0segs m6 m7 MU7 WM7. clear MU7 WM7.
      pose proof (zb8_length arr1a ARR1_SIZE ltac:(lia)) as LA7. pose proof (ovw_length mfa (jseg J 672 1032) 258 ltac:(lia)) as LM7.
      pose proof FO as FO'. fold sN in FO'. unfold gp_fin in FO'. rewrite E1 in FO'. cbn [mtf_emit] in FO'.
      cps_destruct FO' as (_ & WRN & EMf & EOBc).
      pose proof (EMI_get e arr1a mfa wra (gp_EOB e) EMa ltac:(lia)) as [Dm Rm].
      (* [comment removed for export] *)
      brun. try rewrite (sx32_of_Z (wra + 1)) by lia.
      pose proof (u8arr_storeN_ok b0segs m7 A1 _ (2 * wra) 2%nat _ AR1_7 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1.
      wstep. store_addr (A1 + 2 * wra)%Z. zb8_store2 AR1_7 (2 * wra)%Z.
      first [ rewrite (unsigned_lit (gp_EOB e)) in AR1_7 by lia
            | lazymatch type of AR1_7 with context [wr16 _ _ (bv_unsigned ?w)] =>
                replace (bv_unsigned w) with (gp_EOB e) in AR1_7 by (rewrite ?swrap32_small by (rewrite ?swrap32_small by lia; lia); rewrite unsigned_lit by lia; lia) end ].
      (* [comment removed for export] *)
      brun.
      try replace (E + 672 + (nInUse + 1) * 4)%Z with (E + 672 + 4 * gp_EOB e)%Z by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read b0segs mm (E + 672) mfa (jseg J 672 1032) 258 (gp_EOB e) _ MTF7 ltac:(lia) Dm ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mfa (gp_EOB e))) by lia.
      (* [comment removed for export] *)
      brun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok b0segs mm (E + 672) _ (gp_EOB e) _ MTF7 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * gp_EOB e)%Z. ovw_store MTF7 (gp_EOB e) (zget mfa (gp_EOB e) + 1)%Z wval_lit.
      (* [comment removed for export] *)
      brun_to 0x8a9c8%Z.
      (* [comment removed for export] *)
      pose proof (gm_e_spec e arr1a mfa wra E1) as Ee. rewrite Ee in K.
      unfold EHEAD1, EHEAD2 in K.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
           g_aie g_sort g_bs g_zbits g_mtf g_mtf_on] in K.
      pose proof (rw_cells_glue b0segs _ _ _ _ _ SLb6 SLc ltac:(cbn [cells_size csize Nat.add Nat.mul]; lia)) as SLbc.
      pose proof (rw_cells_glue b0segs _ _ _ _ _ SLa SLbc ltac:(cbn [cells_size csize Nat.add Nat.mul]; lia)) as SL. cbn [app] in SL.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm (ovb (gm_yy sN) Jy 256) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq
        | exact EH1
        | exact INU1
        | exact UNS6
        | exact EH2
        | unfold zincr; exact MTF7
        | exact AR1_7
        | exact AR2_6
        | exact YY6
        | rewrite ovb_length_nat; reflexivity
        | unfold slG, cbslB_cells; cbn [bset0 bset8 bset16 bset24 bset32 bset40 bset48 bset56 bset64 bset72 bset80 bset88 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152 bset160 bset168 bset176
                                        q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q128 q136 q144 q152 q160 q168 q176]; rewrite H32, H88; exact SL
        | assumption
        | unfold cbG_W; exact MU0
        | exact WM0 ] end. }
    (* [comment removed for export] *)
    brun; if_cases Kz; [ first [ apply CmpMsKit2.blez_taken in Kz; [|lia] | zify_cond_z Kz ]
                       | first [ apply CmpMsKit2.blez_not_taken in Kz; [|lia] | zify_cond_z Kz ] ].
    - (* [comment removed for export] *)
      enter_with (TAIL (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | exact (GI_EMI e nb sN G)
        | lia
        | exact AR1_6| exact MTF6| exact MI6| apply munch_refl| apply wmono_refl].
    - (* [comment removed for export] *)
      brun_to 0x8a7dc%Z.
      rewrite ?EL672, ?EL676.
      try rewrite (sx32_of_Z_signed (gm_zPend sN + -1)) by lia. try rewrite (sx32_of_Z (gm_zPend sN + -1)) by lia.
      enter_with ((B0_gm_zrun2 cx e Q gp tp (ce_sp X) s4 s9 s10 s11 F fc P SHE CX SEP GF AE) 64%nat (gm_zPend sN - 1) (gm_wr sN) (gm_arr1 sN) (gm_mtfFreq sN) m6 m6);
        [ st_eq| lia| cbn; lia| lia| exact (GI_EMI e nb sN G)| exact AR1_6| exact MTF6| exact MI6| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub b0segs cbG_W _ m m6); [exact SHe| exact MU0| unfold cbG_W; a_sub_fp| lia| unfold ESTATE_SIZE; lia]
        | eapply (shzW_sub b0segs cbG_W _ m m6); [exact SH1| exact MU0| unfold cbG_W; a_sub_fp| lia| lia] |].
      intros arr1' mf' wr' m7 wa2 ws3 ws7 wt3 wt4 wt6 Ez EM' Hwr' AR1_7 MTF7 MI7 MU7 WM7.
      pose proof (zr_cnt_bound 64 (gm_zPend sN - 1) ltac:(lia)) as ZB.
      enter_with (TAIL arr1' mf' wr' m7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with true by (symmetry; apply Z.ltb_lt; lia); exact Ez
        | exact EM'
        | lia
        | exact AR1_7| exact MTF7| exact MI7| exact MU7| exact WM7].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0CBG.

End ACeilS1.
