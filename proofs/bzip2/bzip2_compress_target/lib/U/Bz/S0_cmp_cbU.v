(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpCutMtf CmpCutMtf0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0 CmpHmKit S0_cmp_gmA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_gmZ.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpHmKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_gmA.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut6.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0GMZ.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GF : gm_facts e.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp). Notation nb := (e_nblock e).
  Notation inUse := (e_inUse e).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).

  (* [comment removed for export] *)
  Ltac open_EH1 H := unfold EHEAD1n, EHEAD1 in H; cbn [removelast app] in H.
  Ltac fold_EH1 H v := lazymatch type of H with rw_cells ?sg ?mm ?A _ => change (rw_cells sg mm A (EHEAD1n cx g e v)) in H end.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _).

  (* [comment removed for export] *)
  Ltac zb8_store2 ARR i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le2 ?w)) _) =>
      lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zb8_write2 segs m A a n i w ARR ltac:(lia) ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end end.
  Notation EOB := (gp_EOB e). Notation nInUse := (gp_nInUse e). Notation unseq := (gp_unseq e).

  (* [comment removed for export] *)
  Notation gmMAPS := (S0_gm_maps cx g e Q sp gp tp F fc CX SEP GF).
  Notation gmMFZERO := (S0_gm_mfzero cx Q sp gp tp F fc CX SEP).
  Notation gmYYINIT := (S0_gm_yyinit cx Q sp gp tp F fc).
  Notation gmZRUN2 := (S0_gm_zrun2 cx e Q sp gp tp F fc CX SEP GF).
  Notation gmLOOP := (S0_gm_loop cx e Q sp gp tp F fc CX SEP GF).

  Lemma slot_u8arr : forall segs (mm : word -> option byte) A w, rw_cells segs mm A [C8 w] ->
    u8arr segs mm A (cells_bytes [C8 w]) /\ length (cells_bytes [C8 w]) = 8%nat.
  Proof.
    intros segs mm A w H. split.
    - apply (u8arr_of_rw_cells segs mm A (cells_size [C8 w])). exact (rw_cells_merge segs mm A [] [C8 w] [] H).
    - rewrite cells_bytes_length by (cbn; tauto). reflexivity.
  Qed.

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
  Lemma S0_gm_body : forall (m : word -> option byte) (Jy : list byte)
      (ra t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    let e' := gm_e e in
    ememN cx s0segs g e 0 m -> amem cx s0segs e m -> u8arr s0segs m (usp + 16) Jy -> Z.of_nat (length Jy) = 264%Z ->
    mem_inv s0segs m -> (CEIL <= usp)%Z -> (usp + 384 <= 18446744073709551616)%Z ->
    (forall m' (Jy' : list byte) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
       emem cx s0segs (g_mtf_on g) e' m' -> amem cx s0segs e' m' -> u8arr s0segs m' (usp + 16) Jy' -> Z.of_nat (length Jy') = 264%Z ->
       mem_inv s0segs m' -> munch (genMTF_W cx (usp + 16) (usp + 280)) m m' -> wmono s0segs m m' ->
       evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x16a4c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 256) t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 A1) (Z_to_bv 64 0)
                           (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                           (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (18446744073709551615 - (E + 384)))
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16640) fc None m (seg_rom s0segs)).
  Proof.
    intros m Jy ra t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 e' EM AM YYu LJy MI CE SPB K. subst e'.
    openCX. try clear ME MA2 MF Mb Mf. destruct (mod16_linq _ MA1) as [q1 HQ1]. try clear MA1.
    bz_ceil; bz_params; unfold CEIL in CE. pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct (maps_facts e GF) as (NI & UB & UJ). pose proof (gp_EOB_eq e) as EE.
    cps_destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
    cps_destruct AM as (AR1 & AR2 & FTB).
    pose proof SEP as SP'. unfold cctx_sep, apart in SP'. cbv zeta in SP'. cps_destruct SP' as (_ & _ & AEF & _ & _ & _ & A1F & _).
    unfold ESTATE_SIZE, FTAB_WORDS in *.
    pose proof (zb8_length (e_arr1 e) ARR1_SIZE ltac:(lia)) as LA1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (munch_refl (genMTF_W cx (usp + 16) (usp + 280)) m) as MU0. unfold genMTF_W, ESTATE_SIZE in MU0.
    pose proof (wmono_refl s0segs m) as WM0.
    rewrite <- (firstn_skipn 8 Jy) in YYu. apply (proj1 (u8arr_app s0segs m (usp + 16) _ _)) in YYu. destruct YYu as [SLu YYu].
    assert (LJs : length (firstn 8 Jy) = 8%nat) by (rewrite length_firstn; lia).
    assert (LJyy : Z.of_nat (length (skipn 8 Jy)) = 256%Z) by (rewrite length_skipn; lia).
    rewrite LJs in YYu. replace (usp + 16 + Z.of_nat 8)%Z with (usp + 24)%Z in YYu by lia.
    set (Jyy := skipn 8 Jy) in *.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SLu) as SL. rewrite LJs in SL. clear SLu.
    apply (rw_cells_CB8_C8 s0segs m (usp + 16) [] (firstn 8 Jy) []) in SL. cbn [app] in SL.
    enter_with (gmMAPS 256%nat 0 0 (e_unseqToSeq e) m m);
      [st_eq| lia| lia| lia| lia| exact EH1| exact INU| exact UNS| exact MI| apply munch_refl| apply wmono_refl|].
    intros uns' k' m1 xt1 xt2 MK Hk' EH1_1 INU1 UNS1 MI1 MU1 WM1.
    clear EH1 INU UNS MI. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    destruct (gp_maps_surj e _ _ MK) as [-> ->]. clear MK Hk'.
    open_EH1 EH1_1. unfold EHEAD2 in EH2.
    urun_to 0x16688%Z.
    wstep; if_cases Kn; zify_cond_z Kn; [exfalso; lia|].
    urun_to 0x166a4%Z.
    try replace ((nInUse + 2) * 4294967296 / 1073741824)%Z with (4 * (nInUse + 2))%Z
      by (replace ((nInUse + 2) * 4294967296)%Z with ((4 * (nInUse + 2)) * 1073741824)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (gmMFZERO (Z.to_nat (nInUse + 2)) 0 (nInUse + 2) (e_mtfFreq e) mm mm) end;
      [st_eq| lia| lia| lia| lia| exact MTF| exact MI1| apply munch_refl| apply wmono_refl|].
    intros m2 xt4 MTFz MI2 MU2 WM2. clear MTF MI1. lazymatch type of MU2 with munch _ ?mm _ => transport_after_call s0segs mm m2 MU2 WM2 end. clear MU2 WM2.
    replace (Z.to_nat (nInUse + 2)) with (Z.to_nat (gp_EOB e + 1)) in MTFz by (rewrite EE; lia).
    change (zfill0 (Z.to_nat (gp_EOB e + 1)) (e_mtfFreq e) 0) with (gp_mtf0 e) in MTFz.
    wstep; if_cases Kn1; zify_cond_z Kn1; [exfalso; lia|].
    wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc; [|exfalso; lia].
    urun_to 0x166dc%Z.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ YYu) as YYc. replace (length Jyy) with (Z.to_nat 256) in YYc by lia.
    pose proof (ovb_init s0segs m2 (usp + 24) 256 Jyy YYc ltac:(lia)) as YY. clear YYc YYu.
    enter_with (gmYYINIT (Z.to_nat nInUse) 0 nInUse znew Jyy m2 m2);
      [st_eq| lia| lia| lia| lia| exact LJyy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact YY| exact MI2| apply munch_refl| apply wmono_refl|].
    intros m3 YY3 MI3 MU3 WM3. clear YY MI2. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    change (yy_init (Z.to_nat nInUse) znew 0) with (gp_yy0 e) in YY3.
    wstep. try rewrite (sx32_of_Z nb) by lia.
    wstep. wstep. wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|].
    urun_to 0x16740%Z.
    replace (Z.land 18446744073709551615 nb) with nb by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    pose proof (gmLOOP (Z.to_nat nb) 0 Jyy m3 m3) as LOOP. cbv zeta in LOOP.
    change (Z.to_nat 0) with 0%nat in LOOP. rewrite gp_st_0 in LOOP.
    cbn [gm_wr gm_yy gm_zPend gm_arr1 gm_mtfFreq gp_s0] in LOOP.
    enter_with LOOP;
      [st_eq| lia| lia| lia| exact LJyy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact AR1| exact AR2| exact UNS1| exact MTFz| exact YY3| exact MI3
      | apply munch_refl| apply wmono_refl|].
    clear LOOP. intros m4 xra xa1 xs8 xs10 xs11 xt3 AR1_4 AR2_4 UNS4 MTF4 YY4 MI4 MU4 WM4.
    clear AR1 AR2 UNS1 MTFz YY3 MI3. transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    pose proof (gp_fin_ok e GF) as FO. cbv zeta in FO.
    pose proof (gp_st_GI e GF (Z.to_nat nb) ltac:(lia)) as G. replace (Z.of_nat (Z.to_nat nb)) with nb in G by lia.
    set (sN := gp_st e (Z.to_nat nb)) in *.
    pose proof G as G'. cps_destruct G' as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV).
    assert (TAIL : forall arr1a mfa wra m5 (x1 x5 x6 x7 xs1 xa1 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt5 xt6 : word),
      (if 0 <? gm_zPend sN then mtf_zrun 64%nat (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) (gm_zPend sN - 1) else (gm_arr1 sN, gm_mtfFreq sN, gm_wr sN))%Z = (arr1a, mfa, wra) ->
      EMI e arr1a mfa wra -> (gm_wr sN <= wra <= gm_wr sN + gm_zPend sN)%Z ->
      u8arr s0segs m5 A1 (zb8 arr1a ARR1_SIZE) -> u32arr s0segs m5 (E + 672) (ovw mfa (jseg J 672 1032) 258) -> mem_inv s0segs m5 ->
      munch [(E + 672, E + 1704); (A1, A1 + ARR1_SIZE)]%Z m4 m5 -> wmono s0segs m4 m5 ->
      evt s0segs Q (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 E) xs1 (Z_to_bv 64 A1) xa1 (Z_to_bv 64 (E + 672)) (NOT (E + 672)) xa4 xa5 xa6 xa7
                             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 (Z_to_bv 64 wra) xt5 xt6)
                        F (Z_to_bv 64 0x169d8) fc None m5 (seg_rom s0segs))).
    { intros arr1a mfa wra m5 x1 x5 x6 x7 xs1 xa1' xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8' xs9 xs10' xs11' xt3' xt5 xt6 E1 EMa Hwra AR1_5 MTF5 MI5 MU5 WM5.
      clear AR1_4 MTF4 MI4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
      pose proof (zb8_length arr1a ARR1_SIZE ltac:(lia)) as LA5. pose proof (ovw_length mfa (jseg J 672 1032) 258 ltac:(lia)) as LM5.
      pose proof FO as FO'. fold sN in FO'. unfold gp_fin in FO'. rewrite E1 in FO'. cbn [mtf_emit] in FO'.
      cps_destruct FO' as (_ & WRN & EMf & EOBc).
      pose proof (EMI_get e arr1a mfa wra (gp_EOB e) EMa ltac:(lia)) as [Dm Rm].
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u8arr_storeN_ok s0segs mm A1 _ (2 * wra) 2%nat _ AR1_5 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1 end.
      wstep. store_addr (A1 + 2 * wra)%Z. zb8_store2 AR1_5 (2 * wra)%Z.
      lazymatch type of AR1_5 with context [wr16 _ _ (bv_unsigned ?w)] =>
        replace (bv_unsigned w) with (gp_EOB e) in AR1_5 by (rewrite ?swrap32_small by (rewrite ?swrap32_small by lia; lia); rewrite unsigned_lit by lia; lia) end.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (E + 672) mfa (jseg J 672 1032) 258 (gp_EOB e) _ MTF5 ltac:(lia) Dm ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mfa (gp_EOB e))) by lia.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 672) _ (gp_EOB e) _ MTF5 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * gp_EOB e)%Z. ovw_store MTF5 (gp_EOB e) (zget mfa (gp_EOB e) + 1)%Z wval_lit.
      try rewrite (sx32_of_Z (wra + 1)) by lia.
      urun_to 0x16a4c%Z.
      pose proof (gm_e_spec e arr1a mfa wra E1) as Ee. rewrite Ee in K.
      unfold emem, amem, EHEAD1, EHEAD2 in K.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
           g_aie g_sort g_bs g_zbits g_mtf g_mtf_on] in K.
      unfold FTAB_WORDS in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with HS : rw_cells _ _ (usp + 16)%Z [C8 ?w] |- _ =>
          destruct (slot_u8arr s0segs mm (usp + 16) w HS) as [SLb SLl];
          assert (YYf : u8arr s0segs mm (usp + 16) (cells_bytes [C8 w] ++ ovb (gm_yy sN) Jyy 256))
            by (apply (proj2 (u8arr_app s0segs mm (usp + 16) _ _)); split; [exact SLb|]; rewrite SLl; replace (usp + 16 + Z.of_nat 8)%Z with (usp + 24)%Z by lia; exact YY4);
          enter_with (K mm (cells_bytes [C8 w] ++ ovb (gm_yy sN) Jyy 256))
        end end;
        [ st_eq
        | split; [exact EH1_1|]; split; [exact INU1|]; split; [exact UNS4|]; split; [exact EH2|]; split; [unfold zincr; exact MTF5|];
          split; [exact SEL|]; split; [exact SELM|]; split; [exact LEN|]; split; [exact CODE|]; split; [exact RFQ| exact LPK]
        | split; [exact AR1_5|]; split; [exact AR2_4| exact FTB]
        | exact YYf
        | rewrite length_app, SLl, ovb_length_nat; reflexivity
        | assumption
        | exact MU0
        | exact WM0 ]. }
    wstep; if_cases Kz; zify_cond_z Kz.
    - enter_with (TAIL (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) m4);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | exact (GI_EMI e nb sN G)
        | lia
        | exact AR1_4| exact MTF4| exact MI4| apply munch_refl| apply wmono_refl].
    - wstep. try rewrite (sx32_of_Z_signed (gm_zPend sN + -1)) by lia. try rewrite (sx32_of_Z (gm_zPend sN + -1)) by lia.
      urun_to 0x16934%Z.
      enter_with (gmZRUN2 64%nat (gm_zPend sN - 1) (gm_wr sN) (gm_arr1 sN) (gm_mtfFreq sN) m4 m4);
        [ st_eq| lia| cbn; lia| lia| exact (GI_EMI e nb sN G)| exact AR1_4| exact MTF4| exact MI4| apply munch_refl| apply wmono_refl|].
      intros arr1' mf' wr' m5 zt1 zt2 za1 za6 zs9 zt4 Ez EM' Hwr' AR1_5 MTF5 MI5 MU5 WM5.
      pose proof (zr_cnt_bound 64 (gm_zPend sN - 1) ltac:(lia)) as ZB.
      wstep.
      enter_with (TAIL arr1' mf' wr' m5);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with true by (symmetry; apply Z.ltb_lt; lia); exact Ez
        | exact EM'
        | lia
        | exact AR1_5| exact MTF5| exact MI5| exact MU5| exact WM5].
  Qed.

End S0GMZ.

Theorem S0_genMTF : S0_genMTF_spec gm_facts.
Proof.
  unfold S0_genMTF_spec. intros until fc. cbv zeta. intros EM AM YY LJy MI CX SEP CE SPB GF K.
  eapply (S0_gm_body cx g e Q sp gp tp F fc CX SEP GF m Jy); try eassumption.
Qed.

End ACeilS1.
End S0_cmp_gmZ.

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast Frame.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpCutSM CmpSdTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasSd.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutBsw S0_cmp_bsx4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCBw CmpCutMtf CmpCutMtf0 CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 CmpCutSmC CmpCutSmC0 CmpCutSD CmpCutSD0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSmA BzCFactsSmB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCFactsSd. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpSmKit CmpSmKit2 CmpSmKit20 CmpHmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_smSpec U0_cmp_smT.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSdTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCNumZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.S0_cmp_bsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCBw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmA0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmB0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSmC0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSD0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSmB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCFactsSd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSmKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSmKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSmKit20 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpHmKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbU.S0_cmp_gmZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section CBU.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 384 <= 18446744073709551616)%Z.
  (* [comment removed for export] *)
  Hypothesis IMG : cctx_img S0C cx.
  Notation FT := (c_FT cx).
  (* [comment removed for export] *)
  Ltac openSEP :=
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    cps_destruct S as (?AEA1 & ?AEA2 & ?AEF & _ & _ & ?AA12 & _ & _ & _ & ?AA2F & _); hide_disj.
  Notation SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra :=
    [C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra].
  (* [comment removed for export] *)
  Variables (e0 : est) (sv : word) (lo : Z).
  Hypothesis E0 : gm_e e = e0.
  (* [comment removed for export] *)
  Hypothesis GBW : e_bw e0 = e_bw e. Hypothesis GNB : e_nblock e0 = e_nblock e.
  Hypothesis GF : gm_facts e.
  Hypothesis SFA : smA_facts e0. Hypothesis SFB : smB_facts e0 znew znew znew znew znew.
  Hypothesis SDF : sd_facts (est_C e0 znew znew znew znew znew znew) (smA_ng e0) (smB_nsel e0 znew znew znew znew znew).
  Hypothesis Gmtf : g_mtf g = false \/ g_mtf g = true.   (* [comment removed for export] *)
  Notation nG := (smA_ng e0). Notation nSel := (smB_nsel e0 znew znew znew znew znew). Notation AL := (sm_alpha e0).
  Notation eC := (est_C e0 znew znew znew znew znew znew). Notation eD := (est_D e0 znew znew znew znew znew znew znew). Notation itB := (smB_it e0 znew znew znew znew znew).
  Notation g4 := (g_mtf_on g).

  (* [comment removed for export] *)
  Definition cbU_W : list (Z * Z) :=
    [(E, E + ESTATE_SIZE); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (usp - 6528, usp + 280)]%Z.

  (* [comment removed for export] *)

  Let SMC : sendMTF_spec := U0_sendMTF.

  Lemma S0_cb_U : forall (Q : machine_state -> Prop) (m : word -> option byte) (J0 J16 : list byte) (wisl : word)
      (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word)
      (ra t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    ememN cx s0segs g e 0 m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m ->
    stk s0segs m lo usp -> (lo + 6528 <= usp)%Z -> (CEIL <= lo)%Z -> (usp mod 16 = 0)%Z ->
    u8arr s0segs m usp J0 -> Z.of_nat (length J0) = 8%Z ->
    rw_cells s0segs m (usp + 8) [C8 wisl] ->
    u8arr s0segs m (usp + 16) J16 -> Z.of_nat (length J16) = 264%Z ->
    rw_cells s0segs m (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) ->
    bw_ok (e_bw e0) -> (e_nblock e0 + bw_numZ (e_bw eD) <= ARR2_SIZE)%Z ->
    zb8 (zbl (e_arr2 e0) (e_nblock e0) (e_bw e0)) ARR2_SIZE = zb8 (e_arr2 e0) ARR2_SIZE ->
    (forall m' (J16' : list byte) (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
       rw_cells s0segs m' E (EHEAD1 cx g4 (est_set_bw eC (e_bw eD))) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g4 (est_set_bw eC (e_bw eD))) ->
       u8arr s0segs m' A2 (zb8 (zbl (e_arr2 e0) (e_nblock e0) (e_bw eD)) ARR2_SIZE) ->
       u8arr s0segs m' A1 (zb8 (e_arr1 e0) ARR1_SIZE) -> u32arr s0segs m' FT (zw32 (e_ftab e0) FTAB_WORDS) ->
       u8arr s0segs m' (E + 128) (ovb (e_inUse e0) (jseg J 128 256) 256) ->
       u8arr s0segs m' (E + 384) (ovb (e_unseqToSeq e0) (jseg J 384 256) 256) ->
       u32arr s0segs m' (E + 672) (ovw (e_mtfFreq e0) (jseg J 672 1032) 258) ->
       u8arr s0segs m' (E + 1704) (ovb (it_sel itB) (jseg J 1704 18002) 18002) ->
       u8arr s0segs m' (E + 19706) (ovb (snd (smC_pm e0 znew znew znew znew znew znew)) (jseg J 19706 18002) 18002) ->
       u8arr s0segs m' (E + 37708) (ovb (it_len itB) (jseg J 37708 1548) 1548) ->
       u32arr s0segs m' (E + 39256) (ovw (smC_code e0 znew znew znew znew znew) (jseg J 39256 6192) 1548) ->
       u32arr s0segs m' (E + 45448) (ovw (it_rfreq itB) (jseg J 45448 6192) 1548) ->
       u32arr s0segs m' (E + 51640) (ovw (it_lp itB) (jseg J 51640 4128) 1032) ->
       cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
       u8arr s0segs m' usp J0 -> rw_cells s0segs m' (usp + 8) [C8 wisl] ->
       u8arr s0segs m' (usp + 16) J16' -> Z.of_nat (length J16') = 264%Z ->
       rw_cells s0segs m' (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) ->
       munch cbU_W m m' -> wmono s0segs m m' -> bw_ok (e_bw eD) ->
       evt s0segs Q (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                         F (Z_to_bv 64 0x16a54) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 256) t1 t2 (Z_to_bv 64 E) wisl (Z_to_bv 64 A1) (Z_to_bv 64 0)
                           (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                           (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (18446744073709551615 - (E + 384)))
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16640) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb USP1 USP2 IMG e0 sv lo E0 GNB GF SFA SFB SDF SMC.
    intros Q m J0 J16 wisl x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra ra t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
    intros EMN AM CM MI ST STK CLO AL16 FJ0 LJ0 SL1 FJ16 LJ16 SAV BWOK ROOM ZI K.
    pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1. bz_ceil; bz_params; unfold CEIL in CLO.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    (* [comment removed for export] *)
    pose proof CX as CXL; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL; cbv zeta in CXL;
    cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & ME & MA1 & MA2 & MF & _ & _ & LJ & _).
    (* [comment removed for export] *)
    pose proof S0_cmp_gmZ.S0_genMTF as SG. unfold S0_genMTF_spec in SG. cbv zeta in SG.
    enter_with (SG Q cx g e m J16 ra sp gp tp t1 t2 wisl s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc);
      [ st_eq | exact EMN | exact AM | exact FJ16 | exact LJ16 | exact MI | exact CX | exact SEP | exact USP1 | exact USP2 | exact GF | ].
    clear SG EMN AM FJ16 MI.
    intros m1 J16a yra yt0 yt1 yt2 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 EM1 AM1 FJ16a LJ16a MI1 MU1 WM1.
    rewrite E0 in EM1, AM1. unfold genMTF_W, ESTATE_SIZE in MU1.
    pose proof (munch_refl cbU_W m) as MU0. unfold cbU_W, ESTATE_SIZE in MU0. pose proof (wmono_refl s0segs m) as WM0.
    rename CM into CM0.
    transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    assert (CM1 : cimg_mem S0C m1 sv).
    { pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
      unfold ESTATE_SIZE, FTAB_WORDS in IE, IA1, IA2, IFT.
      eapply (cimg_transportK0 S0C _ m m1 sv eq_refl CM0 MU0 WM0).
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|].
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor. }
    (* [comment removed for export] *)
    wstep. wstep.
    eapply evt_cut.
    { pose proof SMC as SMC'. unfold sendMTF_spec in SMC'. cbv zeta in SMC'.
      eapply (SMC' (Z_to_bv 64 0x16a54) sp gp tp yt0 yt1 yt2 (Z_to_bv 64 E) ys1 _ ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 F fc m1 cx g4 e0 lo sv);
        [ reflexivity | reflexivity | cbn [g_bs g_mtf_on]; exact Gbs | cbn [g_zbits g_mtf_on]; rewrite GNB; exact Gzb
        | exact EM1 | exact AM1 | exact CM1 | exact MI1 | exact ST | lia | exact CLO | exact AL16 | exact CX | exact SEP | exact IMG
        | exact ZI | exact BWOK | rewrite GNB; exact Hnb | exact ROOM | exact SFA | exact SFB | exact SDF ]. }
    clear EM1 AM1 CM1 MI1 ST.
    intros ms' PO. cbv zeta in PO.
    cps_destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & EM5 & AR1 & AR2 & FTB & BWD).
    unfold ESTATE_SIZE in MU5. transport_after_call s0segs m1 m5 MU5 WM5. clear MU5 WM5.
    replace (ret_pc (Z_to_bv 64 0x16a54)) with (Z_to_bv 64 0x16a54) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (CM5 : cimg_mem S0C m5 sv).
    { pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
      unfold ESTATE_SIZE, FTAB_WORDS in IE, IA1, IA2, IFT.
      eapply (cimg_transportK0 S0C _ m m5 sv eq_refl CM0 MU0 WM0).
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|].
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor. }
    cps_destruct EM5 as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN & COD & RFQ & LNP).
    eapply K; [exact EH1| exact EH2| exact AR2| exact AR1| exact FTB| exact INU| exact UNS| exact MTF| exact SEL| exact SLM| exact LEN| exact COD
              | exact RFQ| exact LNP| exact CM5| exact MI5| exact ST5| exact FJ0| exact SL1| exact FJ16a| exact LJ16a| exact SAV| exact MU0| exact WM0| exact BWD].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End CBU.

End ACeilS1.
