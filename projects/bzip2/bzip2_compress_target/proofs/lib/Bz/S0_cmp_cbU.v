(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem CmpCut CmpCut0 CmpCutMtf CmpCutMtf0 BzCFactsGm CmpFsKit0 CmpHmKit S0_cmp_gmA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require S0_memset.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_gmZ.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutMtf0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_gmA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl.S0_memset.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0GMZ.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GF : gm_facts e.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp). Notation nb := (e_nblock e).
  Notation inUse := (e_inUse e).
  (* [comment removed for export] *)
  Notation RG ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (E + 384)) s5 (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128)) s8 s9 s10 s11 t3 t4 t5 t6).

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
  Notation gmMAPS := (S0_gm_maps cx g e Q sp gp tp s8 s9 s10 s11 F fc CX SEP GF).
  Notation gmYYINIT := (S0_gm_yyinit cx Q sp gp tp s8 s9 s10 s11 F fc).
  Notation gmZRUN2 := (S0_gm_zrun2 cx e Q sp gp tp s8 s9 s10 s11 F fc CX SEP GF).
  Notation gmLOOP := (S0_gm_loop cx g e Q sp gp tp s8 s9 s10 s11 F fc CX SEP GF).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma repeat_zero_nth' : forall n k (b : byte), nth_error (repeat (Z_to_bv 8 0) n) k = Some b -> b = Z_to_bv 8 0.
  Proof.
    intros n k b H. destruct (Nat.lt_ge_cases k n).
    - rewrite nth_error_repeat in H by lia. congruence.
    - rewrite (proj2 (nth_error_None _ _)) in H by (rewrite repeat_length; lia). discriminate.
  Qed.
  Lemma mtf_before_memset : forall segs m P p Jm N k,
    u32arr segs m P (ovw p Jm N) -> (0 <= k <= N)%Z ->
    rw_cells segs m P [CB (Z.to_nat (4 * k)) (u32s (firstn (Z.to_nat k) (ovw p Jm N)))] /\
    u32arr segs m (P + 4 * k)%Z (skipn (Z.to_nat k) (ovw p Jm N)).
  Proof.
    intros segs m P p Jm N k H Hk. pose proof (ovw_length_nat p Jm N) as L.
    rewrite <- (firstn_skipn (Z.to_nat k) (ovw p Jm N)) in H. apply (proj1 (u32arr_app segs m P _ _)) in H. destruct H as [H1 H2].
    rewrite length_firstn, L in H2. replace (P + 4 * Z.of_nat (Nat.min (Z.to_nat k) (Z.to_nat N)))%Z with (P + 4 * k)%Z in H2 by lia.
    split; [|exact H2].
    apply (proj1 (u32arr_u8arr' segs m P _)) in H1. apply (rw_cells_of_u8arr segs) in H1.
    rewrite u32s_length, length_firstn, L in H1. replace (4 * Nat.min (Z.to_nat k) (Z.to_nat N))%nat with (Z.to_nat (4 * k)) in H1 by lia. exact H1.
  Qed.
  Lemma ovw_zfill0_split : forall p Jm N k, (0 <= k <= N)%Z ->
    ovw (zfill0 (Z.to_nat k) p 0) Jm N = zw32 znew k ++ skipn (Z.to_nat k) (ovw p Jm N).
  Proof.
    intros p Jm N k Hk. apply nth_error_ext. intros i.
    pose proof (ovw_length_nat p Jm N) as L. pose proof (zw32_length_nat znew k) as Lz.
    destruct (Nat.lt_ge_cases i (Z.to_nat N)) as [Hi|Hi].
    2:{ rewrite (proj2 (nth_error_None _ _)) by (rewrite ovw_length_nat; lia). symmetry. apply (proj2 (nth_error_None _ _)).
        rewrite length_app, Lz, length_skipn, L. lia. }
    replace i with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite ovw_nth_raw by lia. rewrite zfill0_def, zfill0_get.
    destruct (Nat.lt_ge_cases i (Z.to_nat k)) as [H1|H1].
    - rewrite nth_error_app1 by lia. rewrite zw32_nth by lia. rewrite zget_znew.
      replace ((0 <=? Z.of_nat i) && (Z.of_nat i <? 0 + Z.of_nat (Z.to_nat k)))%Z%bool with true
        by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      reflexivity.
    - rewrite nth_error_app2 by lia. rewrite Lz, nth_error_skipn.
      replace (Z.to_nat k + (Z.to_nat (Z.of_nat i) - Z.to_nat k))%nat with (Z.to_nat (Z.of_nat i)) by lia.
      rewrite ovw_nth_raw by lia.
      replace ((0 <=? Z.of_nat i) && (Z.of_nat i <? 0 + Z.of_nat (Z.to_nat k)))%Z%bool with false
        by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
      reflexivity.
  Qed.
  Lemma mtf_after_memset : forall segs m P p Jm N k,
    rw_cells segs m P [CB (Z.to_nat (4 * k)) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * k)))] ->
    u32arr segs m (P + 4 * k)%Z (skipn (Z.to_nat k) (ovw p Jm N)) -> (0 <= k <= N)%Z ->
    u32arr segs m P (ovw (zfill0 (Z.to_nat k) p 0) Jm N).
  Proof.
    intros segs m P p Jm N k H1 H2 Hk. rewrite (ovw_zfill0_split p Jm N k Hk).
    apply (proj2 (u32arr_app segs m P _ _)). split.
    - eapply (zw32_init segs m P k _ H1); [lia| apply repeat_zero_nth'].
    - rewrite zw32_length_nat. replace (P + 4 * Z.of_nat (Z.to_nat k))%Z with (P + 4 * k)%Z by lia. exact H2.
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
      (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    let e' := gm_e e in
    ememN cx s0segs g e 0 m -> amem cx s0segs e m -> u8arr s0segs m (usp + 616) Jy -> Z.of_nat (length Jy) = 256%Z ->
    mem_inv s0segs m -> (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (Jy' : list byte) (t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       emem cx s0segs (g_mtf_on g) e' m' -> amem cx s0segs e' m' -> u8arr s0segs m' (usp + 616) Jy' -> Z.of_nat (length Jy') = 256%Z ->
       mem_inv s0segs m' -> munch (genMTF_W cx (usp + 616) (usp + 872)) m m' -> wmono s0segs m m' ->
       evt s0segs Q (MS (mkR (Z_to_bv 64 0x15bac) sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 672 + 4 * (e_nInUse e' + 1)))
                              (Z_to_bv 64 0) (Z_to_bv 64 3) a2 (Z_to_bv 64 (e_nMTF e')) a4 a5 a6 a7
                              (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128))
                              s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x15d90) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 t2 (Z_to_bv 64 0) a0 a1 (Z_to_bv 64 (E + 640)) a3 a4 a5 a6 a7 s5 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15b68) fc None m (seg_rom s0segs)).
  Proof.
    intros m Jy ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 e' EM AM YYu LJy MI CE SPB K. subst e'.
    openCX. try clear ME MA1 MA2 MF Mb Mf. bz_ceil; bz_params; unfold CEIL in CE. pose proof GF as GF'. cps_destruct GF' as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct (maps_facts e GF) as (NI & UB & UJ). pose proof (gp_EOB_eq e) as EE.
    cps_destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
    cps_destruct AM as (AR1 & AR2 & FTB).
    pose proof SEP as SP'. unfold cctx_sep, apart in SP'. cbv zeta in SP'. cps_destruct SP' as (_ & _ & AEF & _ & _ & _ & A1F & _).
    unfold ESTATE_SIZE, FTAB_WORDS in *.
    pose proof (zb8_length (e_arr1 e) ARR1_SIZE ltac:(lia)) as LA1. pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (zw32_length (e_ftab e) 65537 ltac:(lia)) as LFT.
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6.
    pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9.
    pose proof (munch_refl (genMTF_W cx (usp + 616) (usp + 872)) m) as MU0. unfold genMTF_W, ESTATE_SIZE in MU0.
    pose proof (wmono_refl s0segs m) as WM0.
    (* [comment removed for export] *)
    wstep.
    enter_with (gmMAPS 256%nat 0 0 (e_unseqToSeq e) m m);
      [st_eq| lia| lia| lia| lia| exact EH1| exact INU| exact UNS| exact MI| apply munch_refl| apply wmono_refl|].
    intros uns' k' m1 xa1 MK Hk' EH1_1 INU1 UNS1 MI1 MU1 WM1.
    clear EH1 INU UNS MI. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    destruct (gp_maps_surj e _ _ MK) as [-> ->]. clear MK Hk'.
    (* [comment removed for export] *)
    open_EH1 EH1_1. unfold EHEAD2 in EH2.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Km; zify_cond_z Km; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    replace ((nInUse + 2) * 4294967296 / 1073741824)%Z with (4 * (nInUse + 2))%Z.
    2:{ replace ((nInUse + 2) * 4294967296)%Z with ((4 * (nInUse + 2)) * 1073741824)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
    (* [comment removed for export] *)
    destruct (mtf_before_memset s0segs m1 (E + 672) (e_mtfFreq e) (jseg J 672 1032) 258 (nInUse + 2) MTF ltac:(lia)) as [MTFa MTFb]. clear MTF.
    pose proof (ovw_length_nat (e_mtfFreq e) (jseg J 672 1032) 258) as LMn.
    (* [comment removed for export] *)
    wstep.
    eapply evt_cut.
    { eapply (S0_memset_specZ (E + 672) (4 * (nInUse + 2)) 0); [exact MTFa | exact MI1 | reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    clear MTFa. post_call s0segs m1.
    match goal with H : rw_cells _ _ (E + 672)%Z _ |- _ => rename H into MTFz end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
    pose proof (mtf_after_memset s0segs m2 (E + 672) (e_mtfFreq e) (jseg J 672 1032) 258 (nInUse + 2) MTFz MTFb ltac:(lia)) as MTF. clear MTFz MTFb.
    replace (Z.to_nat (nInUse + 2)) with (Z.to_nat (gp_EOB e + 1)) in MTF by (rewrite EE; lia).
    change (zfill0 (Z.to_nat (gp_EOB e + 1)) (e_mtfFreq e) 0) with (gp_mtf0 e) in MTF.
    (* [comment removed for export] *)
    wstep; if_cases Kn1; zify_cond_z Kn1; [exfalso; lia|]. wstep. wstep. wstep.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ YYu) as YYc. replace (length Jy) with (Z.to_nat 256) in YYc by lia.
    pose proof (ovb_init s0segs m2 (usp + 616) 256 Jy YYc ltac:(lia)) as YY. clear YYc YYu.
    enter_with (gmYYINIT (Z.to_nat nInUse) 0 nInUse znew Jy m2 m2);
      [st_eq| lia| lia| lia| lia| exact LJy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact YY| exact MI2| apply munch_refl| apply wmono_refl|].
    intros m3 ya0 ya1 YY3 MI3 MU3 WM3. clear YY MI2. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    change (yy_init (Z.to_nat nInUse) znew 0) with (gp_yy0 e) in YY3.
    assert (DY0 : zdef (gp_yy0 e) 0 = true /\ zget (gp_yy0 e) 0 = 0%Z).
    { unfold gp_yy0. rewrite yy_init_def, yy_init_get, zget_znew.
      replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nInUse)))%Z%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      split; reflexivity. }
    destruct DY0 as [DY0 VY0].
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z nb) by lia.
    wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    pose proof (ovb_read1 s0segs m3 (usp + 616) (gp_yy0 e) Jy 256 0 _ YY3 ltac:(lia) DY0 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. rewrite VY0. try rewrite (unsigned_lit8 0) by lia. try rewrite (zxb_lit8 0) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    fold_EH1 EH1_1 (gp_nInUse e).
    assert (YY3' : u8arr s0segs m3 (usp + 616) (ovb (zset (gp_yy0 e) 0 0) Jy 256)).
    { rewrite (ovb_ext (zset (gp_yy0 e) 0 0) (gp_yy0 e) Jy 256); [exact YY3|].
      intros q Hq. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec q 0); [subst q| split; reflexivity]. rewrite DY0, VY0. split; reflexivity. }
    pose proof (gmLOOP (Z.to_nat nb) 0 Jy m3 m3) as LOOP. cbv zeta in LOOP.
    change (Z.to_nat 0) with 0%nat in LOOP. rewrite gp_st_0 in LOOP.
    cbn [gm_wr gm_yy gm_zPend gm_arr1 gm_mtfFreq gp_s0] in LOOP. rewrite VY0 in LOOP.
    bz_params.
    enter_with LOOP;
      [st_eq| lia| lia| lia| exact LJy| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact EH1_1| exact AR1| exact AR2| exact UNS1| exact MTF| exact YY3'| exact MI3
      | apply munch_refl| apply wmono_refl|].
    clear LOOP. intros m4 xa0 xt1 xt2 EH1_4 AR1_4 AR2_4 UNS4 MTF4 YY4 MI4 MU4 WM4.
    clear EH1_1 AR1 AR2 UNS1 MTF YY3 YY3' MI3. transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    pose proof (gp_fin_ok e GF) as FO. cbv zeta in FO.
    pose proof (gp_st_GI e GF (Z.to_nat nb) ltac:(lia)) as G. replace (Z.of_nat (Z.to_nat nb)) with nb in G by lia.
    set (sN := gp_st e (Z.to_nat nb)) in *.
    pose proof G as G'. cps_destruct G' as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV).
    lazymatch goal with |- evt _ _ (MS (RG _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x9 ?x10 ?x11 ?x12) _ _ _ _ _ _) =>
      rename x9 into u3; rename x10 into u4; rename x11 into u5; rename x12 into u6 end.
    (* [comment removed for export] *)
    assert (TAIL : forall arr1a mfa wra m5 (x5 x6 x7 xa1 xa2 xa4 xa5 xa6 xa7 : word) (xa0' : word),
      (if 0 <? gm_zPend sN then mtf_zrun 64%nat (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) (gm_zPend sN - 1) else (gm_arr1 sN, gm_mtfFreq sN, gm_wr sN))%Z = (arr1a, mfa, wra) ->
      EMI e arr1a mfa wra -> (gm_wr sN <= wra <= gm_wr sN + gm_zPend sN)%Z ->
      u8arr s0segs m5 A1 (zb8 arr1a ARR1_SIZE) -> u32arr s0segs m5 (E + 672) (ovw mfa (jseg J 672 1032) 258) -> mem_inv s0segs m5 ->
      munch [(E + 672, E + 1704); (A1, A1 + ARR1_SIZE)]%Z m4 m5 -> wmono s0segs m4 m5 ->
      evt s0segs Q (MS (RG (Z_to_bv 64 0x15bac) x5 x6 x7 (Z_to_bv 64 nInUse) xa0' xa1 xa2 (Z_to_bv 64 wra) xa4 xa5 xa6 xa7 (Z_to_bv 64 (E + 672)) u3 u4 u5 u6)
                         F (Z_to_bv 64 0x15d54) fc None m5 (seg_rom s0segs))).
    { intros arr1a mfa wra m5 v5 v6 v7 va1 va2 va4 va5 va6 va7 va0 E1 EMa Hwra AR1_5 MTF5 MI5 MU5 WM5.
      clear AR1_4 MTF4 MI4. open_EH1 EH1_4. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
      pose proof (zb8_length arr1a ARR1_SIZE ltac:(lia)) as LA5. pose proof (ovw_length mfa (jseg J 672 1032) 258 ltac:(lia)) as LM5.
      pose proof FO as FO'. fold sN in FO'. unfold gp_fin in FO'. rewrite E1 in FO'. cbn [mtf_emit] in FO'.
      cps_destruct FO' as (_ & WRN & EMf & EOBc).
      pose proof (EMI_get e arr1a mfa wra (gp_EOB e) EMa ltac:(lia)) as [Dm Rm].
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (nInUse + 1)) by lia. wstep. wstep.
      (* [comment removed for export] *)
      pose proof (u8arr_storeN_ok s0segs m5 A1 _ (2 * wra) 2%nat _ AR1_5 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO1.
      wstep. store_addr (A1 + 2 * wra)%Z. zb8_store2 AR1_5 (2 * wra)%Z.
      lazymatch type of AR1_5 with context [wr16 _ _ (bv_unsigned ?w)] =>
        replace (bv_unsigned w) with (gp_EOB e) in AR1_5 by (rewrite ?swrap32_small by (rewrite ?swrap32_small by lia; lia); rewrite unsigned_lit by lia; lia) end.
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (E + 672) mfa (jseg J 672 1032) 258 (gp_EOB e) _ MTF5 ltac:(lia) Dm ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mfa (gp_EOB e))) by lia.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 672) _ (gp_EOB e) _ MTF5 ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
      wstep. store_addr (E + 672 + 4 * gp_EOB e)%Z. ovw_store MTF5 (gp_EOB e) (zget mfa (gp_EOB e) + 1)%Z wval_lit.
      (* [comment removed for export] *)
      wstep. wstep. try rewrite (sx32_of_Z (wra + 1)) by lia. wstep.
      (* [comment removed for export] *)
      wstep.
      (* [comment removed for export] *)
      wstep; if_cases Kv; zify_cond_z Kv; [| exfalso; lia].
      (* [comment removed for export] *)
      pose proof (gm_e_spec e arr1a mfa wra E1) as Ee. rewrite Ee in K.
      unfold emem, amem, EHEAD1, EHEAD2 in K.
      cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
           e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
           g_aie g_sort g_bs g_zbits g_mtf g_mtf_on] in K.
      unfold FTAB_WORDS in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm (ovb (zset (gm_yy sN) 0 0) Jy 256));
        [ st_eq
        | split; [exact EH1_4|]; split; [exact INU1|]; split; [exact UNS4|]; split; [exact EH2|]; split; [unfold zincr; exact MTF5|];
          split; [exact SEL|]; split; [exact SELM|]; split; [exact LEN|]; split; [exact CODE|]; split; [exact RFQ| exact LPK]
        | split; [exact AR1_5|]; split; [exact AR2_4| exact FTB]
        | exact YY4
        | rewrite ovb_length_nat; reflexivity
        | assumption
        | exact MU0
        | exact WM0 ] end. }
    (* [comment removed for export] *)
    wstep; if_cases Kz; zify_cond_z Kz.
    - (* [comment removed for export] *)
      enter_with (TAIL (gm_arr1 sN) (gm_mtfFreq sN) (gm_wr sN) m4);
        [ st_eq
        | replace (0 <? gm_zPend sN)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | exact (GI_EMI e nb sN G)
        | lia
        | exact AR1_4| exact MTF4| exact MI4| apply munch_refl| apply wmono_refl].
    - (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z_signed (gm_zPend sN + -1)) by lia. try rewrite (sx32_of_Z (gm_zPend sN + -1)) by lia.
      wstep. wstep. try rewrite (sx32_of_Z (gm_wr sN + 1)) by lia. wstep. wstep.
      enter_with (gmZRUN2 64%nat (gm_zPend sN - 1) (gm_wr sN) (gm_arr1 sN) (gm_mtfFreq sN) m4 m4);
        [ st_eq| lia| cbn; lia| lia| exact (GI_EMI e nb sN G)| exact AR1_4| exact MTF4| exact MI4| apply munch_refl| apply wmono_refl|].
      intros arr1' mf' wr' m5 za0 za2 za4 za7 Ez EM' Hwr' AR1_5 MTF5 MI5 MU5 WM5.
      pose proof (zr_cnt_bound 64 (gm_zPend sN - 1) ltac:(lia)) as ZB.
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
  eapply (S0_gm_body cx g e Q sp gp tp s8 s9 s10 s11 F fc CX SEP GF m Jy); try eassumption.
Qed.

End ACeilS1.
End S0_cmp_gmZ.

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SegsS0 StoreFast Frame.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzArrD BzCLemmas1 CmpMem BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpSdTac CmpArith CmpArith2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCNumZ BzWalkArith4 BzCLemmasSd.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_cbT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCutBsw S0_cmp_bsx4 CmpCutCB CmpCutCBw CmpCutMtf CmpCutMtf0 CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 CmpCutSmC CmpCutSmC0 CmpCutSD CmpCutSD0 BzCFactsGm BzCFactsSmA BzCFactsSmB BzCFactsSd CmpSmKit CmpSmKit2 CmpSmKit20 CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smZ S0_cmp_smBz S0_cmp_smS S0_cmp_sdZ S0_cmp_cbT.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_cbT.S0_cmp_bsw OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutBsw OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_bsx4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutCB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutCBw OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutMtf0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmC OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmC0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit20 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_cbU.S0_cmp_gmZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBz OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_cbT.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section CBU.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
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
  Variables (e0 : est) (c0 f0 p0 i0 h0 w0 q0 : zarr) (sv : word) (lo : Z).
  Hypothesis E0 : gm_e e = e0.
  (* [comment removed for export] *)
  Hypothesis GBW : e_bw e0 = e_bw e. Hypothesis GNB : e_nblock e0 = e_nblock e.
  Hypothesis GF : gm_facts e.
  Hypothesis SFA : smA_facts e0. Hypothesis SFB : smB_facts e0 c0 f0 h0 w0 q0.
  Hypothesis SDF : sd_facts (est_C e0 c0 f0 p0 h0 w0 q0) (smA_ng e0) (smB_nsel e0 c0 f0 h0 w0 q0).
  Hypothesis Gmtf : g_mtf g = false \/ g_mtf g = true.   (* [comment removed for export] *)
  Notation nG := (smA_ng e0). Notation nSel := (smB_nsel e0 c0 f0 h0 w0 q0). Notation AL := (sm_alpha e0).
  Notation eC := (est_C e0 c0 f0 p0 h0 w0 q0). Notation eD := (est_D e0 c0 f0 p0 i0 h0 w0 q0). Notation itB := (smB_it e0 c0 f0 h0 w0 q0).
  Notation g4 := (g_mtf_on g).

  (* [comment removed for export] *)
  Definition cbU_W : list (Z * Z) :=
    [(E, E + ESTATE_SIZE); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (usp - HM_FRAME, usp + 900)]%Z.

  (* [comment removed for export] *)
  Definition cbU_W3 (wisl : word) : s3w :=
    S3W (Z_to_bv 64 37450) wisl (Z_to_bv 64 (E + 38998)) (Z_to_bv 64 (E + 51648)) (Z_to_bv 64 (flag6 nG)) (Z_to_bv 64 (nG - 1))
        (Z_to_bv 64 (4 * AL)) (Z_to_bv 64 (E + 45448 + 1032 * nG)) (Z_to_bv 64 4) (Z_to_bv 64 (A1 + 2)) (Z_to_bv 64 (E + 51648 + 16 * AL))
        (Z_to_bv 64 (E + 51640)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (usp + 616 + 4 * nG)) (Z_to_bv 64 AL) (Z_to_bv 64 (E + 45448))
        (Z_to_bv 64 3005).

  Lemma S0_cb_U : forall (Q : machine_state -> Prop) (m : word -> option byte)
      (J0 J184 Jy i16 J888 J900 : list byte) (wisl w8 w16 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 : word)
      (w576 w584 w592 w600 w608 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word)
      (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    ememN cx s0segs g e 0 m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m ->
    stk s0segs m lo usp -> (lo + HM_FRAME <= usp)%Z -> (CEIL <= lo)%Z -> (usp mod 16 = 0)%Z ->
    u8arr s0segs m usp J0 -> Z.of_nat (length J0) = 8%Z ->
    rw_cells s0segs m (usp + 8)
      [C8 w8; C8 w16; C8 wisl; C8 w32; C8 w40; C8 w48; C8 (Z_to_bv 64 (E + 51648)); C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120;
       C8 (Z_to_bv 64 (E + 37708)); C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176] ->
    u8arr s0segs m (usp + 184) J184 -> Z.of_nat (length J184) = 392%Z ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 w608] ->
    u8arr s0segs m (usp + 616) Jy -> Z.of_nat (length Jy) = 256%Z ->
    u8arr s0segs m (usp + 872) i16 -> Z.of_nat (length i16) = 16%Z ->
    u8arr s0segs m (usp + 888) J888 -> Z.of_nat (length J888) = 12%Z ->
    u8arr s0segs m (usp + 900) J900 -> Z.of_nat (length J900) = 4%Z ->
    rw_cells s0segs m (usp + 904) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) ->
    bw_ok (e_bw e0) -> (e_nblock e0 + bw_numZ (e_bw eD) <= ARR2_SIZE)%Z ->
    zb8 (zbl (e_arr2 e0) (e_nblock e0) (e_bw e0)) ARR2_SIZE = zb8 (e_arr2 e0) ARR2_SIZE ->
    (forall m' (J184' J616' Jy' i16' J888' : list byte) (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
       rw_cells s0segs m' E (EHEAD1 cx g4 (est_set_bw eC (e_bw eD))) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g4 (est_set_bw eC (e_bw eD))) ->
       u8arr s0segs m' A2 (zb8 (zbl (e_arr2 e0) (e_nblock e0) (e_bw eD)) ARR2_SIZE) ->
       u8arr s0segs m' A1 (zb8 (e_arr1 e0) ARR1_SIZE) -> u32arr s0segs m' FT (zw32 (e_ftab e0) FTAB_WORDS) ->
       u8arr s0segs m' (E + 128) (ovb (e_inUse e0) (jseg J 128 256) 256) ->
       u8arr s0segs m' (E + 384) (ovb (e_unseqToSeq e0) (jseg J 384 256) 256) ->
       u32arr s0segs m' (E + 672) (ovw (e_mtfFreq e0) (jseg J 672 1032) 258) ->
       u8arr s0segs m' (E + 1704) (ovb (it_sel itB) (jseg J 1704 18002) 18002) ->
       u8arr s0segs m' (E + 19706) (ovb (snd (smC_pm e0 c0 f0 p0 h0 w0 q0)) (jseg J 19706 18002) 18002) ->
       u8arr s0segs m' (E + 37708) (ovb (it_len itB) (jseg J 37708 1548) 1548) ->
       u32arr s0segs m' (E + 39256) (ovw (smC_code e0 c0 f0 h0 w0 q0) (jseg J 39256 6192) 1548) ->
       u32arr s0segs m' (E + 45448) (ovw (it_rfreq itB) (jseg J 45448 6192) 1548) ->
       u32arr s0segs m' (E + 51640) (ovw (it_lp itB) (jseg J 51640 4128) 1032) ->
       cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
       u8arr s0segs m' usp J0 ->
       rw_cells s0segs m' (usp + 8) (sd_lo3 cx eC nG sv (cbU_W3 wisl)) ->
       u8arr s0segs m' (usp + 184) J184' -> Z.of_nat (length J184') = 376%Z ->
       rw_cells s0segs m' (usp + 560) (sd_hi3 cx eC nG nSel (cbU_W3 wisl)) ->
       u8arr s0segs m' (usp + 616) J616' -> Z.of_nat (length J616') = 24%Z ->
       u8arr s0segs m' (usp + 640) Jy' -> Z.of_nat (length Jy') = 232%Z ->
       u8arr s0segs m' (usp + 872) i16' -> Z.of_nat (length i16') = 16%Z ->
       u8arr s0segs m' (usp + 888) J888' -> Z.of_nat (length J888') = 12%Z ->
       u8arr s0segs m' (usp + 900) J900 ->
       rw_cells s0segs m' (usp + 904) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) ->
       munch cbU_W m m' -> wmono s0segs m m' -> bw_ok (e_bw eD) ->
       evt s0segs Q (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                         F (Z_to_bv 64 0x19190) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 0) a0 a1 (Z_to_bv 64 (E + 640)) a3 a4 a5 a6 a7
                           (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 (E + 384)) s5 (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128))
                           s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x15b68) fc None m (seg_rom s0segs)).
  Proof.
    intros Q m J0 J184 Jy i16 J888 J900 wisl w8 w16 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176
           w576 w584 w592 w600 w608 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6.
    intros EMN AM CM MI ST STK CLO AL16 FJ0 LJ0 SL22 FJ184 LJ184 SL5 FJy LJy FI16 LI16 FJ888 LJ888 FJ900 LJ900 SAV BWOK ROOM ZI K.
    pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1. unfold HM_FRAME in STK. bz_ceil; bz_params; unfold CEIL in CLO.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    (* [comment removed for export] *)
    pose proof CX as CXL; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL; cbv zeta in CXL;
    cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & ME & MA1 & MA2 & MF & _ & _ & LJ & _).
    (* [comment removed for export] *)
    pose proof S0_genMTF as SG. unfold S0_genMTF_spec in SG. cbv zeta in SG.
    enter_with (SG Q cx g e m Jy ra sp gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc);
      [ st_eq | exact EMN | exact AM | exact FJy | exact LJy | exact MI | exact CX | exact SEP | exact USP1 | exact USP2 | exact GF | ].
    clear SG EMN AM FJy MI.
    intros m1 Jy1 yt0 yt1 yt2 ya2 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 EM1 AM1 FJy1 LJy1 MI1 MU1 WM1.
    rewrite E0 in EM1, AM1 |- *. unfold genMTF_W, ESTATE_SIZE in MU1.
    pose proof (munch_refl cbU_W m) as MU0. unfold cbU_W, ESTATE_SIZE, HM_FRAME in MU0. pose proof (wmono_refl s0segs m) as WM0.
    rename CM into CM0.
    transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
    unfold ESTATE_SIZE, FTAB_WORDS in IE, IA1, IA2, IFT.
    assert (CM1 : cimg_mem S0C m1 sv).
    { eapply (cimg_transportK0 S0C _ m m1 sv eq_refl CM0 MU0 WM0).
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|].
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor. }
    clear IE IA1 IA2 IFT.
    (* [comment removed for export] *)
    pose proof S0_smA as SA. unfold S0_smA_spec in SA. cbv zeta in SA.
    enter_with (SA Q cx g4 e0 m1 sv w8 w16 wisl w32 w40 w48 (Z_to_bv 64 (E + 51648)) w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176
                   w576 w584 w592 w600 w608 (Z_to_bv 64 0x15bac) sp gp tp);
      [ st_eq | reflexivity | exact EM1 | exact AM1 | exact CM1 | exact SL22 | exact SL5 | exact MI1 | exact CX | exact SEP | exact IMG
      | exact USP1 | exact USP2 | exact SFA | ].
    clear SA EM1 AM1 CM1 SL22 SL5 MI1.
    intros m2 zra zt0 zt1 zt2 zs1 za0 za1 za2 za3 za4 za5 za6 za7 zs4 zs6 zt3 zt4 zt5 zt6 EM2 AM2 CM2 SL22 SL5 MI2 MU2 WM2.
    unfold smA_W3 in MU2.
    transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    u8take FJy1 FJ616 24%Z (usp + 640)%Z. rename FJy1 into FJ640.
    name_bytes FJ616 J616 24%Z. name_bytes FJ640 J640 232%Z.
    pose proof S0_smB as SB. unfold S0_smB_spec in SB. cbv zeta in SB.
    enter_with (SB Q cx g4 e0 c0 f0 h0 w0 q0 m2 sv wisl (Z_to_bv 64 (E + 51648)) w584 J184 J616 J888 lo _ sp gp tp);
      [ st_eq | reflexivity | reflexivity | exact EM2 | exact AM2 | exact CM2 | exact SL22 | exact FJ184 | exact LJ184 | exact SL5
      | exact FJ616 | lia | exact FJ888 | exact LJ888 | exact ST | unfold HM_FRAME; lia | bz_ceil; bz_params; unfold CEIL; lia | exact AL16
      | exact MI2 | exact CX | exact SEP | exact IMG | exact USP2 | exact SFB | ].
    clear SB EM2 AM2 CM2 SL22 FJ184 SL5 FJ616 FJ888 ST MI2.
    intros m3 w584' J184' J616' J888' vra vt0 vt1 vt2 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6
           EM3 AM3 CM3 SL22 FJ184 LJ184' SL5 FJ616 LJ616' FJ888 LJ888' ST MI3 MU3 WM3.
    unfold smB_W3, HM_FRAME in MU3. clear CM3.
    transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    (* [comment removed for export] *)
    cps_destruct EM3 as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN & COD & RFQ & LNP). cps_destruct AM3 as (AR1 & AR2 & FTB).
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
         e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_A est_B] in
        INU, UNS, MTF, SEL, SLM, LEN, COD, RFQ, LNP, AR1, AR2, FTB.
    unfold FTAB_WORDS in AR1, AR2, FTB.
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6.
    pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9.
    pose proof S0_smC as SC. unfold S0_smC_spec in SC. cbv zeta in SC.
    enter_with (SC Q cx e0 c0 f0 p0 h0 w0 q0 m3 sv wisl (Z_to_bv 64 (E + 51648)) w584' J184' i16 lo _ sp gp tp);
      [ st_eq | exact SEL | exact SLM | exact LEN | exact COD | exact SL22 | exact FJ184 | exact LJ184' | exact SL5 | exact FI16 | exact LI16
      | exact ST | lia | bz_ceil; bz_params; unfold CEIL; lia | exact MI3 | exact CX | exact SEP | exact USP2 | exact SDF | ].
    clear SC SEL SLM LEN COD SL22 FJ184 SL5 FI16 ST MI3.
    intros m4 J184'' i16' xra' xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
           SEL SLM LEN COD SL22 FJ184 LJ184'' SHI FI16 LI16' ST MI4 MU4 WM4.
    unfold smC_W3 in MU4. unfold EHEAD1 in EH1. unfold EHEAD2 in EH2.
    openSEP.
    transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4 AEA1 AEA2 AEF AA12 AA2F.
    (* [comment removed for export] *)
    assert (MB : MS3 cx g4 eC nG nSel usp sv (cbU_W3 wisl) m4 i16' (e_bw e0) m4).
    { unfold MS3. cbn [e_inUse e_selectorMtf e_selector e_len e_code e_arr1 e_arr2 e_nblock e_nInUse est_C]. rewrite ZI.
      split; [unfold EHEAD1; exact EH1|]. split; [unfold EHEAD2; exact EH2|].
      split; [exact AR2|]. split; [exact AR1|]. split; [exact INU|]. split; [exact SLM|]. split; [exact SEL|]. split; [exact LEN|]. split; [exact COD|].
      split; [unfold sd_lo3; cbn [CmpCutSD.w8 CmpCutSD.w24 CmpCutSD.w48 CmpCutSD.w56 CmpCutSD.w64 CmpCutSD.w72 CmpCutSD.w80 CmpCutSD.w88 CmpCutSD.w104 CmpCutSD.w112 CmpCutSD.w120 CmpCutSD.w136 CmpCutSD.w152 CmpCutSD.w160 CmpCutSD.w168 CmpCutSD.w176 cbU_W3]; unfold smB_slots3 in SL22; cbv zeta in SL22; exact SL22|].
      split; [unfold sd_hi3; cbn [CmpCutSD.w568 cbU_W3]; unfold smC_hi3 in SHI; exact SHI|].
      split; [exact FI16|]. split; [exact MI4|]. split; [apply munch_refl| apply wmono_refl]. }
    clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SL22 SHI FI16 MI4.
    pose proof S0_smD as SD. unfold S0_smD_spec in SD. cbv zeta in SD.
    enter_with (SD Q cx g4 e0 c0 f0 p0 i0 h0 w0 q0 m4 sv (cbU_W3 wisl) i16' _ sp gp tp);
      [ st_eq | reflexivity | exact Gbs | cbn [g_zbits g_mtf_on]; rewrite GNB; exact Gzb | exact CX | exact SEP | exact USP1 | exact USP2
      | rewrite GNB; exact Hnb | exact ROOM | exact BWOK | exact LI16' | exact SDF | exact MB | ].
    clear SD MB.
    intros m5 i16'' wra wt0 wt1 wt2 ws1 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 wt3 wt4 wt5 wt6 MB' LI16'' BWD.
    cps_destruct MB' as (EH1 & EH2 & AR2 & AR1 & INU & SLM & SEL & LEN & COD & SLO & SHI & FI16 & MI5 & MU5 & WM5).
    unfold sdW3 in MU5.
    openSEP.
    transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5 AEA1 AEA2 AEF AA12 AA2F.
    cbn [e_inUse e_selectorMtf e_selector e_len e_code e_arr1 e_arr2 e_nblock e_nInUse est_C] in AR2, AR1, INU, SLM, SEL, LEN, COD.
    (* [comment removed for export] *)
    assert (CM5 : cimg_mem S0C m5 sv).
    { pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
      unfold ESTATE_SIZE, FTAB_WORDS in IE, IA1, IA2, IFT.
      eapply (cimg_transportK0 S0C _ m m5 sv eq_refl CM0 MU0 WM0).
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|].
      constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia|]. constructor. }
    (* [comment removed for export] *)
    eapply K;
      [ exact EH1 | exact EH2 | exact AR2 | exact AR1 | exact FTB | exact INU | exact UNS | exact MTF | exact SEL | exact SLM | exact LEN | exact COD
      | exact RFQ | exact LNP | exact CM5 | exact MI5 | exact ST | exact FJ0 | exact SLO | exact FJ184 | exact LJ184'' | exact SHI
      | exact FJ616 | exact LJ616' | exact FJ640 | exact LJ640 | exact FI16 | exact LI16'' | exact FJ888 | exact LJ888' | exact FJ900 | exact SAV | exact MU0 | exact WM0 | exact BWD ].
  Qed.
End CBU.

End ACeilS1.
