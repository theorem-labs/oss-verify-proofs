(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame SumWalkTac
  Spec ShapeLaws ExistsRun PhaseG HUImg HUTargetPre HUWorld HUWorldK
  HUReadBase HUReadStage HUReadChunk HURead0 HUReadF1 HULeafBigFile
  HUHeader_defs HULeafHeader HUHeaderK HUTargetFull.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_rng_lit : forall (i base : Z) (len : Z),
  (0 <= base < 2 ^ 64)%Z -> (0 <= i < 2 ^ 64)%Z ->
  in_rng (Z_to_bv 64 i) (Z_to_bv 64 base) len <-> (base <= i < base + len)%Z.
Proof.
  intros i base len Hb Hi. unfold in_rng. rewrite !u64_lit by lia. tauto.
Qed.

Lemma read0_outside : forall (sp0 gm : word) (L i : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  (0x354000 <= bv_unsigned gm)%Z -> (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  (0 <= L)%Z -> (0 <= i < 2 ^ 64)%Z ->
  ~ (bv_unsigned sp0 - 8388608 <= i < bv_unsigned sp0 - 128)%Z ->
  ~ (bv_unsigned gm + 32 <= i < bv_unsigned gm + 32 + L)%Z ->
  ~ (STAGE <= i < STAGE + 65536)%Z ->
  outside (Z_to_bv 64 i) (read_regions0 sp0 gm L).
Proof.
  intros sp0 gm L i Hsp Hg1 Hg2 HL Hi N1 N2 N3. unfold read_regions0, STAGE in *. cbn [outside].
  rewrite !in_rng_lit by lia. repeat split; lia.
Qed.

Lemma world0_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid can sec : Z),
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas tid can sec M0 ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas tid can sec M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid can sec RQ HL W.
  pose proof (w_sp0 _ _ _ _ _ _ _ _ _ W) as Hsp.
  pose proof (w_area_rng _ _ _ _ _ _ _ _ _ W) as Har. pose proof (w_gm_rng _ _ _ _ _ _ _ _ _ W) as Hgr.
  pose proof (w_disj _ _ _ _ _ _ _ _ _ W) as Hdj. pose proof (w_grp_def _ _ _ _ _ _ _ _ _ W) as Hdef.
  pose proof (w_area_img _ _ _ _ _ _ _ _ _ W) as Hai.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr. pose proof (rq_grows _ _ _ _ _ _ _ _ RQ) as Hgw.
  eapply world0_frame; [exact W | |].
  - intros i Hi. apply Hfr. unfold world0_fp in Hi.
    apply read0_outside; unfold STAGE; lia.
  - intros i Hi. apply Hgw. apply Hdef. exact Hi.
Qed.

Lemma main_frame_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid can sec : Z),
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas tid can sec M0 ->
  main_frame (bv_unsigned sp0) M0 -> main_frame (bv_unsigned sp0) M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid can sec RQ HL W MF.
  pose proof (w_sp0 _ _ _ _ _ _ _ _ _ W) as Hsp. pose proof (w_gm_rng _ _ _ _ _ _ _ _ _ W) as Hgr.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr.
  eapply main_frame_frame; [lia | lia | | | | exact MF].
  - intros i Hi. apply Hfr. apply read0_outside; unfold STAGE; lia.
  - (* [comment removed for export] *) apply Hfr. apply read0_outside; unfold STAGE; lia.
  - (* [comment removed for export] *) intros i Hi. apply Hfr. apply read0_outside; unfold STAGE; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Kdd0a8 (content : list byte) (fs0 : Fs) (KT : TSet) : TSet :=
  if (Z.of_nat (length content) <? 65536)%Z then t_hdr content fs0 KT
  else (* [comment removed for export] *)
       (if (Z.of_nat (length content) <? 67108864)%Z then t_hdr content fs0 KT else t_die msg_refused fs0).

(* [comment removed for export] *)
Lemma Kdd0a8_body : forall content fs0,
  t_eq (Kdd0a8 content fs0 (t_target content fs0))
       (t_body content fs0).     (* [comment removed for export] *)
Proof.
  intros content fs0. unfold Kdd0a8. rewrite <- t_body_hdr.
  destruct (Z.ltb_spec0 (Z.of_nat (length content)) 65536) as [Hs|Hb]; [apply t_eq_refl|].
  destruct (Z.ltb_spec0 (Z.of_nat (length content)) 67108864) as [Hs2|Hb2]; [apply t_eq_refl|].
  rewrite (t_body_refused content fs0) by (unfold MAX_INPUT; lia). apply t_eq_refl.
Qed.

Section FilePhase.
  Variables (sp0 p1 mb bw gm can sec : word) (R : bvmap 5 word) (M : word -> option byte).
  Variables (area brkv mas : Z) (VM : VmMaps) (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.
  Hypothesis Harea : area = (bv_unsigned mb + 4096)%Z.
  Hypothesis Hbw : bv_unsigned bw = brkv.
  Hypothesis RP : read_pre sp0 p1 mb bw gm can sec R M.
  Hypothesis W : world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas (bv_unsigned tid) (bv_unsigned can) (bv_unsigned sec) M.
  Hypothesis MF : main_frame (bv_unsigned sp0) M.
  Hypothesis VP : vm_pre VM sp0 mb bw gm.

  Let L : Z := Z.of_nat (length content).

  (* [comment removed for export] *)
  Theorem file_phase : forall mode Q (KT : TSet),
    (mode = true -> HUReadStage.oom_branch sp0 path stdin0 fs0 tid M (t_die msg_oom fs0)) ->
    (mode = true -> forall R' M' off V', oom_leaf sp0 M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xe1bf8) M' (seg_rom RSEGS)) (HUReadStage.modelG path stdin0 fs0 tid off V'))
                (t_die msg_refused fs0)) ->
    (mode = false -> (6 + hdr_cfglen content <= L < 67108864)%Z) ->
    (* [comment removed for export] *)
    (forall (k buf : Z) (V' : VmMaps) R' M',
       tgt_entry_full sp0 k buf can content V' R' M' ->
       GG RSEGS mode Q KT (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' stdin0 fs0 tid))) ->
    GG RSEGS mode Q (Kdd0a8 content fs0 KT)
       (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) (model_pre path VM stdin0 fs0 tid)).
  Proof.
    intros mode Q KT HOOM HREF HLT HTGT.
    pose proof (rp_sp0 _ _ _ _ _ _ _ _ _ RP) as Hsp.
    assert (Hvsp : valid_sp sp0) by (unfold valid_sp, sp_window_lo, sp_window_hi; lia).
    pose proof (u64_range can) as Hcanr. pose proof (u64_range sec) as Hsecr.
    destruct VP as (Vres & Vlim & Visp & Vhas & Vrest).
    unfold Kdd0a8. fold L. destruct (Z.ltb_spec0 L 65536) as [Hlt|Hge].
    - (* [comment removed for export] *)
      apply (read_k0 sp0 p1 mb bw gm can sec path content VM stdin0 fs0 tid Hfile mode Q R M _ RP Hlt).
      intros R' M' RQ.
      apply (header_phase mode Q sp0 p1 gm tid area brkv mas (bv_unsigned can) (bv_unsigned sec) content VM stdin0 fs0 R M R' M' KT Hvsp RQ).
      + eapply world0_after_read0; [exact RQ | exact Hlt | exact W].
      + eapply main_frame_after_read0; [exact RQ | exact Hlt | exact W | exact MF].
      + exact Hlt.
      + exact Hcanr.
      + exact Hsecr.
      + apply HUReadG0.map_has_In. exact Vhas.
      + intros Hm. specialize (HLT Hm). lia.
      + intros R'' TE. apply (HTGT 0%Z (bv_unsigned gm + 32)%Z VM R'' M').
        constructor.
        * exact TE.
        * eapply main_frame_after_read0; [exact RQ | exact Hlt | exact W | exact MF].
        * exists mb, bw, gm, brkv, mas, (bv_unsigned tid), (bv_unsigned sec). split; [exact Hbw|]. left.
          split; [reflexivity|]. split; [exact Hlt|]. split; [reflexivity|]. split.
          -- rewrite <- Harea. eapply world0_after_read0; [exact RQ | exact Hlt | exact W].
          -- exact (conj Vres (conj Vlim (conj Visp (conj Vhas Vrest)))).
    - (* [comment removed for export] *)
      apply (ref_big_file sp0 p1 mb bw gm can sec R M area brkv mas VM path content stdin0 fs0 tid
               Hfile ltac:(lia) Harea Hbw RP W (conj Vres (conj Vlim (conj Visp (conj Vhas Vrest)))) MF mode Q KT _ _ HOOM HREF).
      + intros Hm. specialize (HLT Hm). lia.
      + intros k B V' R' M' Hk TE. exact (HTGT k _ V' R' M' TE).
  Qed.
End FilePhase.

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
