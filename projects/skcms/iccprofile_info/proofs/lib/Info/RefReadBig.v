(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY14.  (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim AllocSim FileSim AgentLib MemSplit Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefNodes LibKnowFrame LibKnowXfer RefReadLib RefReadDefs RefReadBase RefReadStage.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require StepTac Hoare WalkTac LibMaskBits SumWalkTac RefMemcpyBase RefMemcpy SpecConsts RefReadChunkW Ref_code_1293c_12d58 Ref_code_1dbe0_1e5bc.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module RefReadChunk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibMaskBits OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SumWalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SpecConsts OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_1293c_12d58 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_1dbe0_1e5bc.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

Local Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mid_regs (R : bvmap 5 word) (sp0 buf len cap : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (sp0 - 128) /\ getr R 9 = Z_to_bv 64 buf /\ getr R 19 = Z_to_bv 64 len
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 RS.

(* [comment removed for export] *)
Definition loop_post_regs (R R' : bvmap 5 word) (sp0 buf len' s7v : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf /\ getr R' 23 = Z_to_bv 64 s7v
  /\ getr R' 19 = Z_to_bv 64 len'
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition loop_regions (sp0 buf len len' : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z)].

(* [comment removed for export] *)
Definition loop_post_mem (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' (loop_regions sp0 buf len len')
  /\ rdn RSEGS M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop_kept_B : forall r, In r loop_kept -> In r loopB_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopB_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma loop_kept_C : forall r, In r loop_kept -> In r loopC_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopC_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma loop_kept_D : forall r, In r loop_kept -> In r loopD_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopD_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma kept_regupd10 : forall X (v : word) r, In r loop_kept -> getr (regupd X 10 v) r = getr X r.
Proof.
  intros X v r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [rewrite getr_other by reg_neq_tac; reflexivity|]). destruct Hr.
Qed.

Lemma post_regs_compose : forall R R2 R' sp0 buf len' s7v,
  loop_post_regs R2 R' sp0 buf len' s7v ->
  (forall r, In r loop_kept -> getr R2 r = getr R r) ->
  loop_post_regs R R' sp0 buf len' s7v.
Proof.
  intros R R2 R' sp0 buf len' s7v (P2 & P9 & P23 & P19 & PK) HK.
  repeat split; try assumption. intros r Hr. rewrite (PK r Hr). apply HK, Hr.
Qed.

(* [comment removed for export] *)
Lemma frame_three : forall M (a1 a2 a3 : word) bs1 bs2 bs3,
  (bv_unsigned a1 + Z.of_nat (length bs1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) <= 2 ^ 64)%Z ->
  (bv_unsigned a3 + Z.of_nat (length bs3) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes (wbytes (wbytes M a1 bs1) a2 bs2) a3 bs3)
    [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2)); (a3, Z.of_nat (length bs3))].
Proof.
  intros M a1 a2 a3 bs1 bs2 bs3 H1 H2 H3.
  change [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2)); (a3, Z.of_nat (length bs3))]
    with ([(a1, Z.of_nat (length bs1))] ++ [(a2, Z.of_nat (length bs2))] ++ [(a3, Z.of_nat (length bs3))]).
  eapply frame_mod_trans; [apply frame_mod_wbytes; assumption|].
  eapply frame_mod_trans; apply frame_mod_wbytes; assumption.
Qed.

Section PostAlgebra.
  Variables (content : list byte) (M : word -> option byte) (sp0 buf len n : Z) (ra : word) (bs : list byte).
  Hypothesis Hlen : (0 <= len)%Z.
  Hypothesis Hn : (0 <= n <= 65536)%Z.
  Hypothesis Hbuf : (RS + 65536 <= buf)%Z.
  Hypothesis Hsp : (sp0 <= 2 ^ 63)%Z.
  Hypothesis Hsp' : (144 <= sp0)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  #[local] Notation M2 := (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra))
                                          (Z_to_bv 64 RS) bs) (Z_to_bv 64 (buf + len)) bs) (only parsing).

  (* [comment removed for export] *)
  Lemma post_mem_here : (buf + len + n <= sp0 - 136)%Z ->
    loop_post_mem content M M2 sp0 buf len (len + n).
  Proof.
    intros Hb. pose proof (length_N_to_le_bytes 8 ra) as L8. pose proof Hbuf as Hbuf'. unfold RS in Hbuf'. split.
    - eapply frame_mod_weaken; [|apply frame_three; rewrite ?L8, ?Hbl, u_small by (unfold RS in *; lia); unfold RS in *; lia].
      intros a Ha. unfold loop_regions in Ha. cbn [outside] in *. rewrite L8, Hbl.
      replace (len + n - len)%Z with n in Ha by lia.
      destruct Ha as (A1 & A2 & A3 & _). split; [exact A1|]. split; [|split; [exact A3 | exact I]].
      unfold in_rng in *. rewrite u_small in * by (unfold RS; lia). lia.
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 136)%Z ->
    loop_post_mem content M2 M' sp0 buf (len + n) len' ->
    loop_post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' [FR RD]. pose proof (length_N_to_le_bytes 8 ra) as L8. pose proof Hbuf as Hbuf'. unfold RS in Hbuf'. split.
    - eapply frame_mod_weaken.
      2: { eapply frame_mod_trans; [ | exact FR ]. apply frame_three; rewrite ?L8, ?Hbl, u_small by (unfold RS in *; lia); unfold RS in *; lia. }
      intros a (O1 & O2 & O3 & _). unfold loop_regions. cbn [outside app]. rewrite L8, Hbl. unfold in_rng in *.
      rewrite !u_small in * by (unfold RS in *; lia).
      repeat split; lia.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn RSEGS M2 M' _ (length bs) (Z_to_bv 64 (buf + len)) FR).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. unfold loop_regions. cbn [outside]. unfold in_rng.
          rewrite ?Hbl, !u_small by (unfold RS in *; lia). unfold RS in *. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

(* [comment removed for export] *)
Lemma post_mem_end : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (sp0 <= 2 ^ 63)%Z -> (144 <= sp0)%Z ->
  loop_post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl Hsp Hsp'.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2. split.
  - eapply frame_mod_weaken.
    2: { eapply frame_mod_trans; apply frame_mod_wbytes; rewrite ?L1, ?L2, u_small by lia; lia. }
    intros a (O1 & _). cbn [outside app]. rewrite L1, L2. noncert_qtauto.
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ChunkLoop.
  Context {AMB : Amb}.
  Variables (path content : list byte) (stdin0 : InputStream) (fs0 : Fs) (tid : word) (V : VmMaps).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Theorem chunk_loop : forall (fuel : nat) (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    mid_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (RS + 65536 <= buf)%Z -> (buf + cap <= sp0 - 8388608)%Z ->
    (0x7fff80000000 <= sp0 <= 2 ^ 47)%Z ->
    (len <= L)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok RSEGS M (Z_to_bv 64 RS) (Z.to_nat 65536) = true ->
    store_ok RSEGS M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->
    (* [comment removed for export] *)
    ((cap <= L)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf cap buf -> loop_post_mem content M M' sp0 buf len cap ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12b1c) M' (seg_rom RSEGS)) (modelG cap V)) K) ->
    (* [comment removed for export] *)
    ((L < cap)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf L 0 -> loop_post_mem content M M' sp0 buf len L ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12b84) M' (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG len V)) K.
  Proof.
    induction fuel as [|fuel IH]; intros R M sp0 buf len cap K Hfuel (R2 & R9 & R19 & R20 & R21 & R22) Hlen Hcap Hbuf Hbc Hsp HlenL SOKs SOKr SOKb HFULL HEND.
    { exfalso. cbn in Hfuel. lia. }
    assert (Hbuf0 : (0x308d9 <= buf)%Z) by (unfold RS in Hbuf; lia).
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    (* [comment removed for export] *)
    destruct (walkA R M (seg_rom RSEGS) sp0 len cap R2 R19 R21 R20 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A9 & A19 & AK).
    replace (Z_to_bv 64 0x12b54) with (0x12b54 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12b70))).
    assert (GR1 : mem_grows M M1) by apply wbytes_grows.
    assert (SOK1s : store_ok RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = true)
      by (eapply store_ok_mono; [exact GR1 | exact SOKs]).
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b70)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (rz_read_file RSEGS R1 (0x1e504 : word) M1 (modelG len V) W_1e504 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_1e504 E_1e504).
    - reflexivity.
    - reflexivity.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - unfold rw_bytes_max. lia.
    - lia.
    - rewrite A11, u_small by (unfold RS; lia). unfold TASK_SIZE, RS. lia.
    - rewrite A11. eapply store_ok_mono; [exact GR1|].
      eapply (store_ok_sub _ _ _ _ (Z.to_nat 65536)); [ | exact SOKr | | ]; rewrite ?u_small by (unfold RS; lia); unfold RS; lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite modelG_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (mkModelC (fds_file path (Z_to_bv 64 (len + n))) V stdin0 fs0 None (Some tid) None) with (modelG (len + n) V).
      replace (v_addi (0x1e504 : word) 4) with (0x1e508 : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 RS) bs).
      assert (GR2 : mem_grows M M2) by (subst M2; eapply mem_grows_trans; [exact GR1 | apply wbytes_grows]).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + (* [comment removed for export] *)
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        destruct (walkBC (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom RSEGS) sp0
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C23 & CK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12b84))).
        (* [comment removed for export] *)
        eapply (rz_close RSEGS R3 (0x1e504 : word) M3 (modelG (len + 0) V) W_1e504 (Z_to_bv 64 3) _ K F_1e504 E_1e504).
        * reflexivity.
        * reflexivity.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite modelG_close.
          replace (v_addi (0x1e504 : word) 4) with (0x1e508 : word) by (apply bv_eq; reflexivity).
          destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom RSEGS) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN4 |]. clear RUN4.
          replace (0x12b84 : word) with (Z_to_bv 64 0x12b84) by (apply bv_eq; reflexivity).
          apply (HEND ltac:(lia) R4 M3).
          -- (* [comment removed for export] *)
             split; [exact D2|]. split; [|split; [|split]].
             ++ rewrite (DK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (CK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite A9. exact R9.
             ++ rewrite (DK 23%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C23.
             ++ rewrite (DK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (CK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite A19. f_equal. lia.
             ++ intros r Hr. rewrite (DK r) by (apply loop_kept_D, Hr).
                rewrite (kept_regupd10 _ _ r Hr). rewrite (CK r (loop_kept_C r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr.
          -- (* [comment removed for export] *)
             subst M3 M1. rewrite <- HLe. apply post_mem_end; lia.
      + (* [comment removed for export] *)
        assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b70))).
        { subst M2. rewrite rdn_wbytes_out; [exact RD1 | rewrite !u_small by (unfold RS; lia); unfold RS; lia | rewrite u_small by lia; lia | rewrite u_small by (unfold RS; lia); unfold RS; lia]. }
        destruct (walkB1 (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom RSEGS) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; rewrite A9; exact R9)
                   ltac:(gres; rewrite (AK 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold RS in *; lia) ltac:(lia) RD2)
          as (R5 & RUN5 & B1 & B2 & B10 & B11 & B12 & B23 & B9 & B19 & BK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
        (* [comment removed for export] *)
        assert (MC : mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) n bs).
        { constructor.
          - lia.
          - lia.
          - subst M2. apply rdn_wbytes_self. rewrite u_small by (unfold RS; lia). unfold RS. lia.
          - eapply store_ok_mono; [exact GR2|].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - rewrite !u_small by (unfold RS in *; lia). unfold RS in *. lia.
          - rewrite u_small by (unfold RS; lia). unfold RS. lia.
          - rewrite u_small by lia. lia. }
        assert (RT : ret_ok (Z_to_bv 64 0x12b08)) by (apply bv_eq; vm_compute; reflexivity).
        destruct (ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) n bs (seg_rom RSEGS) MC R5 (Z_to_bv 64 0x12b08)
                    RT B1 B10 B11 B12) as (R6 & RUN6 & MK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN6 |]. clear RUN6.
        set (M4 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        assert (GR4 : mem_grows M M4) by (subst M4; eapply mem_grows_trans; [exact GR2 | apply wbytes_grows]).
        assert (KK6 : forall r, In r loop_kept -> getr R6 r = getr R r).
        { intros r Hr. rewrite (MK r) by (cbv [loop_kept In] in Hr; cbv [callee_kept In];
                                         repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]); destruct Hr).
          rewrite (BK r Hr). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        assert (C23 : getr R6 23 = Z_to_bv 64 n) by (rewrite (MK 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (C19 : getr R6 19 = Z_to_bv 64 len) by (rewrite (MK 19%bv) by (cbv; noncert_qtauto); exact B19).
        assert (C9 : getr R6 9 = Z_to_bv 64 buf) by (rewrite (MK 9%bv) by (cbv; noncert_qtauto); exact B9).
        assert (C21 : getr R6 21 = Z_to_bv 64 cap) by (rewrite (KK6 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (C2 : getr R6 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (MK 2%bv) by (cbv; noncert_qtauto); exact B2).
        destruct (walkB2 R6 M4 (seg_rom RSEGS) buf len n cap C23 C19 C9 C21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (R7 & pc7 & RUN7 & Hpc7 & E19 & E9 & E23 & EK).
        replace (Z_to_bv 64 0x12b08) with (0x12b08 : word) by (apply bv_eq; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
        assert (KK7 : forall r, In r loop_kept -> getr R7 r = getr R r).
        { intros r Hr. rewrite (EK r (loop_kept_B r Hr)). apply KK6, Hr. }
        assert (E2 : getr R7 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (EK 2%bv) by (cbv; noncert_qtauto); exact C2).
        destruct (Z.eqb_spec (len + n) cap) as [Hfull|Hmore]; subst pc7.
        * (* [comment removed for export] *)
          rewrite Hfull in E19 |- *.
          replace (0x12b1c : word) with (Z_to_bv 64 0x12b1c) by (apply bv_eq; reflexivity).
          apply (HFULL ltac:(lia) R7 M4).
          -- repeat split; assumption.
          -- subst M4 M2 M1. rewrite <- Hfull. apply post_mem_here; try lia. exact RB.
        * (* [comment removed for export] *)
          replace (0x12b54 : word) with (Z_to_bv 64 0x12b54) by (apply bv_eq; reflexivity).
          apply (IH R7 M4 sp0 buf (len + n)%Z cap K ltac:(lia)).
          -- repeat split.
             ++ exact E2.
             ++ exact E9.
             ++ exact E19.
             ++ rewrite (KK7 20%bv) by (cbv; noncert_qtauto). exact R20.
             ++ rewrite (KK7 21%bv) by (cbv; noncert_qtauto). exact R21.
             ++ rewrite (KK7 22%bv) by (cbv; noncert_qtauto). exact R22.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- eapply store_ok_mono; [exact GR4 | exact SOKs].
          -- eapply store_ok_mono; [exact GR4 | exact SOKr].
          -- eapply store_ok_mono; [exact GR4 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros HcL R' M' PR PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact KK7].
             ++ subst M4 M2 M1. eapply post_mem_compose; [ | | | | | | exact RB | | | exact PM]; lia.
          -- intros HLc R' M' PR PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact KK7].
             ++ subst M4 M2 M1. eapply post_mem_compose; [ | | | | | | exact RB | | | exact PM]; lia.
  Qed.
End ChunkLoop.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadChunk.

Module RefReadFrame.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Lemma frame_mod_split1 : forall M M' (a1 : word) (n1 : Z) rs,
  frame_mod M M' ((a1, n1) :: rs) ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' rs.
Proof.
  intros M M' a1 n1 rs [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a Ha. destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|exact Ha].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) (b3 : expr) (k3 n3 : Z),
  know_ok RSEGS E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 -> flat E (SA b3 k3) n3 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2); (adenot E (SA b3 k3), n3)] ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2) b3 k3 n3).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 b3 k3 n3 HK F1 F2 F3 FR.
  destruct (frame_mod_split1 _ _ _ _ _ FR) as (Ma & [E1 G1] & FR2).
  destruct (frame_mod_split1 _ _ _ _ _ FR2) as (Mb & [E2 G2] & [E3 G3]).
  pose proof (flat_u E _ _ F1) as U1. pose proof (flat_u E _ _ F2) as U2. pose proof (flat_u E _ _ F3) as U3.
  eapply know_ok_frame; [eapply know_ok_frame; [eapply know_ok_frame; [exact HK | exact F1 | | exact G1] | exact F2 | | exact G2] | exact F3 | | exact G3].
  - intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
  - intros x Hx. apply E2. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U2. lia.
  - intros x Hx. apply E3. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U3. lia.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x52000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

Lemma rdn1_mem_high : forall M (a : word) (b : byte),
  (0x52000 <= bv_unsigned a)%Z -> rdn RSEGS M a 1 = Some [b] -> M a = Some b.
Proof.
  intros M a b Ha H. cbn [rdn] in H. destruct (M a) as [b'|] eqn:Hm.
  - injection H as ->. reflexivity.
  - rewrite seg_rom_high in H by exact Ha. discriminate.
Qed.

(* [comment removed for export] *)
Lemma kblob_of_rdn : forall E M (e : expr) (a : word) (off n : Z) (k : nat) (bs : list byte),
  edenot E e = a -> eb E k = bs -> Z.of_nat (length bs) = n ->
  (0x52000 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned a + off)) (length bs) = Some bs ->
  kentry_ok RSEGS E M (KBlob (SA e off) (ELit n) k).
Proof.
  intros E M e a off n k bs He Hb Hn Hlo Hhi RD.
  eapply (kblob_intro RSEGS E M e a off (ELit n) k bs He Hb); try lia.
  - cbn [edenot]. rewrite u_small by lia. lia.
  - intros i Hi.
    pose proof (SeqExec.rdn_nth RSEGS M (length bs) (Z_to_bv 64 (bv_unsigned a + off)) bs (Z.to_nat i) RD ltac:(lia)) as R1.
    apply rdn1_mem_high; [rewrite u_small by lia; lia|].
    replace (Z_to_bv 64 (bv_unsigned a + off + i)) with (Z_to_bv 64 (bv_unsigned a + off) + nat_to_word (Z.to_nat i)); [exact R1|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma pres_loop_post : forall content M0 M M' (sp0 : word) (buf len len' : Z),
  pres M0 M sp0 -> loop_post_mem content M M' (bv_unsigned sp0) buf len len' ->
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (0x52000 <= buf + len)%Z -> (buf + len' <= bv_unsigned sp0 - 8388608)%Z ->
  (len <= len')%Z ->
  pres M0 M' sp0.
Proof.
  intros content M0 M M' sp0 buf len len' P [[EQ _] _] Hsp Hlo Hhi Hll x Hx.
  pose proof (u64_range sp0) as U.
  rewrite <- (P x Hx). apply EQ. unfold loop_regions. cbn [outside]. unfold in_rng. rewrite !u_small by (unfold RS; lia).
  unfold img_prot, RS in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma stack_writable_grows : forall M M' sp0, mem_grows M M' -> stack_writable M sp0 -> stack_writable M' sp0.
Proof. intros M M' sp0 G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma group_writable_grows : forall M M' gm, mem_grows M M' -> group_writable M gm -> group_writable M' gm.
Proof. intros M M' gm G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

(* [comment removed for export] *)
Lemma content_at_buf : forall content M M' (sp0 buf held : Z),
  (0 <= held <= Z.of_nat (length content))%Z -> (0x52000 <= buf)%Z -> (buf + Z.of_nat (length content) <= sp0 - 8388608)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS M (Z_to_bv 64 buf) (Z.to_nat held) = Some (pref held content) ->
  loop_post_mem content M M' sp0 buf held (Z.of_nat (length content)) ->
  rdn RSEGS M' (Z_to_bv 64 buf) (length content) = Some content.
Proof.
  intros content M M' sp0 buf held Hh Hb Hbl Hsp HELD [FR RD].
  replace (length content) with (Z.to_nat held + Z.to_nat (Z.of_nat (length content) - held))%nat by lia.
  rewrite <- (pref_dropz_app held content) at 2. rewrite <- (pref_all (Z.of_nat (length content) - held) (dropz held content))
    by (rewrite dropz_length by lia; lia).
  apply SeqExec.rdn_app.
  - rewrite (frame_mod_rdn RSEGS M M' _ (Z.to_nat held) (Z_to_bv 64 buf) FR); [exact HELD| |rewrite u_small by lia; lia].
    intros i Hi. rewrite (u_small buf) by lia. unfold loop_regions. cbn [outside]. unfold in_rng.
    rewrite !u_small by (unfold RS; lia). unfold RS. repeat split; lia.
  - replace (Z_to_bv 64 buf + nat_to_word (Z.to_nat held)) with (Z_to_bv 64 (buf + held)); [exact RD|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadFrame.

Module RefRead0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

Section R0.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  Let MPRE := model_pre path VM stdin0 fs0 tid.
  Let MPOST := model_post VM stdin0 fs0 tid.

  (* [comment removed for export] *)
  Lemma loop_entry : forall R M K,
    read_pre sp0 p1 mb gm sec cnr R M ->
    (forall R1, getr R1 9 = Z_to_bv 64 (bv_unsigned gm + 32) -> getr R1 23 = Z_to_bv 64 (bv_unsigned gm + 32) ->
       getr R1 19 = Z_to_bv 64 0 -> getr R1 22 = Z_to_bv 64 RS ->
       (forall r, In r front_kept -> getr R1 r = getr R r) ->
       realizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) MPRE) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12adc) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K RP HK. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm. pose proof (u64_range sp0) as Usp.
    destruct (walkF R M (seg_rom RSEGS) (bv_unsigned gm + 32) (rp_a0 _ _ _ _ _ _ _ _ RP) (rp_s5 _ _ _ _ _ _ _ _ RP) ltac:(lia))
      as (R1 & RUN & A9 & A23 & A19 & A22 & AK).
    replace (Z_to_bv 64 0x12adc) with (0x12adc : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN |].
    replace (0x12b54 : word) with (Z_to_bv 64 0x12b54) by (apply bv_eq; reflexivity).
    apply HK; assumption.
  Qed.

  Lemma front_loop_regs : forall R R1,
    read_pre sp0 p1 mb gm sec cnr R (fun _ => None) \/ True ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 20 = Z_to_bv 64 3 -> getr R 21 = Z_to_bv 64 65536 ->
    getr R1 9 = Z_to_bv 64 (bv_unsigned gm + 32) -> getr R1 19 = Z_to_bv 64 0 -> getr R1 22 = Z_to_bv 64 RS ->
    (forall r, In r front_kept -> getr R1 r = getr R r) ->
    mid_regs R1 (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536.
  Proof.
    intros R R1 _ Rsp Rs4 Rs5 A9 A19 A22 AK.
    split; [|split; [exact A9 | split; [exact A19 | split; [|split; [|exact A22]]]]].
    - rewrite (AK 2%bv) by (cbn; noncert_qtauto). exact Rsp.
    - rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
    - rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
  Qed.

  (* [comment removed for export] *)
  Theorem read_k0 : forall R M K,
    read_pre sp0 p1 mb gm sec cnr R M -> (L < 65536)%Z ->
    (forall R' M', read_post0 sp0 p1 gm content R M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12b84) M' (seg_rom RSEGS)) MPOST) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12adc) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K RP HL Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hgm Hgb Hst Hgr Hmw Her Hkm].
    pose proof (u64_range sp0) as Usp.
    apply (loop_entry R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop path content stdin0 fs0 tid VM Hfile (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - apply (front_loop_regs R R1 (or_intror I)); assumption.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - apply data_store_ok; unfold RS; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - intros HcL. exfalso. subst L. lia.
    - intros HLc R' M' (P2 & P9 & P23 & P19 & PK) PM. apply Hk.
      pose proof PM as [[EQ GR] RD].
      constructor.
      + exact P2.
      + rewrite (PK 3%bv) by (cbn; noncert_qtauto). rewrite (AK 3%bv) by (cbn; noncert_qtauto). exact Rgp.
      + rewrite (PK 4%bv) by (cbn; noncert_qtauto). rewrite (AK 4%bv) by (cbn; noncert_qtauto). exact Rtp.
      + rewrite (PK 8%bv) by (cbn; noncert_qtauto). rewrite (AK 8%bv) by (cbn; noncert_qtauto). exact Rs0.
      + exact P9.
      + rewrite (PK 18%bv) by (cbn; noncert_qtauto). rewrite (AK 18%bv) by (cbn; noncert_qtauto). exact Rs2.
      + rewrite P19. subst L. reflexivity.
      + rewrite (PK 20%bv) by (cbn; noncert_qtauto). rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (PK 21%bv) by (cbn; noncert_qtauto). rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
      + rewrite (PK 22%bv) by (cbn; noncert_qtauto). exact A22.
      + exact P23.
      + intros r Hr. cbv [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
          (rewrite PK by (cbn; noncert_qtauto); rewrite AK by (cbn; noncert_qtauto); reflexivity).
      + (* [comment removed for export] *)
        intros a (O1 & O2 & O3 & _). apply EQ. unfold loop_regions. cbn [outside]. unfold in_rng in *.
        rewrite !u_small in * by (unfold RS; lia).
        subst L. unfold RS in *. repeat split; lia.
      + exact GR.
      + (* [comment removed for export] *)
        subst L. eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned gm + 32) 0); try lia; [|exact PM].
        rewrite pref_0. reflexivity.
      + eapply stack_writable_grows; [exact GR | exact Hst].
      + eapply group_writable_grows; [exact GR | exact Hgr].
  Qed.

  (* [comment removed for export] *)
  Theorem read_full0 : forall R M K (e : word),
    read_pre sp0 p1 mb gm sec cnr R M -> (65536 <= L)%Z ->
    rdn RSEGS M (Z_to_bv 64 0x30944) 4 = Some (word_to_le_bytes 4 e) ->
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (forall R' M', full0 sp0 p1 mb gm L e sec cnr content M R' M' ->
       stack_writable M' sp0 ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12b1c) M' (seg_rom RSEGS)) (modelG path stdin0 fs0 tid 65536 VM)) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12adc) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K e RP HL He Hpage0 Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hgm Hgb Hst Hgr Hmw Her Hkm].
    pose proof (u64_range sp0) as Usp.
    apply (loop_entry R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop path content stdin0 fs0 tid VM Hfile (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - apply (front_loop_regs R R1 (or_intror I)); assumption.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - apply data_store_ok; unfold RS; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - intros HcL R' M' (P2 & P9 & P23 & P19 & PK) PM. pose proof PM as [[EQ GR] RD]. apply Hk.
      2:{ eapply stack_writable_grows; [exact GR | exact Hst]. }
      split.
      2:{ eapply (pres_loop_post content M M M' sp0); [apply pres_refl | exact PM | lia | lia | lia | lia]. }
      exists (junk_vals R'). split; [apply junk_vals_length|].
      set (E := ENV_RD sp0 p1 mb gm L (Z_to_bv 64 0) e sec cnr (junk_vals R') content).
      split.
      + (* [comment removed for export] *)
        apply (sr_GROW_regs sp0 p1 mb gm L (Z_to_bv 64 0) e sec cnr content R' (gmx 32) (bv_unsigned gm + 32) 65536 65536
                 (lr_gmx _ _ _ _ _ _ _ _ _ _ _ 32));
          try assumption.
        * rewrite (PK 3%bv) by (cbn; noncert_qtauto). rewrite (AK 3%bv) by (cbn; noncert_qtauto). exact Rgp.
        * rewrite (PK 4%bv) by (cbn; noncert_qtauto). rewrite (AK 4%bv) by (cbn; noncert_qtauto). exact Rtp.
        * rewrite (PK 8%bv) by (cbn; noncert_qtauto). rewrite (AK 8%bv) by (cbn; noncert_qtauto). exact Rs0.
        * rewrite (PK 18%bv) by (cbn; noncert_qtauto). rewrite (AK 18%bv) by (cbn; noncert_qtauto). exact Rs2.
        * rewrite (PK 20%bv) by (cbn; noncert_qtauto). rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
        * rewrite (PK 21%bv) by (cbn; noncert_qtauto). rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
        * rewrite (PK 22%bv) by (cbn; noncert_qtauto). exact A22.
      + (* [comment removed for export] *)
        assert (KG : know_ok RSEGS E M kn_G0).
        { unfold kn_G0. apply (proj2 (know_ok_app _ _ _ _ _)).
          split; [| apply (know_ok_noblob_irrel RSEGS _ (blobs_ev []) (gblobs content) M kn_M1 eq_refl
                                 (Hkm sp0 p1 (Z_to_bv 64 L) (Z_to_bv 64 0) e (junk_vals R') []))].
          unfold know_ok.
          repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
            change (ev E 0) with sp0; change (ev E 1) with p1; change (ev E 2) with mb; change (ev E 3) with gm; change (ev E 6) with e;
            unfold flat, estart, LA, BAND, CEIL; cbn [a_base a_off edenot];
            change (ev E 0) with sp0; change (ev E 2) with mb; change (ev E 3) with gm;
            try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
          - split; [lia | exact (proj2 Hsp)].
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 0) with sp0.
            replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia. apply Hst; lia.
          - lia.
          - split; [lia | exact (proj2 (proj2 Hb))].
          - lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with mb.
            apply Hmw; lia.
          - split; [lia | exact (proj2 (proj2 Hgm))].
          - lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 3) with gm.
            rewrite Z.add_0_r. apply Hgr; lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot].
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
            replace (0 + 131072 + d)%Z with (131072 + d)%Z by lia. apply data_store_ok; lia.
          - split; [lia|]. split; [lia|]. unfold adenot, v_addi. cbn [a_base a_off edenot].
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact He.
          - split; [lia|]. split; [lia|]. exact Hpage0. }
        (* [comment removed for export] *)
        assert (KG' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn_G0 (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 3) 32 65536)).
        { apply (know_ok_frame3 E M M' kn_G0 (EVar 0) (-136) 8 (ELit 0) 0x208d9 65536 (EVar 3) 32 65536 KG).
          - apply flat_intro; cbn [edenot]; change (ev E 0) with sp0; lia.
          - apply flat_intro; cbn [edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
          - apply flat_intro; cbn [edenot]; change (ev E 3) with gm; lia.
          - unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 0) with sp0. change (ev E 3) with gm.
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
            replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
            replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
            replace 65536%Z with (65536 - 0)%Z at 3 by lia.
            replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + 0)%Z by lia. exact (proj1 PM). }
        assert (EQK : kn_frame (kn_frame (kn_frame kn_G0 (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 3) 32 65536 = kn_G0)
          by (vm_compute; reflexivity).
        rewrite EQK in KG'. clear KG EQK.
        (* [comment removed for export] *)
        assert (KB : kentry_ok RSEGS E M' (KBlob (GMA 32) (ELit 65536) 0%nat)).
        { unfold GMA. apply (kblob_of_rdn E M' (EVar 3) gm 32 65536 0%nat (pref 65536 content)).
          - reflexivity.
          - cbn [eb E ENV_RD]. rewrite <- (gblobs_fb 0) by lia. reflexivity.
          - pose proof (pref_length 65536 content ltac:(lia)). subst L. lia.
          - lia.
          - lia.
          - pose proof (pref_length 65536 content ltac:(lia)) as PL.
            replace (length (pref 65536 content)) with (Z.to_nat (65536 - 0)) by (subst L; lia).
            replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + 0)%Z by lia.
            rewrite RD. rewrite dropz_0. f_equal. }
        unfold kn_FULL0. apply (proj2 (know_ok_app _ _ _ _ _)). split; [exact KG'|].
        apply know_ok_cons; [exact KB | apply Forall_nil].
    - intros HLc. exfalso. subst L. lia.
  Qed.
End R0.
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefRead0.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require StreamSim MallocDefs RefEnframeBase RefEnframe RefGetMeta.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfWalkBz.

Module RefReadG0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition RFUEL : nat := 5000.
Definition RSTOPS : list Z :=
  [0x1dbe0; 0x1dfe4; 0x1e0dc; 0x1e120; 0x12f28; 0x18348; 0x16f74; 0x16a60; 0x12b84; 0x12cf0; 0x12cd0; 0x12b1c; 0x12b54]%Z.
Definition scr0 : scripts := SCR [] [] [].
Definition scrT : scripts := SCR [true] [] [].
End WithFP1.


#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP2. Context {FP : PropExec.FPState}.
Lemma bv_add_0_l : forall x : word, (Z_to_bv 64 0 + x)%bv = x.
Proof. intros x. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
End WithFP2.


(* [comment removed for export] *)
Ltac kwr_solve HK :=
  lazymatch goal with |- store_ok _ _ (adenot _ (SA ?b ?k)) ?m = true =>
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let i := kidx kn (is_kwr_cov b k 1%Z) in
      eapply (kwr_store_ok segs E M kn i b _ _ k m HK eq_refl); [lia | try lia]
    end end.

Section WithFP3. Context {FP : PropExec.FPState}.
Lemma lxor_m1_bound : forall x : Z, (0 <= x < 2 ^ 64)%Z -> (x <> 2 ^ 64 - 1)%Z ->
  (0 < Z.lxor x (2 ^ 64 - 1) < 2 ^ 64)%Z.
Proof.
  intros x Hx Hne.
  assert (NZ : Z.lxor x (2 ^ 64 - 1) <> 0%Z) by (intros H0; apply Z.lxor_eq in H0; lia).
  assert (NN : (0 <= Z.lxor x (2 ^ 64 - 1))%Z) by (apply (proj2 (Z.lxor_nonneg _ _)); lia).
  split; [lia|].
  destruct (Z.eq_dec x 0) as [->|Hx0].
  - rewrite Z.lxor_0_l. lia.
  - apply (proj2 (Z.log2_lt_pow2 (Z.lxor x (2 ^ 64 - 1)) 64 ltac:(lia))).
    eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
    apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))); lia | apply (proj1 (Z.log2_lt_pow2 (2 ^ 64 - 1) 64 ltac:(lia))); lia].
Qed.

Lemma xor_m1_ne0 : forall E (b : expr),
  (bv_unsigned (edenot E b) < 2 ^ 64 - 1)%Z ->
  branch_taken BC_NE (edenot E (EAlu ALU_XOR b (ELit (-1)))) (edenot E (ELit 0)) = true.
Proof.
  intros E b Hb. cbn [edenot]. rewrite alu_xor. unfold v_xor. cbn [branch_taken].
  apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  pose proof (u64_range (edenot E b)) as Hr. set (x := edenot E b) in *.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1)%Z by (vm_compute; reflexivity).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  pose proof (lxor_m1_bound (bv_unsigned x) Hr ltac:(lia)) as HB.
  rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition is_kzero_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA c kk) (ELit l) => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + l) && Z.ltb l (2 ^ 64) && Z.leb 0 l
  | _ => false
  end.

Lemma kzero_byte : forall segs E M kn i b kk l (k : Z),
  know_ok segs E M kn -> nth_error kn i = Some (KZero (SA b kk) (ELit l)) ->
  (0 <= l < 2 ^ 64)%Z -> (kk <= k < kk + l)%Z ->
  M (Z_to_bv 64 (bv_unsigned (edenot E b) + k)) = Some (Z_to_bv 8 0).
Proof.
  intros segs E M kn i b kk l k HK Hn Hl Hk.
  pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. destruct H as [Hf Hz].
  unfold elenZ, estart in Hz. cbn [a_base a_off edenot] in Hz. rewrite u_small in Hz by lia.
  replace (bv_unsigned (edenot E b) + k)%Z with (bv_unsigned (edenot E b) + kk + (k - kk))%Z by lia.
  apply Hz. lia.
Qed.
End WithFP3.


Ltac kzero_at HK b k H :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    let i := kidx kn (is_kzero_cov b k 1%Z) in
    lazymatch eval vm_compute in (nth_error kn i) with
    | Some (KZero (SA _ ?kk) (ELit ?l)) =>
        pose proof (kzero_byte segs E M kn i b kk l k HK eq_refl ltac:(lia) ltac:(lia)) as H
    end end.

Section WithFP4. Context {FP : PropExec.FPState}.
Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Lemma kimg_none : forall segs E M kn i lo hi,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  forall a, (lo <= a < hi)%Z -> M (Z_to_bv 64 a) = None.
Proof.
  intros segs E M kn i lo hi HK Hn a Ha.
  pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. apply (proj2 (proj2 H)). exact Ha.
Qed.



(* [comment removed for export] *)
Definition gm_kept : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma gm_keeps_kept : forall a b, gm_keeps a b -> forall r : reg, In r gm_kept -> getr b r = getr a r.
Proof.
  intros a b K r Hr. apply K. unfold gm_clob. intros Hc.
  cbv [gm_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbv [In] in Hc; intuition discriminate|]). exact Hr.
Qed.
Lemma gm_kept_no0 : ~ In (0%bv : reg) gm_kept.
Proof.
  unfold gm_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Section G0.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Lemma map_has_of_In : forall maps (a n : word), In (a, n) maps -> map_has maps a n = true.
  Proof.
    intros maps a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|].
    cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
  Qed.

  Lemma In_map_has : forall maps (a n : word), map_has maps a n = true -> In (a, n) maps.
  Proof.
    intros maps a n H. unfold map_has in H. apply existsb_exists in H as ([b m] & Hin & Hb).
    cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
    assert (b = a) by (apply bv_eq; unfold bv_eqb in H1; lia).
    assert (m = n) by (apply bv_eq; unfold bv_eqb in H2; lia). subst. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Definition half1_branch (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half 1 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 1) V)) K.

  (* [comment removed for export] *)
  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  (* [comment removed for export] *)
  Ltac save_know HK := pose proof (conj HK I) as HKb.

  (* [comment removed for export] *)
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Theorem grow0 : forall R M (e : word) M0 K,
    full0 sp0 p1 mb gm L e sec cnr content M0 R M -> vm_pre VM sp0 mb gm ->
    (65536 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x52000 <= bv_unsigned gm)%Z -> (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned gm mod 4096 = 0)%Z ->
    half1_branch M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 65536 VM)) K.
  Proof.
    intros R M e M0 K F0 VP HL64 Hsp Hmb0 Hmb1 Hmba Hgm0 Hgm1 Hgma HK1.
    assert (Hgm : (0x52000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z /\ (bv_unsigned gm mod 4096 = 0)%Z) by (repeat split; assumption).
    assert (Hmb : (0x52000 <= bv_unsigned mb)%Z /\ (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z /\ (bv_unsigned mb mod 4096 = 0)%Z) by (repeat split; assumption).
    pose proof (proj1 Hsp) as HspR.
    destruct F0 as ((extra & HLx & HR & HK) & PRES).
    rename M0 into Minit.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L (Z_to_bv 64 0) e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    norm_know HK. norm_regs HR.
    assert (EB1 : gblobs content 0%nat = pref 65536 content) by (apply (gblobs_fb 0); lia).
    assert (RL1 : length (pref 65536 content) = Z.to_nat 65536)
      by (pose proof (pref_length 65536 content ltac:(lia)); lia).
    (* [comment removed for export] *)
    pose (R0 := tt). pose (M0 := M).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      destruct VP as (Vres & Vlim & Vsp & Vhas & Vsz & Vlen & Vlive & Vcont & Vseps).
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 131092 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 131092) with 135168%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B HG.
        change (page_round_up_Z 131092) with 135168%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, rsegs_reserved in GF. rewrite Vsp in GC.
        (* [comment removed for export] *)
        assert (GB1 : (0x52000 <= bv_unsigned B)%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B + 135168 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= bv_unsigned B)%Z).
        { pose proof (region_free_In _ _ _ gm (Z_to_bv 64 69632) GF
                        ltac:(apply in_or_app; right; apply In_map_has; exact Vhas)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B + 135168 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B)%Z).
        { destruct Vcont as ([cb cs] & Cin & Cne & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK.
        assert (P41 : vals_ev (vals ++ [B]) 41 = B) by (rewrite <- HL; apply vals_ev_last).
        assert (P0' : vals_ev (vals ++ [B]) 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (P1' : vals_ev (vals ++ [B]) 1 = p1) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
        assert (P2' : vals_ev (vals ++ [B]) 2 = mb) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
        assert (P3' : vals_ev (vals ++ [B]) 3 = gm) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P3).
        assert (P4' : vals_ev (vals ++ [B]) 4 = Z_to_bv 64 L) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P4).
        assert (P6' : vals_ev (vals ++ [B]) 6 = e) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P6).
        assert (P7' : vals_ev (vals ++ [B]) 7 = sec) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P7).
        assert (P8' : vals_ev (vals ++ [B]) 8 = cnr) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P8).
        assert (HL1 : length (vals ++ [B]) = 42%nat) by (rewrite length_app, HL; reflexivity).
        set (vals1 := vals ++ [B]) in *. clearbody vals1.
        clear HL P0 P1 P2 P3 P4 P6 P7 P8 vals. rename vals1 into vals. rename HL1 into HL.
        rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P3' into P3. rename P4' into P4. rename P6' into P6.
        rename P7' into P7. rename P8' into P8.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B).
        { unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 135168))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 135168 (SA (EVar 3) 0) 69632)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P3. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 135168 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 135168)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 135168 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B (Z_to_bv 64 135168) M1) (KWr (SA (EVar 41) 0) 135168)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres Minit (zfill B (Z_to_bv 64 135168) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 135168); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { (* [comment removed for export] *) apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 2) (bv_unsigned mb + 4160) (bv_unsigned B) 139232 0 131072 0 0 135152 (bv_unsigned B + 16) 2) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B + 16 - 4)%Z with (bv_unsigned B + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B + 16 - 3)%Z with (bv_unsigned B + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros j Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        assert (G1 : getr R2 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity).
        assert (G10 : getr R2 10 = Z_to_bv 64 (bv_unsigned mb + 4160)).
        { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity. }
        assert (G11 : getr R2 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
        assert (G12 : getr R2 12 = Z_to_bv 64 131072) by (regv HR (12:reg); reflexivity).
        assert (G13 : getr R2 13 = Z_to_bv 64 2) by (regv HR (13:reg); reflexivity).
        destruct (ref_enframe R2 M2 (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 2) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
          as (R3 & M3 & RUN & KEEP & A0 & FR & POST).
        clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 48))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        (* [comment removed for export] *)
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 135151 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 135151 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (135152 - 4 - 131072 - 16 * 2))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (135152 * 0 / 16 + 2)%Z with 2%Z in Pm2 by (vm_compute; reflexivity).
        replace (135152 - 4 - 131072 - 16 * 2)%Z with 4044%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B) by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        Ltac hdr_byte EV41 Pf off :=
          lazymatch type of EV41 with _ = ?B =>
          eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
            lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
        Ltac hdr_word EV41 Pf off w z :=
          lazymatch type of EV41 with _ = ?B =>
          eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
            lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 44) 1 (ELit 0))) by (hdr_byte EV41 Pm4 44%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 45) 1 (ELit 160))) by (hdr_byte EV41 Pm3 45%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 46) 2 (ELit 2))) by (hdr_word EV41 Pm2 46%Z 2%nat 2%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 131120) 1 (ELit 0))) by (hdr_byte EV41 Pzr 131120%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 135159) 1 (ELit 0))) by (hdr_byte EV41 Pe5 135159%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 135160) 4 (ELit 4044))) by (hdr_word EV41 Pe4 135160%Z 4%nat 4044%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 2))) by (hdr_word EV41 Ps2 14%Z 2%nat 2%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres Minit M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B + 13) 135151); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 3) 32 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as SRC end.
        change (eb E 0%nat) with (gblobs content 0%nat) in SRC. rewrite EB1 in SRC.
        set (dst := adenot E (SA (EVar 41) 48)). set (src := adenot E (SA (EVar 3) 32)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B + 48)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned gm + 32)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P3, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 65536 (pref 65536 content)) end.
        { constructor.
          - lia.
          - exact RL1.
          - exact SRC.
          - subst dst. rewrite RL1. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 65536 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 48 0%nat (pref 65536 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RL1; lia)
                        EB1 ltac:(rewrite RL1; lia) ltac:(rewrite RL1; lia)) as HK2 end.
        fold dst in HK2. rewrite RL1, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B + 48)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres Minit (wbytes M4 (Z_to_bv 64 (bv_unsigned B + 48)) (pref 65536 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B + 48) 65536); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RL1 by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR.
        norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat3 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 69632)%Z -> flat E (SA (EVar 3) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P3; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 3%nat 28%Z 1%nat Gb4. { apply Hflat3; lia. }
        krdv HK 3%nat 29%Z 1%nat Gb3. { apply Hflat3; lia. }
        krdv HK 3%nat 30%Z 2%nat Goff. { apply Hflat3; lia. }
        krdv HK 3%nat 0%Z 8%nat Gmeta. { apply Hflat3; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P3 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned gm + 32) (bv_unsigned gm) (bv_unsigned mb + 4120) 0 5 1 72480 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned gm + 32 - 4)%Z with (bv_unsigned gm + 28)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned gm + 32 - 3)%Z with (bv_unsigned gm + 29)%Z by lia. exact Gb3.
          - replace (bv_unsigned gm + 32 - 2)%Z with (bv_unsigned gm + 30)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, (proj2 (proj2 Hmb)); reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let j := kidx kn (is_kimg_cov 0x10508 96) in exact j) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned gm + 32) (bv_unsigned gm) (bv_unsigned mb + 4120) 0 5 1 72480 0 0).
        { constructor.
          all: try (change (w_lastidx 72480) with 0%Z); try (change (w_sizeclass 72480) with 44%Z);
               try (change (w_maplen 72480) with 17%Z); try (change (size_class 44) with 4680%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned gm mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact (proj2 (proj2 Hgm))]. }
          all: try lia.
          all: try reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat3.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned gm + 32))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; subst E; cbn [ev]; rewrite P3; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 1)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR.
        norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW gm 69632 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P3.
        * unfold page_size. exact (proj2 (proj2 Hgm)).
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 69632) with 69632%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 69632) with 69632%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps vm_maps]. apply map_has_cons. exact Vhas.
        * change (page_round_up_Z 69632) with 69632%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD3 : adenot E (SA (EVar 3) 0) = gm).
          { unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P3. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 3) 0 69632 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P3; lia) ltac:(lia)) as HK2 end.
          rewrite AD3 in HK2. clear HK AD3. rename HK2 into HK.
          norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres Minit Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned gm) 69632); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 1) V)) K) end.
          unfold half1_branch in HK1. apply (HK1 _ _ _ B (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 1) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 1) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- (* [comment removed for export] *)
            intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- (* [comment removed for export] *)
            match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- (* [comment removed for export] *)
            unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
            cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
            unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
            assert (Hbg : bv_eqb B gm = false).
            { unfold bv_eqb. apply Z.eqb_neq. intros HH. lia. }
            exists (map_remove (vm_maps VM) gm). split; [|split; [|split; [|split; [|split; [|split]]]]].
            ++ change (nb_of 1) with 135168%Z. rewrite map_remove_skip; [reflexivity|]. intros HH. rewrite HH in Hbg. rewrite bv_eqb_refl in Hbg. discriminate.
            ++ apply incl_Forall with (l1 := vm_maps VM); [|exact Vsz]. unfold map_remove. apply incl_filter.
            ++ pose proof (map_remove_length (vm_maps VM) gm). lia.
            ++ pose proof (live_bytes_map_remove_le (vm_maps VM) gm). lia.
            ++ destruct Vcont as (pc & Cin & Cne & C1 & C2). exists pc. split; [|split; assumption].
               unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst] in Cne |- *.
               apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH. apply Cne. apply bv_eq. exact HH.
            ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 1) with 135168%Z.
               unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
               pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; exact Hq)) as X.
               rewrite u_small in X by lia. lia.
            ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.

End G0.
End WithFP4.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadG0.

Module RefReadG1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow1 : forall R M V B e M0 K,
    full 1 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (131072 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 2 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 131072 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 1) with 135168%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 135168 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 65536 (dropz 65536 content)) = Z.to_nat 65536)
      by (pose proof (pref_length 65536 (dropz 65536 content) ltac:(lia)); pose proof (dropz_length 65536 content ltac:(lia)); lia).
    assert (EBc : gblobs content 1%nat = pref 65536 (dropz 65536 content))
      by (rewrite <- (gblobs_cb 1) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 262164 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 262164) with 266240%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 262164) with 266240%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 266240 <= bv_unsigned B \/ bv_unsigned B + 135168 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 135168) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 266240 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 266240))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 266240 (SA (EVar 5) 0) 135168)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 266240 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 266240)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 266240 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 266240) M1) (KWr (SA (EVar 41) 0) 266240)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 266240) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 266240); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 3) (bv_unsigned mb + 4120) (bv_unsigned B') 270304 0 262144 0 0 266224 (bv_unsigned B' + 16) 3) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 262144) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 3) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 3) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 64))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 266223 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 266223 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (266224 - 4 - 262144 - 16 * 3))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (266224 * 0 / 16 + 3)%Z with 3%Z in Pm2 by (vm_compute; reflexivity).
        replace (266224 - 4 - 262144 - 16 * 3)%Z with 4028%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 60) 1 (ELit 0))) by (hdr_byte EV41 Pm4 60%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 61) 1 (ELit 160))) by (hdr_byte EV41 Pm3 61%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 62) 2 (ELit 3))) by (hdr_word EV41 Pm2 62%Z 2%nat 3%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 262208) 1 (ELit 0))) by (hdr_byte EV41 Pzr 262208%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 266231) 1 (ELit 0))) by (hdr_byte EV41 Pe5 266231%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 266232) 4 (ELit 4028))) by (hdr_word EV41 Pe4 266232%Z 4%nat 4028%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 3))) by (hdr_word EV41 Ps2 14%Z 2%nat 3%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 266223); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 135168)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 48 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 65584 (ELit 65536) 1%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 0%nat) with (gblobs content 0%nat) in SRC1. rewrite (gblobs_hb 1) in SRC1 by lia. change (held_of 1) with 65536%Z in SRC1.
        change (eb E 1%nat) with (gblobs content 1%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 65536 content) = Z.to_nat 65536) by (pose proof (pref_length 65536 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 48)) (length (pref 131072 content)) = Some (pref 131072 content)).
        { replace (pref 131072 content) with (pref 65536 content ++ pref 65536 (dropz 65536 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 48) + nat_to_word (Z.to_nat 65536)) with (adenot E (SA (EVar 5) 65584)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 131072 content) = Z.to_nat 131072) by (pose proof (pref_length 131072 content ltac:(lia)); lia).
        assert (EBf : gblobs content 2%nat = pref 131072 content) by (rewrite <- (gblobs_fb 1) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 64)). set (src := adenot E (SA (EVar 5) 48)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 64)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 48)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 131072 (pref 131072 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 131072) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 131072 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 64 2%nat (pref 131072 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 64)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 64)) (pref 131072 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 64) 131072); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 135168)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 44%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 45%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 46%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 48) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 2 139232 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 48 - 4)%Z with (bv_unsigned B + 44)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 48 - 3)%Z with (bv_unsigned B + 45)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 48 - 2)%Z with (bv_unsigned B + 46)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 48) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 2 139232 0 0).
        { constructor.
          all: try (change (w_lastidx 139232) with 0%Z); try (change (w_sizeclass 139232) with 63%Z);
               try (change (w_maplen 139232) with 33%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 48))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 2)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 135168 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 135168) with 135168%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 135168) with 135168%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 135168) with 135168%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 135168 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 135168); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 2) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 2) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 2) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 2) with 266240%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 2) with 266240%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG1.

Module RefReadG2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow2 : forall R M V B e M0 K,
    full 2 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (262144 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 3 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 262144 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 2) with 266240%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 266240 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 131072 (dropz 131072 content)) = Z.to_nat 131072)
      by (pose proof (pref_length 131072 (dropz 131072 content) ltac:(lia)); pose proof (dropz_length 131072 content ltac:(lia)); lia).
    assert (EBc : gblobs content 3%nat = pref 131072 (dropz 131072 content))
      by (rewrite <- (gblobs_cb 2) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 524308 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 524308) with 528384%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 524308) with 528384%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 528384 <= bv_unsigned B \/ bv_unsigned B + 266240 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 266240) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 528384 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 528384))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 528384 (SA (EVar 5) 0) 266240)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 528384 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 528384)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 528384 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 528384) M1) (KWr (SA (EVar 41) 0) 528384)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 528384) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 528384); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 4) (bv_unsigned mb + 4160) (bv_unsigned B') 532448 0 524288 0 0 528368 (bv_unsigned B' + 16) 4) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 524288) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 4) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 4) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 80))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 528367 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 528367 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (528368 - 4 - 524288 - 16 * 4))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (528368 * 0 / 16 + 4)%Z with 4%Z in Pm2 by (vm_compute; reflexivity).
        replace (528368 - 4 - 524288 - 16 * 4)%Z with 4012%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 76) 1 (ELit 0))) by (hdr_byte EV41 Pm4 76%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 77) 1 (ELit 160))) by (hdr_byte EV41 Pm3 77%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 78) 2 (ELit 4))) by (hdr_word EV41 Pm2 78%Z 2%nat 4%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 524368) 1 (ELit 0))) by (hdr_byte EV41 Pzr 524368%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 528375) 1 (ELit 0))) by (hdr_byte EV41 Pe5 528375%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 528376) 4 (ELit 4012))) by (hdr_word EV41 Pe4 528376%Z 4%nat 4012%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 4))) by (hdr_word EV41 Ps2 14%Z 2%nat 4%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 528367); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 266240)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 64 (ELit 131072) 2%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 131136 (ELit 131072) 3%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 2%nat) with (gblobs content 2%nat) in SRC1. rewrite (gblobs_hb 2) in SRC1 by lia. change (held_of 2) with 131072%Z in SRC1.
        change (eb E 3%nat) with (gblobs content 3%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 131072 content) = Z.to_nat 131072) by (pose proof (pref_length 131072 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 64)) (length (pref 262144 content)) = Some (pref 262144 content)).
        { replace (pref 262144 content) with (pref 131072 content ++ pref 131072 (dropz 131072 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 64) + nat_to_word (Z.to_nat 131072)) with (adenot E (SA (EVar 5) 131136)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 262144 content) = Z.to_nat 262144) by (pose proof (pref_length 262144 content ltac:(lia)); lia).
        assert (EBf : gblobs content 4%nat = pref 262144 content) by (rewrite <- (gblobs_fb 2) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 80)). set (src := adenot E (SA (EVar 5) 64)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 80)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 64)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 262144 (pref 262144 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 262144) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 262144 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 80 4%nat (pref 262144 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 80)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 80)) (pref 262144 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 80) 262144); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 266240)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 60%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 61%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 62%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 64) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 3 270304 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 64 - 4)%Z with (bv_unsigned B + 60)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 64 - 3)%Z with (bv_unsigned B + 61)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 64 - 2)%Z with (bv_unsigned B + 62)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 64) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 3 270304 0 0).
        { constructor.
          all: try (change (w_lastidx 270304) with 0%Z); try (change (w_sizeclass 270304) with 63%Z);
               try (change (w_maplen 270304) with 65%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 64))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 3)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 266240 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 266240) with 266240%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 266240) with 266240%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 266240) with 266240%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 266240 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 266240); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 3) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 3) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 3) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 3) with 528384%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 3) with 528384%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG2.

Module RefReadG3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow3 : forall R M V B e M0 K,
    full 3 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (524288 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 4 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 524288 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 3) with 528384%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 528384 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 262144 (dropz 262144 content)) = Z.to_nat 262144)
      by (pose proof (pref_length 262144 (dropz 262144 content) ltac:(lia)); pose proof (dropz_length 262144 content ltac:(lia)); lia).
    assert (EBc : gblobs content 5%nat = pref 262144 (dropz 262144 content))
      by (rewrite <- (gblobs_cb 3) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 1048596 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 1048596) with 1052672%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 1048596) with 1052672%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 1052672 <= bv_unsigned B \/ bv_unsigned B + 528384 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 528384) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 1052672 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 1052672))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 1052672 (SA (EVar 5) 0) 528384)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 1052672 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 1052672)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 1052672 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 1052672) M1) (KWr (SA (EVar 41) 0) 1052672)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 1052672) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 1052672); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 5) (bv_unsigned mb + 4120) (bv_unsigned B') 1056736 0 1048576 0 0 1052656 (bv_unsigned B' + 16) 5) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 1048576) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 5) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 5) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 96))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 1052655 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 1052655 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (1052656 - 4 - 1048576 - 16 * 5))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (1052656 * 0 / 16 + 5)%Z with 5%Z in Pm2 by (vm_compute; reflexivity).
        replace (1052656 - 4 - 1048576 - 16 * 5)%Z with 3996%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 92) 1 (ELit 0))) by (hdr_byte EV41 Pm4 92%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 93) 1 (ELit 160))) by (hdr_byte EV41 Pm3 93%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 94) 2 (ELit 5))) by (hdr_word EV41 Pm2 94%Z 2%nat 5%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 1048672) 1 (ELit 0))) by (hdr_byte EV41 Pzr 1048672%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 1052663) 1 (ELit 0))) by (hdr_byte EV41 Pe5 1052663%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 1052664) 4 (ELit 3996))) by (hdr_word EV41 Pe4 1052664%Z 4%nat 3996%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 5))) by (hdr_word EV41 Ps2 14%Z 2%nat 5%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 1052655); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 528384)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 80 (ELit 262144) 4%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 262224 (ELit 262144) 5%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 4%nat) with (gblobs content 4%nat) in SRC1. rewrite (gblobs_hb 3) in SRC1 by lia. change (held_of 3) with 262144%Z in SRC1.
        change (eb E 5%nat) with (gblobs content 5%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 262144 content) = Z.to_nat 262144) by (pose proof (pref_length 262144 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 80)) (length (pref 524288 content)) = Some (pref 524288 content)).
        { replace (pref 524288 content) with (pref 262144 content ++ pref 262144 (dropz 262144 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 80) + nat_to_word (Z.to_nat 262144)) with (adenot E (SA (EVar 5) 262224)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 524288 content) = Z.to_nat 524288) by (pose proof (pref_length 524288 content ltac:(lia)); lia).
        assert (EBf : gblobs content 6%nat = pref 524288 content) by (rewrite <- (gblobs_fb 3) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 96)). set (src := adenot E (SA (EVar 5) 80)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 96)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 80)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 524288 (pref 524288 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 524288) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 524288 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 96 6%nat (pref 524288 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 96)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 96)) (pref 524288 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 96) 524288); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 528384)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 76%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 77%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 78%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 80) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 4 532448 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 80 - 4)%Z with (bv_unsigned B + 76)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 80 - 3)%Z with (bv_unsigned B + 77)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 80 - 2)%Z with (bv_unsigned B + 78)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 80) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 4 532448 0 0).
        { constructor.
          all: try (change (w_lastidx 532448) with 0%Z); try (change (w_sizeclass 532448) with 63%Z);
               try (change (w_maplen 532448) with 129%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 80))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 4)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 528384 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 528384) with 528384%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 528384) with 528384%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 528384) with 528384%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 528384 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 528384); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 4) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 4) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 4) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 4) with 1052672%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 4) with 1052672%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG3.

Module RefReadG4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow4 : forall R M V B e M0 K,
    full 4 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (1048576 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 5 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 1048576 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 4) with 1052672%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 1052672 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 524288 (dropz 524288 content)) = Z.to_nat 524288)
      by (pose proof (pref_length 524288 (dropz 524288 content) ltac:(lia)); pose proof (dropz_length 524288 content ltac:(lia)); lia).
    assert (EBc : gblobs content 7%nat = pref 524288 (dropz 524288 content))
      by (rewrite <- (gblobs_cb 4) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 2097172 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 2097172) with 2101248%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 2097172) with 2101248%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 2101248 <= bv_unsigned B \/ bv_unsigned B + 1052672 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 1052672) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 2101248 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 2101248))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 2101248 (SA (EVar 5) 0) 1052672)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 2101248 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 2101248)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 2101248 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 2101248) M1) (KWr (SA (EVar 41) 0) 2101248)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 2101248) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 2101248); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 6) (bv_unsigned mb + 4160) (bv_unsigned B') 2105312 0 2097152 0 0 2101232 (bv_unsigned B' + 16) 6) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 2097152) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 6) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 6) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 112))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 2101231 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 2101231 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (2101232 - 4 - 2097152 - 16 * 6))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (2101232 * 0 / 16 + 6)%Z with 6%Z in Pm2 by (vm_compute; reflexivity).
        replace (2101232 - 4 - 2097152 - 16 * 6)%Z with 3980%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 108) 1 (ELit 0))) by (hdr_byte EV41 Pm4 108%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 109) 1 (ELit 160))) by (hdr_byte EV41 Pm3 109%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 110) 2 (ELit 6))) by (hdr_word EV41 Pm2 110%Z 2%nat 6%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 2097264) 1 (ELit 0))) by (hdr_byte EV41 Pzr 2097264%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 2101239) 1 (ELit 0))) by (hdr_byte EV41 Pe5 2101239%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 2101240) 4 (ELit 3980))) by (hdr_word EV41 Pe4 2101240%Z 4%nat 3980%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 6))) by (hdr_word EV41 Ps2 14%Z 2%nat 6%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 2101231); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 1052672)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 96 (ELit 524288) 6%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 524384 (ELit 524288) 7%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 6%nat) with (gblobs content 6%nat) in SRC1. rewrite (gblobs_hb 4) in SRC1 by lia. change (held_of 4) with 524288%Z in SRC1.
        change (eb E 7%nat) with (gblobs content 7%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 524288 content) = Z.to_nat 524288) by (pose proof (pref_length 524288 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 96)) (length (pref 1048576 content)) = Some (pref 1048576 content)).
        { replace (pref 1048576 content) with (pref 524288 content ++ pref 524288 (dropz 524288 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 96) + nat_to_word (Z.to_nat 524288)) with (adenot E (SA (EVar 5) 524384)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 1048576 content) = Z.to_nat 1048576) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        assert (EBf : gblobs content 8%nat = pref 1048576 content) by (rewrite <- (gblobs_fb 4) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 112)). set (src := adenot E (SA (EVar 5) 96)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 112)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 96)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 1048576 (pref 1048576 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 1048576) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 1048576 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 112 8%nat (pref 1048576 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 112)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 112)) (pref 1048576 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 112) 1048576); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 1052672)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 92%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 93%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 94%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 96) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 5 1056736 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 96 - 4)%Z with (bv_unsigned B + 92)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 96 - 3)%Z with (bv_unsigned B + 93)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 96 - 2)%Z with (bv_unsigned B + 94)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 96) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 5 1056736 0 0).
        { constructor.
          all: try (change (w_lastidx 1056736) with 0%Z); try (change (w_sizeclass 1056736) with 63%Z);
               try (change (w_maplen 1056736) with 257%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 96))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 5)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 1052672 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 1052672) with 1052672%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 1052672) with 1052672%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 1052672) with 1052672%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 1052672 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 1052672); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 5) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 5) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 5) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 5) with 2101248%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 5) with 2101248%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG4.

Module RefReadG5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow5 : forall R M V B e M0 K,
    full 5 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (2097152 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 6 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 2097152 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 5) with 2101248%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 2101248 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 1048576 (dropz 1048576 content)) = Z.to_nat 1048576)
      by (pose proof (pref_length 1048576 (dropz 1048576 content) ltac:(lia)); pose proof (dropz_length 1048576 content ltac:(lia)); lia).
    assert (EBc : gblobs content 9%nat = pref 1048576 (dropz 1048576 content))
      by (rewrite <- (gblobs_cb 5) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 4194324 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 4194324) with 4198400%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 4194324) with 4198400%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 4198400 <= bv_unsigned B \/ bv_unsigned B + 2101248 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 2101248) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 4198400 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 4198400))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 4198400 (SA (EVar 5) 0) 2101248)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 4198400 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 4198400)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 4198400 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 4198400) M1) (KWr (SA (EVar 41) 0) 4198400)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 4198400) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 4198400); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 7) (bv_unsigned mb + 4120) (bv_unsigned B') 4202464 0 4194304 0 0 4198384 (bv_unsigned B' + 16) 7) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 4194304) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 7) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 7) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 128))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 4198383 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 4198383 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (4198384 - 4 - 4194304 - 16 * 7))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (4198384 * 0 / 16 + 7)%Z with 7%Z in Pm2 by (vm_compute; reflexivity).
        replace (4198384 - 4 - 4194304 - 16 * 7)%Z with 3964%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 124) 1 (ELit 0))) by (hdr_byte EV41 Pm4 124%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 125) 1 (ELit 160))) by (hdr_byte EV41 Pm3 125%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 126) 2 (ELit 7))) by (hdr_word EV41 Pm2 126%Z 2%nat 7%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 4194432) 1 (ELit 0))) by (hdr_byte EV41 Pzr 4194432%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 4198391) 1 (ELit 0))) by (hdr_byte EV41 Pe5 4198391%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 4198392) 4 (ELit 3964))) by (hdr_word EV41 Pe4 4198392%Z 4%nat 3964%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 7))) by (hdr_word EV41 Ps2 14%Z 2%nat 7%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 4198383); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 2101248)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 1048688 (ELit 1048576) 9%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 8%nat) with (gblobs content 8%nat) in SRC1. rewrite (gblobs_hb 5) in SRC1 by lia. change (held_of 5) with 1048576%Z in SRC1.
        change (eb E 9%nat) with (gblobs content 9%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 1048576 content) = Z.to_nat 1048576) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 112)) (length (pref 2097152 content)) = Some (pref 2097152 content)).
        { replace (pref 2097152 content) with (pref 1048576 content ++ pref 1048576 (dropz 1048576 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 112) + nat_to_word (Z.to_nat 1048576)) with (adenot E (SA (EVar 5) 1048688)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 2097152 content) = Z.to_nat 2097152) by (pose proof (pref_length 2097152 content ltac:(lia)); lia).
        assert (EBf : gblobs content 10%nat = pref 2097152 content) by (rewrite <- (gblobs_fb 5) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 128)). set (src := adenot E (SA (EVar 5) 112)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 128)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 112)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 2097152 (pref 2097152 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 2097152) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 2097152 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 128 10%nat (pref 2097152 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 128)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 128)) (pref 2097152 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 128) 2097152); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 2101248)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 108%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 109%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 110%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 112) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 6 2105312 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 112 - 4)%Z with (bv_unsigned B + 108)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 112 - 3)%Z with (bv_unsigned B + 109)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 112 - 2)%Z with (bv_unsigned B + 110)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 112) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 6 2105312 0 0).
        { constructor.
          all: try (change (w_lastidx 2105312) with 0%Z); try (change (w_sizeclass 2105312) with 63%Z);
               try (change (w_maplen 2105312) with 513%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 112))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 6)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 2101248 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 2101248) with 2101248%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 2101248) with 2101248%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 2101248) with 2101248%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 2101248 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 2101248); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 6) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 6) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 6) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 6) with 4198400%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 6) with 4198400%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG5.

Module RefReadG6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow6 : forall R M V B e M0 K,
    full 6 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (4194304 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 7 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 4194304 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 6) with 4198400%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 4198400 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 2097152 (dropz 2097152 content)) = Z.to_nat 2097152)
      by (pose proof (pref_length 2097152 (dropz 2097152 content) ltac:(lia)); pose proof (dropz_length 2097152 content ltac:(lia)); lia).
    assert (EBc : gblobs content 11%nat = pref 2097152 (dropz 2097152 content))
      by (rewrite <- (gblobs_cb 6) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 8388628 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 8388628) with 8392704%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 8388628) with 8392704%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 8392704 <= bv_unsigned B \/ bv_unsigned B + 4198400 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 4198400) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 8392704 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 8392704))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 8392704 (SA (EVar 5) 0) 4198400)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 8392704 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 8392704)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 8392704 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 8392704) M1) (KWr (SA (EVar 41) 0) 8392704)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 8392704) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 8392704); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 8) (bv_unsigned mb + 4160) (bv_unsigned B') 8396768 0 8388608 0 0 8392688 (bv_unsigned B' + 16) 8) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 8388608) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 8) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 8) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 144))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 8392687 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 8392687 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (8392688 - 4 - 8388608 - 16 * 8))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (8392688 * 0 / 16 + 8)%Z with 8%Z in Pm2 by (vm_compute; reflexivity).
        replace (8392688 - 4 - 8388608 - 16 * 8)%Z with 3948%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 140) 1 (ELit 0))) by (hdr_byte EV41 Pm4 140%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 141) 1 (ELit 160))) by (hdr_byte EV41 Pm3 141%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 142) 2 (ELit 8))) by (hdr_word EV41 Pm2 142%Z 2%nat 8%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 8388752) 1 (ELit 0))) by (hdr_byte EV41 Pzr 8388752%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 8392695) 1 (ELit 0))) by (hdr_byte EV41 Pe5 8392695%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 8392696) 4 (ELit 3948))) by (hdr_word EV41 Pe4 8392696%Z 4%nat 3948%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 8))) by (hdr_word EV41 Ps2 14%Z 2%nat 8%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 8392687); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 4198400)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 128 (ELit 2097152) 10%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 2097280 (ELit 2097152) 11%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 10%nat) with (gblobs content 10%nat) in SRC1. rewrite (gblobs_hb 6) in SRC1 by lia. change (held_of 6) with 2097152%Z in SRC1.
        change (eb E 11%nat) with (gblobs content 11%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 2097152 content) = Z.to_nat 2097152) by (pose proof (pref_length 2097152 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 128)) (length (pref 4194304 content)) = Some (pref 4194304 content)).
        { replace (pref 4194304 content) with (pref 2097152 content ++ pref 2097152 (dropz 2097152 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 128) + nat_to_word (Z.to_nat 2097152)) with (adenot E (SA (EVar 5) 2097280)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 4194304 content) = Z.to_nat 4194304) by (pose proof (pref_length 4194304 content ltac:(lia)); lia).
        assert (EBf : gblobs content 12%nat = pref 4194304 content) by (rewrite <- (gblobs_fb 6) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 144)). set (src := adenot E (SA (EVar 5) 128)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 144)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 128)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 4194304 (pref 4194304 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 4194304) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 4194304 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 144 12%nat (pref 4194304 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 144)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 144)) (pref 4194304 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 144) 4194304); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 4198400)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 124%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 125%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 126%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 128) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 7 4202464 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 128 - 4)%Z with (bv_unsigned B + 124)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 128 - 3)%Z with (bv_unsigned B + 125)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 128 - 2)%Z with (bv_unsigned B + 126)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 128) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 7 4202464 0 0).
        { constructor.
          all: try (change (w_lastidx 4202464) with 0%Z); try (change (w_sizeclass 4202464) with 63%Z);
               try (change (w_maplen 4202464) with 1025%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 128))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 7)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 4198400 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 4198400) with 4198400%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 4198400) with 4198400%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 4198400) with 4198400%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 4198400 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 4198400); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 7) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 7) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 7) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 7) with 8392704%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 7) with 8392704%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG6.

Module RefReadG7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow7 : forall R M V B e M0 K,
    full 7 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (8388608 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 8 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 8388608 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 7) with 8392704%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 8392704 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 4194304 (dropz 4194304 content)) = Z.to_nat 4194304)
      by (pose proof (pref_length 4194304 (dropz 4194304 content) ltac:(lia)); pose proof (dropz_length 4194304 content ltac:(lia)); lia).
    assert (EBc : gblobs content 13%nat = pref 4194304 (dropz 4194304 content))
      by (rewrite <- (gblobs_cb 7) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 16777236 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 16777236) with 16781312%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 16777236) with 16781312%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 16781312 <= bv_unsigned B \/ bv_unsigned B + 8392704 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 8392704) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 16781312 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 16781312))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 16781312 (SA (EVar 5) 0) 8392704)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 16781312 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 16781312)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 16781312 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 16781312) M1) (KWr (SA (EVar 41) 0) 16781312)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 16781312) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 16781312); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 9) (bv_unsigned mb + 4120) (bv_unsigned B') 16785376 0 16777216 0 0 16781296 (bv_unsigned B' + 16) 9) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 16777216) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 9) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 9) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 160))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 16781295 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 16781295 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (16781296 - 4 - 16777216 - 16 * 9))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (16781296 * 0 / 16 + 9)%Z with 9%Z in Pm2 by (vm_compute; reflexivity).
        replace (16781296 - 4 - 16777216 - 16 * 9)%Z with 3932%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 156) 1 (ELit 0))) by (hdr_byte EV41 Pm4 156%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 157) 1 (ELit 160))) by (hdr_byte EV41 Pm3 157%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 158) 2 (ELit 9))) by (hdr_word EV41 Pm2 158%Z 2%nat 9%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 16777376) 1 (ELit 0))) by (hdr_byte EV41 Pzr 16777376%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 16781303) 1 (ELit 0))) by (hdr_byte EV41 Pe5 16781303%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 16781304) 4 (ELit 3932))) by (hdr_word EV41 Pe4 16781304%Z 4%nat 3932%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 9))) by (hdr_word EV41 Ps2 14%Z 2%nat 9%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 16781295); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8392704)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 144 (ELit 4194304) 12%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 4194448 (ELit 4194304) 13%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 12%nat) with (gblobs content 12%nat) in SRC1. rewrite (gblobs_hb 7) in SRC1 by lia. change (held_of 7) with 4194304%Z in SRC1.
        change (eb E 13%nat) with (gblobs content 13%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 4194304 content) = Z.to_nat 4194304) by (pose proof (pref_length 4194304 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 144)) (length (pref 8388608 content)) = Some (pref 8388608 content)).
        { replace (pref 8388608 content) with (pref 4194304 content ++ pref 4194304 (dropz 4194304 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 144) + nat_to_word (Z.to_nat 4194304)) with (adenot E (SA (EVar 5) 4194448)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 8388608 content) = Z.to_nat 8388608) by (pose proof (pref_length 8388608 content ltac:(lia)); lia).
        assert (EBf : gblobs content 14%nat = pref 8388608 content) by (rewrite <- (gblobs_fb 7) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 160)). set (src := adenot E (SA (EVar 5) 144)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 160)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 144)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 8388608 (pref 8388608 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 8388608) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 8388608 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 160 14%nat (pref 8388608 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 160)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 160)) (pref 8388608 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 160) 8388608); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8392704)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 140%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 141%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 142%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 144) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 8 8396768 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 144 - 4)%Z with (bv_unsigned B + 140)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 144 - 3)%Z with (bv_unsigned B + 141)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 144 - 2)%Z with (bv_unsigned B + 142)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 144) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 8 8396768 0 0).
        { constructor.
          all: try (change (w_lastidx 8396768) with 0%Z); try (change (w_sizeclass 8396768) with 63%Z);
               try (change (w_maplen 8396768) with 2049%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 144))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 8)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 8392704 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 8392704) with 8392704%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 8392704) with 8392704%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 8392704) with 8392704%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 8392704 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 8392704); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 8) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 8) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 8) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 8) with 16781312%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 8) with 16781312%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG7.

Module RefReadG8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow8 : forall R M V B e M0 K,
    full 8 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (16777216 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 9 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 16777216 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 8) with 16781312%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 16781312 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 8388608 (dropz 8388608 content)) = Z.to_nat 8388608)
      by (pose proof (pref_length 8388608 (dropz 8388608 content) ltac:(lia)); pose proof (dropz_length 8388608 content ltac:(lia)); lia).
    assert (EBc : gblobs content 15%nat = pref 8388608 (dropz 8388608 content))
      by (rewrite <- (gblobs_cb 8) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 33554452 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 33554452) with 33558528%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 33554452) with 33558528%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 33558528 <= bv_unsigned B \/ bv_unsigned B + 16781312 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 16781312) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 33558528 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 33558528))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 33558528 (SA (EVar 5) 0) 16781312)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 33558528 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 33558528)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 33558528 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 33558528) M1) (KWr (SA (EVar 41) 0) 33558528)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 33558528) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 33558528); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 10) (bv_unsigned mb + 4160) (bv_unsigned B') 33562592 0 33554432 0 0 33558512 (bv_unsigned B' + 16) 10) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 33554432) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 10) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 10) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 176))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 33558511 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 33558511 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (33558512 - 4 - 33554432 - 16 * 10))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (33558512 * 0 / 16 + 10)%Z with 10%Z in Pm2 by (vm_compute; reflexivity).
        replace (33558512 - 4 - 33554432 - 16 * 10)%Z with 3916%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 172) 1 (ELit 0))) by (hdr_byte EV41 Pm4 172%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 173) 1 (ELit 160))) by (hdr_byte EV41 Pm3 173%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 174) 2 (ELit 10))) by (hdr_word EV41 Pm2 174%Z 2%nat 10%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 33554608) 1 (ELit 0))) by (hdr_byte EV41 Pzr 33554608%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 33558519) 1 (ELit 0))) by (hdr_byte EV41 Pe5 33558519%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 33558520) 4 (ELit 3916))) by (hdr_word EV41 Pe4 33558520%Z 4%nat 3916%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 10))) by (hdr_word EV41 Ps2 14%Z 2%nat 10%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 33558511); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 16781312)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 160 (ELit 8388608) 14%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 8388768 (ELit 8388608) 15%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 14%nat) with (gblobs content 14%nat) in SRC1. rewrite (gblobs_hb 8) in SRC1 by lia. change (held_of 8) with 8388608%Z in SRC1.
        change (eb E 15%nat) with (gblobs content 15%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 8388608 content) = Z.to_nat 8388608) by (pose proof (pref_length 8388608 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 160)) (length (pref 16777216 content)) = Some (pref 16777216 content)).
        { replace (pref 16777216 content) with (pref 8388608 content ++ pref 8388608 (dropz 8388608 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 160) + nat_to_word (Z.to_nat 8388608)) with (adenot E (SA (EVar 5) 8388768)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 16777216 content) = Z.to_nat 16777216) by (pose proof (pref_length 16777216 content ltac:(lia)); lia).
        assert (EBf : gblobs content 16%nat = pref 16777216 content) by (rewrite <- (gblobs_fb 8) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 176)). set (src := adenot E (SA (EVar 5) 160)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 176)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 160)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 16777216 (pref 16777216 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 16777216) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 16777216 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 176 16%nat (pref 16777216 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 176)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 176)) (pref 16777216 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 176) 16777216); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 16781312)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 156%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 157%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 158%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 160) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 9 16785376 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 160 - 4)%Z with (bv_unsigned B + 156)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 160 - 3)%Z with (bv_unsigned B + 157)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 160 - 2)%Z with (bv_unsigned B + 158)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 160) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 9 16785376 0 0).
        { constructor.
          all: try (change (w_lastidx 16785376) with 0%Z); try (change (w_sizeclass 16785376) with 63%Z);
               try (change (w_maplen 16785376) with 4097%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 160))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 9)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 16781312 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 16781312) with 16781312%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 16781312) with 16781312%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 16781312) with 16781312%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 16781312 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 16781312); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 9) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 9) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 9) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 9) with 33558528%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 9) with 33558528%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG8.

Module RefReadG9.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpy OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MallocDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframeBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefEnframe OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefGetMeta OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Section G.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of j') V)) K.

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV41 Pf off :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 41) _ off _ EV41); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV41 Pf off w z :=
    lazymatch type of EV41 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 41) _ off w (ELit z) (Z_to_bv 64 z) EV41 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow9 : forall R M V B e M0 K,
    full 9 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (33554432 <= L)%Z ->
    (0x52000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    half_branch 10 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 33554432 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 Hmb0 Hmb1 Hmba HspR HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Vsp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps).
    change (nb_of 9) with 33558528%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 33558528 <= bv_unsigned sp0 - 8388608)%Z) by (unfold CEIL, BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 16777216 (dropz 16777216 content)) = Z.to_nat 16777216)
      by (pose proof (pref_length 16777216 (dropz 16777216 content) ltac:(lia)); pose proof (dropz_length 16777216 content ltac:(lia)); lia).
    assert (EBc : gblobs content 17%nat = pref 16777216 (dropz 16777216 content))
      by (rewrite <- (gblobs_cb 9) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. run_block_keep scr0 41%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
        eapply (rz_mmap_anon RSEGS Rc (Z_to_bv 64 0x186d8) Mc MD ECALLW 67108884 K fetch_181b0 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 67108884) with 67112960%Z.
        apply grant_exists; [ | | | apply grant_budget_intro; [reflexivity | reflexivity |] | ];
          cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]; rewrite ?Vres, ?Vmaps, ?rsegs_reserved.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. lia.
        * rewrite alloc_top_val, Vsp. lia.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 67108884) with 67112960%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (100056 + 4)%Z with 0x186dc%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        rewrite alloc_top_val in GC. unfold page_size in GA.
        cbv [m_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps] in GF, GLv, GC. rewrite Vres, Vmaps, rsegs_reserved in GF. rewrite Vsp in GC.
        assert (GB1 : (0x52000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 131072) (Z_to_bv 64 204800) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 67112960 <= bv_unsigned B \/ bv_unsigned B + 33558528 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 33558528) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 67112960 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P41 : vals_ev (vals ++ [B']) 41 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 42%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD41 : adenot E (SA (EVar 41) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 41) HR2 ltac:(cbn [edenot ev]; subst E; exact P41)) as HR. clear HR2.
        assert (KA41 : kentry_ok RSEGS E M1 (KAlign (EVar 41) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. exact GA. }
        assert (KR41 : kentry_ok RSEGS E M1 (KRange (EVar 41) 0x52000 (CEIL - 67112960))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. unfold CEIL. lia. }
        assert (KD41a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 67112960 (SA (EVar 5) 0) 33558528)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P5. lia. }
        assert (KD41b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 41) 0) 67112960 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, P2. lia. }
        assert (KD41s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) BAND (SA (EVar 41) 0) 67112960)).
        { cbn [kentry_ok]. unfold estart, BAND. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P41, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA41 (know_ok_cons _ _ _ _ _ KR41 (know_ok_cons _ _ _ _ _ KD41s
                     (know_ok_cons _ _ _ _ _ KD41a (know_ok_cons _ _ _ _ _ KD41b HK2))))) as HK2'.
        clear KA41 KR41 KD41s KD41a KD41b HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 41) 0 67112960 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD41 in HK3. clear HK2'.
        assert (KW41 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 67112960) M1) (KWr (SA (EVar 41) 0) 67112960)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW41 HK3) as HK. clear KW41 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 67112960) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 67112960); [lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scrT 42%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P41. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P41 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 41) 12%Z Z12. kzero_at HK (EVar 41) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P41 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
        assert (EF : efH Mc (Z_to_bv 64 11) (bv_unsigned mb + 4120) (bv_unsigned B') 67117024 0 67108864 0 0 67112944 (bv_unsigned B' + 16) 11) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 41) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P41; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10508 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b30)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b30) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 67108864) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 11) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x12b30) (Z_to_bv 64 11) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 99144) with (0x18348 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD41. subst E.
        grow_vals HL (junk_vals R3) 74%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 41) (ELit 192))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P41. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 41) 13) \/ estart E (SA (EVar 41) 13) + 67112943 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P41 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 41) 13 67112943 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (67112944 - 4 - 67108864 - 16 * 11))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (67112944 * 0 / 16 + 11)%Z with 11%Z in Pm2 by (vm_compute; reflexivity).
        replace (67112944 - 4 - 67108864 - 16 * 11)%Z with 3900%Z in Pe4 by reflexivity.
        assert (EV41 : edenot E (EVar 41) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P41).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 188) 1 (ELit 0))) by (hdr_byte EV41 Pm4 188%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 189) 1 (ELit 160))) by (hdr_byte EV41 Pm3 189%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 190) 2 (ELit 11))) by (hdr_word EV41 Pm2 190%Z 2%nat 11%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 67109056) 1 (ELit 0))) by (hdr_byte EV41 Pzr 67109056%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 67112951) 1 (ELit 0))) by (hdr_byte EV41 Pe5 67112951%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 67112952) 4 (ELit 3900))) by (hdr_word EV41 Pe4 67112952%Z 4%nat 3900%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 13) 1 (ELit 224))) by (hdr_byte EV41 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 41) 14) 2 (ELit 11))) by (hdr_word EV41 Ps2 14%Z 2%nat 11%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 67112943); [lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 74%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 33558528)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 176 (ELit 16777216) 16%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 16777392 (ELit 16777216) 17%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 16%nat) with (gblobs content 16%nat) in SRC1. rewrite (gblobs_hb 9) in SRC1 by lia. change (held_of 9) with 16777216%Z in SRC1.
        change (eb E 17%nat) with (gblobs content 17%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 16777216 content) = Z.to_nat 16777216) by (pose proof (pref_length 16777216 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 176)) (length (pref 33554432 content)) = Some (pref 33554432 content)).
        { replace (pref 33554432 content) with (pref 16777216 content ++ pref 16777216 (dropz 16777216 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 176) + nat_to_word (Z.to_nat 16777216)) with (adenot E (SA (EVar 5) 16777392)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 33554432 content) = Z.to_nat 33554432) by (pose proof (pref_length 33554432 content ltac:(lia)); lia).
        assert (EBf : gblobs content 18%nat = pref 33554432 content) by (rewrite <- (gblobs_fb 9) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 41) 192)). set (src := adenot E (SA (EVar 5) 176)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 192)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P41, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 176)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (MC : mcH Mc dst src 33554432 (pref 33554432 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x12b4c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x12b4c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 33554432) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 33554432 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0x12b4c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 41) 192 18%nat (pref 33554432 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P41, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 192)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 192)) (pref 33554432 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 192) 33554432); [lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV41 Hflat5.
        grow_vals HL (junk_vals R5) 106%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 106%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 33558528)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 172%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 173%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 174%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x50cf0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 176) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 10 33562592 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 176 - 4)%Z with (bv_unsigned B + 172)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 176 - 3)%Z with (bv_unsigned B + 173)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 176 - 2)%Z with (bv_unsigned B + 174)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. rewrite P7 in Garea. exact Garea.
          - change (ev E 7) with (vals_ev vals 7) in Gsec. rewrite P7 in Gsec. exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x10508 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 176) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 10 33562592 0 0).
        { constructor.
          all: try (change (w_lastidx 33562592) with 0%Z); try (change (w_sizeclass 33562592) with 63%Z);
               try (change (w_maplen 33562592) with 8193%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x16dcc)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 176))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x16dcc) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x16dcc) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 94068) with (0x16f74 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 138%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 10)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) _ =>
          eapply (rz_munmap RSEGS Rc (Z_to_bv 64 0x18770) Mc MD ECALLW B 33558528 K fetch_18248 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 33558528) with 33558528%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 33558528) with 33558528%Z. cbv [m_vmmaps mmap_model with_vmmaps RefReadDefs.modelG mkModelC m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 33558528) with 33558528%Z.
          rewrite v_addi_pc4 by lia. change (0x18770 + 4)%Z with 0x18774%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 33558528 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 33558528); [lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. run_block_keep scr0 138%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               RefReadDefs.modelG mkModelC]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) _ =>
            change (realizes RSEGS (mkCfg (mkst Rc (Z_to_bv 64 0x12b54) Mc (seg_rom RSEGS)) (modelG (held_of 10) V')) K) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 41; EExt true 0 4 (EVar 6); EVar 7; EVar 8] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb gm L B' (edenot E (EExt true 0 4 (EVar 6))) sec cnr (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 10) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 10) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P41, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Vsp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split]]]]].
             ++ change (nb_of 10) with 67112960%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 10) with 67112960%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
  Qed.
End G.
End WithFP1.

End RefReadG9.

Module RefReadF1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill1 : forall R M V B e M0 K,
    half 1 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (131072 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 1 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 65536 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 135168 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 135168%Z 65584%Z (Z.to_nat 65536) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z in SOKb by lia.
    replace (Z.to_nat 65536) with (Z.to_nat (131072 - 65536)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 48 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 0%nat) with (gblobs content 0%nat) in HELD. rewrite (gblobs_hb 1) in HELD by lia. change (held_of 1) with 65536%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 65536) R M (bv_unsigned sp0) (bv_unsigned B + 48) 65536 131072 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((131072 - 65536)%Z) with (65536%Z) in FR. change ((131072 - 65536)%Z) with (65536%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 65584 65536)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 65536 (dropz 65536 content))) = 65536%Z)
        by (pose proof (pref_length 65536 (dropz 65536 content) ltac:(lia)); pose proof (dropz_length 65536 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 65584) (ELit 65536) 1%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 65584 65536 1%nat (pref 65536 (dropz 65536 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 1%nat) with (gblobs content 1%nat). rewrite (gblobs_cb 1) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 65536 (dropz 65536 content))) with (Z.to_nat 65536) by lia.
          replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 48)) (ridx 23) (bx 48)) (ridx 19) (ELit 131072)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 1) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 1) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin1 : forall R M V B e M0 K,
    half 1 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (65536 <= L < 131072)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 1 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 65536 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 135168 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 135168%Z 65584%Z (Z.to_nat 65536) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z in SOKb by lia.
    replace (Z.to_nat 65536) with (Z.to_nat (131072 - 65536)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 48 (ELit 65536) 0%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 0%nat) with (gblobs content 0%nat) in HELD. rewrite (gblobs_hb 1) in HELD by lia. change (held_of 1) with 65536%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 65536) R M (bv_unsigned sp0) (bv_unsigned B + 48) 65536 131072 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 48 + 65536), 65536%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 65584 65536)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 65584)%Z with (bv_unsigned B + 48 + 65536)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 1)%Z with (bv_unsigned B + 48)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 48) 65536); try lia; [|exact PM].
        replace (Z.to_nat 65536) with (length (pref 65536 content)) by (pose proof (pref_length 65536 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 1) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF1.

Module RefReadF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill2 : forall R M V B e M0 K,
    half 2 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (262144 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 2 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 131072 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 266240 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 266240%Z 131136%Z (Z.to_nat 131072) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z in SOKb by lia.
    replace (Z.to_nat 131072) with (Z.to_nat (262144 - 131072)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 64 (ELit 131072) 2%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 2%nat) with (gblobs content 2%nat) in HELD. rewrite (gblobs_hb 2) in HELD by lia. change (held_of 2) with 131072%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 131072) R M (bv_unsigned sp0) (bv_unsigned B + 64) 131072 262144 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((262144 - 131072)%Z) with (131072%Z) in FR. change ((262144 - 131072)%Z) with (131072%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 131136 131072)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 131072 (dropz 131072 content))) = 131072%Z)
        by (pose proof (pref_length 131072 (dropz 131072 content) ltac:(lia)); pose proof (dropz_length 131072 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 131136) (ELit 131072) 3%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 131136 131072 3%nat (pref 131072 (dropz 131072 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 3%nat) with (gblobs content 3%nat). rewrite (gblobs_cb 2) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 131072 (dropz 131072 content))) with (Z.to_nat 131072) by lia.
          replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 64)) (ridx 23) (bx 64)) (ridx 19) (ELit 262144)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 2) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 2) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin2 : forall R M V B e M0 K,
    half 2 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (131072 <= L < 262144)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 2 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 131072 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 266240 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 266240%Z 131136%Z (Z.to_nat 131072) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z in SOKb by lia.
    replace (Z.to_nat 131072) with (Z.to_nat (262144 - 131072)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 64 (ELit 131072) 2%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 2%nat) with (gblobs content 2%nat) in HELD. rewrite (gblobs_hb 2) in HELD by lia. change (held_of 2) with 131072%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 131072) R M (bv_unsigned sp0) (bv_unsigned B + 64) 131072 262144 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 64 + 131072), 131072%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 131136 131072)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 131136)%Z with (bv_unsigned B + 64 + 131072)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 2)%Z with (bv_unsigned B + 64)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 64) 131072); try lia; [|exact PM].
        replace (Z.to_nat 131072) with (length (pref 131072 content)) by (pose proof (pref_length 131072 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 2) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF2.

Module RefReadF3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill3 : forall R M V B e M0 K,
    half 3 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (524288 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 3 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 262144 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 528384 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 528384%Z 262224%Z (Z.to_nat 262144) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z in SOKb by lia.
    replace (Z.to_nat 262144) with (Z.to_nat (524288 - 262144)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 80 (ELit 262144) 4%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 4%nat) with (gblobs content 4%nat) in HELD. rewrite (gblobs_hb 3) in HELD by lia. change (held_of 3) with 262144%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 262144) R M (bv_unsigned sp0) (bv_unsigned B + 80) 262144 524288 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((524288 - 262144)%Z) with (262144%Z) in FR. change ((524288 - 262144)%Z) with (262144%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 262224 262144)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 262144 (dropz 262144 content))) = 262144%Z)
        by (pose proof (pref_length 262144 (dropz 262144 content) ltac:(lia)); pose proof (dropz_length 262144 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 262224) (ELit 262144) 5%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 262224 262144 5%nat (pref 262144 (dropz 262144 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 5%nat) with (gblobs content 5%nat). rewrite (gblobs_cb 3) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 262144 (dropz 262144 content))) with (Z.to_nat 262144) by lia.
          replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 80)) (ridx 23) (bx 80)) (ridx 19) (ELit 524288)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 3) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 3) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin3 : forall R M V B e M0 K,
    half 3 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (262144 <= L < 524288)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 3 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 262144 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 528384 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 528384%Z 262224%Z (Z.to_nat 262144) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z in SOKb by lia.
    replace (Z.to_nat 262144) with (Z.to_nat (524288 - 262144)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 80 (ELit 262144) 4%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 4%nat) with (gblobs content 4%nat) in HELD. rewrite (gblobs_hb 3) in HELD by lia. change (held_of 3) with 262144%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 262144) R M (bv_unsigned sp0) (bv_unsigned B + 80) 262144 524288 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 80 + 262144), 262144%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 262224 262144)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 262224)%Z with (bv_unsigned B + 80 + 262144)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 3)%Z with (bv_unsigned B + 80)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 80) 262144); try lia; [|exact PM].
        replace (Z.to_nat 262144) with (length (pref 262144 content)) by (pose proof (pref_length 262144 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 3) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF3.

Module RefReadF4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill4 : forall R M V B e M0 K,
    half 4 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (1048576 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 4 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 524288 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 1052672 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 1052672%Z 524384%Z (Z.to_nat 524288) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z in SOKb by lia.
    replace (Z.to_nat 524288) with (Z.to_nat (1048576 - 524288)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 96 (ELit 524288) 6%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 6%nat) with (gblobs content 6%nat) in HELD. rewrite (gblobs_hb 4) in HELD by lia. change (held_of 4) with 524288%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 524288) R M (bv_unsigned sp0) (bv_unsigned B + 96) 524288 1048576 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((1048576 - 524288)%Z) with (524288%Z) in FR. change ((1048576 - 524288)%Z) with (524288%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 524384 524288)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 524288 (dropz 524288 content))) = 524288%Z)
        by (pose proof (pref_length 524288 (dropz 524288 content) ltac:(lia)); pose proof (dropz_length 524288 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 524384) (ELit 524288) 7%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 524384 524288 7%nat (pref 524288 (dropz 524288 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 7%nat) with (gblobs content 7%nat). rewrite (gblobs_cb 4) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 524288 (dropz 524288 content))) with (Z.to_nat 524288) by lia.
          replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 96)) (ridx 23) (bx 96)) (ridx 19) (ELit 1048576)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 4) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 4) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin4 : forall R M V B e M0 K,
    half 4 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (524288 <= L < 1048576)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 4 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 524288 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 1052672 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 1052672%Z 524384%Z (Z.to_nat 524288) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z in SOKb by lia.
    replace (Z.to_nat 524288) with (Z.to_nat (1048576 - 524288)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 96 (ELit 524288) 6%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 6%nat) with (gblobs content 6%nat) in HELD. rewrite (gblobs_hb 4) in HELD by lia. change (held_of 4) with 524288%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 524288) R M (bv_unsigned sp0) (bv_unsigned B + 96) 524288 1048576 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 96 + 524288), 524288%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 524384 524288)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 524384)%Z with (bv_unsigned B + 96 + 524288)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 4)%Z with (bv_unsigned B + 96)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 96) 524288); try lia; [|exact PM].
        replace (Z.to_nat 524288) with (length (pref 524288 content)) by (pose proof (pref_length 524288 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 4) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF4.

Module RefReadF5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill5 : forall R M V B e M0 K,
    half 5 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (2097152 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 5 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 1048576 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 2101248 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 2101248%Z 1048688%Z (Z.to_nat 1048576) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z in SOKb by lia.
    replace (Z.to_nat 1048576) with (Z.to_nat (2097152 - 1048576)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 8%nat) with (gblobs content 8%nat) in HELD. rewrite (gblobs_hb 5) in HELD by lia. change (held_of 5) with 1048576%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 1048576) R M (bv_unsigned sp0) (bv_unsigned B + 112) 1048576 2097152 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((2097152 - 1048576)%Z) with (1048576%Z) in FR. change ((2097152 - 1048576)%Z) with (1048576%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 1048688 1048576)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 1048576 (dropz 1048576 content))) = 1048576%Z)
        by (pose proof (pref_length 1048576 (dropz 1048576 content) ltac:(lia)); pose proof (dropz_length 1048576 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 1048688) (ELit 1048576) 9%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 1048688 1048576 9%nat (pref 1048576 (dropz 1048576 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 9%nat) with (gblobs content 9%nat). rewrite (gblobs_cb 5) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 1048576 (dropz 1048576 content))) with (Z.to_nat 1048576) by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 112)) (ridx 23) (bx 112)) (ridx 19) (ELit 2097152)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 5) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 5) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin5 : forall R M V B e M0 K,
    half 5 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (1048576 <= L < 2097152)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 5 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 1048576 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 2101248 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 2101248%Z 1048688%Z (Z.to_nat 1048576) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z in SOKb by lia.
    replace (Z.to_nat 1048576) with (Z.to_nat (2097152 - 1048576)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 8%nat) with (gblobs content 8%nat) in HELD. rewrite (gblobs_hb 5) in HELD by lia. change (held_of 5) with 1048576%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 1048576) R M (bv_unsigned sp0) (bv_unsigned B + 112) 1048576 2097152 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 112 + 1048576), 1048576%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 1048688 1048576)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 1048688)%Z with (bv_unsigned B + 112 + 1048576)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 5)%Z with (bv_unsigned B + 112)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 112) 1048576); try lia; [|exact PM].
        replace (Z.to_nat 1048576) with (length (pref 1048576 content)) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 5) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF5.

Module RefReadF6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill6 : forall R M V B e M0 K,
    half 6 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (4194304 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 6 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 2097152 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 4198400 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 4198400%Z 2097280%Z (Z.to_nat 2097152) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z in SOKb by lia.
    replace (Z.to_nat 2097152) with (Z.to_nat (4194304 - 2097152)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 128 (ELit 2097152) 10%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 10%nat) with (gblobs content 10%nat) in HELD. rewrite (gblobs_hb 6) in HELD by lia. change (held_of 6) with 2097152%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 2097152) R M (bv_unsigned sp0) (bv_unsigned B + 128) 2097152 4194304 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((4194304 - 2097152)%Z) with (2097152%Z) in FR. change ((4194304 - 2097152)%Z) with (2097152%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 2097280 2097152)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 2097152 (dropz 2097152 content))) = 2097152%Z)
        by (pose proof (pref_length 2097152 (dropz 2097152 content) ltac:(lia)); pose proof (dropz_length 2097152 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 2097280) (ELit 2097152) 11%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 2097280 2097152 11%nat (pref 2097152 (dropz 2097152 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 11%nat) with (gblobs content 11%nat). rewrite (gblobs_cb 6) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 2097152 (dropz 2097152 content))) with (Z.to_nat 2097152) by lia.
          replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 128)) (ridx 23) (bx 128)) (ridx 19) (ELit 4194304)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 6) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 6) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin6 : forall R M V B e M0 K,
    half 6 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (2097152 <= L < 4194304)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 6 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 2097152 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 4198400 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 4198400%Z 2097280%Z (Z.to_nat 2097152) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z in SOKb by lia.
    replace (Z.to_nat 2097152) with (Z.to_nat (4194304 - 2097152)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 128 (ELit 2097152) 10%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 10%nat) with (gblobs content 10%nat) in HELD. rewrite (gblobs_hb 6) in HELD by lia. change (held_of 6) with 2097152%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 2097152) R M (bv_unsigned sp0) (bv_unsigned B + 128) 2097152 4194304 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 128 + 2097152), 2097152%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 2097280 2097152)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 2097280)%Z with (bv_unsigned B + 128 + 2097152)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 6)%Z with (bv_unsigned B + 128)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 128) 2097152); try lia; [|exact PM].
        replace (Z.to_nat 2097152) with (length (pref 2097152 content)) by (pose proof (pref_length 2097152 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 6) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF6.

Module RefReadF7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill7 : forall R M V B e M0 K,
    half 7 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (8388608 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 7 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 4194304 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 8392704 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 8392704%Z 4194448%Z (Z.to_nat 4194304) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z in SOKb by lia.
    replace (Z.to_nat 4194304) with (Z.to_nat (8388608 - 4194304)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 144 (ELit 4194304) 12%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 12%nat) with (gblobs content 12%nat) in HELD. rewrite (gblobs_hb 7) in HELD by lia. change (held_of 7) with 4194304%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 4194304) R M (bv_unsigned sp0) (bv_unsigned B + 144) 4194304 8388608 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((8388608 - 4194304)%Z) with (4194304%Z) in FR. change ((8388608 - 4194304)%Z) with (4194304%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 4194448 4194304)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 4194304 (dropz 4194304 content))) = 4194304%Z)
        by (pose proof (pref_length 4194304 (dropz 4194304 content) ltac:(lia)); pose proof (dropz_length 4194304 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 4194448) (ELit 4194304) 13%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 4194448 4194304 13%nat (pref 4194304 (dropz 4194304 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 13%nat) with (gblobs content 13%nat). rewrite (gblobs_cb 7) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 4194304 (dropz 4194304 content))) with (Z.to_nat 4194304) by lia.
          replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 144)) (ridx 23) (bx 144)) (ridx 19) (ELit 8388608)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 7) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 7) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin7 : forall R M V B e M0 K,
    half 7 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (4194304 <= L < 8388608)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 7 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 4194304 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 8392704 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 8392704%Z 4194448%Z (Z.to_nat 4194304) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z in SOKb by lia.
    replace (Z.to_nat 4194304) with (Z.to_nat (8388608 - 4194304)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 144 (ELit 4194304) 12%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 12%nat) with (gblobs content 12%nat) in HELD. rewrite (gblobs_hb 7) in HELD by lia. change (held_of 7) with 4194304%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 4194304) R M (bv_unsigned sp0) (bv_unsigned B + 144) 4194304 8388608 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 144 + 4194304), 4194304%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 4194448 4194304)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 4194448)%Z with (bv_unsigned B + 144 + 4194304)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 7)%Z with (bv_unsigned B + 144)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 144) 4194304); try lia; [|exact PM].
        replace (Z.to_nat 4194304) with (length (pref 4194304 content)) by (pose proof (pref_length 4194304 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 7) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF7.

Module RefReadF8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill8 : forall R M V B e M0 K,
    half 8 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (16777216 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 8 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 8388608 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 16781312 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 16781312%Z 8388768%Z (Z.to_nat 8388608) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z in SOKb by lia.
    replace (Z.to_nat 8388608) with (Z.to_nat (16777216 - 8388608)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 160 (ELit 8388608) 14%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 14%nat) with (gblobs content 14%nat) in HELD. rewrite (gblobs_hb 8) in HELD by lia. change (held_of 8) with 8388608%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 8388608) R M (bv_unsigned sp0) (bv_unsigned B + 160) 8388608 16777216 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((16777216 - 8388608)%Z) with (8388608%Z) in FR. change ((16777216 - 8388608)%Z) with (8388608%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 8388768 8388608)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 8388608 (dropz 8388608 content))) = 8388608%Z)
        by (pose proof (pref_length 8388608 (dropz 8388608 content) ltac:(lia)); pose proof (dropz_length 8388608 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 8388768) (ELit 8388608) 15%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 8388768 8388608 15%nat (pref 8388608 (dropz 8388608 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 15%nat) with (gblobs content 15%nat). rewrite (gblobs_cb 8) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 8388608 (dropz 8388608 content))) with (Z.to_nat 8388608) by lia.
          replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 160)) (ridx 23) (bx 160)) (ridx 19) (ELit 16777216)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 8) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 8) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin8 : forall R M V B e M0 K,
    half 8 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (8388608 <= L < 16777216)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 8 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 8388608 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 16781312 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 16781312%Z 8388768%Z (Z.to_nat 8388608) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z in SOKb by lia.
    replace (Z.to_nat 8388608) with (Z.to_nat (16777216 - 8388608)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 160 (ELit 8388608) 14%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 14%nat) with (gblobs content 14%nat) in HELD. rewrite (gblobs_hb 8) in HELD by lia. change (held_of 8) with 8388608%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 8388608) R M (bv_unsigned sp0) (bv_unsigned B + 160) 8388608 16777216 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 160 + 8388608), 8388608%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 8388768 8388608)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 8388768)%Z with (bv_unsigned B + 160 + 8388608)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 8)%Z with (bv_unsigned B + 160)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 160) 8388608); try lia; [|exact PM].
        replace (Z.to_nat 8388608) with (length (pref 8388608 content)) by (pose proof (pref_length 8388608 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 8) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF8.

Module RefReadF9.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill9 : forall R M V B e M0 K,
    half 9 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (33554432 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 9 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 16777216 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 33558528 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 33558528%Z 16777392%Z (Z.to_nat 16777216) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z in SOKb by lia.
    replace (Z.to_nat 16777216) with (Z.to_nat (33554432 - 16777216)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 176 (ELit 16777216) 16%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 16%nat) with (gblobs content 16%nat) in HELD. rewrite (gblobs_hb 9) in HELD by lia. change (held_of 9) with 16777216%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 16777216) R M (bv_unsigned sp0) (bv_unsigned B + 176) 16777216 33554432 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((33554432 - 16777216)%Z) with (16777216%Z) in FR. change ((33554432 - 16777216)%Z) with (16777216%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 16777392 16777216)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 16777216 (dropz 16777216 content))) = 16777216%Z)
        by (pose proof (pref_length 16777216 (dropz 16777216 content) ltac:(lia)); pose proof (dropz_length 16777216 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 16777392) (ELit 16777216) 17%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 16777392 16777216 17%nat (pref 16777216 (dropz 16777216 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 17%nat) with (gblobs content 17%nat). rewrite (gblobs_cb 9) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 16777216 (dropz 16777216 content))) with (Z.to_nat 16777216) by lia.
          replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 176)) (ridx 23) (bx 176)) (ridx 19) (ELit 33554432)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 9) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 9) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin9 : forall R M V B e M0 K,
    half 9 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (16777216 <= L < 33554432)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 9 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 16777216 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 33558528 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 33558528%Z 16777392%Z (Z.to_nat 16777216) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z in SOKb by lia.
    replace (Z.to_nat 16777216) with (Z.to_nat (33554432 - 16777216)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 176 (ELit 16777216) 16%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 16%nat) with (gblobs content 16%nat) in HELD. rewrite (gblobs_hb 9) in HELD by lia. change (held_of 9) with 16777216%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 16777216) R M (bv_unsigned sp0) (bv_unsigned B + 176) 16777216 33554432 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 176 + 16777216), 16777216%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 16777392 16777216)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 16777392)%Z with (bv_unsigned B + 176 + 16777216)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 9)%Z with (bv_unsigned B + 176)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 176) 16777216); try lia; [|exact PM].
        replace (Z.to_nat 16777216) with (length (pref 16777216 content)) by (pose proof (pref_length 16777216 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 9) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF9.

Module RefReadF10.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Amb OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Nodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FileSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AgentLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MemSplit OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefNodes OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibKnowXfer OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadStage OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefReadChunkW RefReadChunk RefReadFrame RefReadG0.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.

Section WithFP1. Context {FP : PropExec.FPState}.
Lemma loop_kept_no0 : ~ In (0%bv : reg) loop_kept.
Proof.
  unfold loop_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
Lemma map_nth_seq0 : forall {A} (l : list A) (d : A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A l d. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. cbn [nth]. exact IH.
Qed.

Lemma map_vals_ev_seq : forall vals, length vals = 41%nat -> map (vals_ev vals) (seq 0 41) = vals.
Proof. intros vals HL. rewrite <- HL. unfold vals_ev. apply map_nth_seq0. Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac rewrite_pins := repeat match goal with P : vals_ev ?v ?i = _ |- context [vals_ev ?v ?i] => rewrite !P end.

Section WithFP2. Context {FP : PropExec.FPState}.
Section F.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  Definition post_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post j' sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Definition full_branch (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, full j' sp0 p1 mb gm L B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG (cap_of j') V)) K.

  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.

  (* [comment removed for export] *)
  Ltac regq HR :=
    lazymatch goal with |- getr _ ?rr = _ =>
      regv HR rr; rewrite ?edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with E := _ : env |- _ => subst E | _ => idtac end; cbn [ev];
      rewrite_pins; first [reflexivity | f_equal; lia | apply bv_eq; rewrite ?u_small by lia; lia] end.

  Theorem fill10 : forall R M V B e M0 K,
    half 10 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (67108864 <= L)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    full_branch 10 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 33554432 V)) K.
  Proof.
    intros R M V B e M0 K ST HL64 HspR HFB.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 67112960 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 67112960%Z 33554624%Z (Z.to_nat 33554432) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z in SOKb by lia.
    replace (Z.to_nat 33554432) with (Z.to_nat (67108864 - 33554432)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 192 (ELit 33554432) 18%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 18%nat) with (gblobs content 18%nat) in HELD. rewrite (gblobs_hb 10) in HELD by lia. change (held_of 10) with 33554432%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 33554432) R M (bv_unsigned sp0) (bv_unsigned B + 192) 33554432 67108864 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *)
      intros HcL R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HFB R' M' V B e). split; [| split; [eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia] | exact VS]].
      pose proof (proj1 PM) as FR. pose proof (proj2 PM) as RD. cbn zeta in RD.
      change ((67108864 - 33554432)%Z) with (33554432%Z) in FR. change ((67108864 - 33554432)%Z) with (33554432%Z) in RD.
      (* [comment removed for export] *)
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 33554624 33554432)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z by lia. exact FR. }
      norm_know HK'.
      assert (RLc : Z.of_nat (length (pref 33554432 (dropz 33554432 content))) = 33554432%Z)
        by (pose proof (pref_length 33554432 (dropz 33554432 content) ltac:(lia)); pose proof (dropz_length 33554432 content ltac:(lia)); lia).
      assert (KBc : kentry_ok RSEGS E M' (KBlob (SA (EVar 5) 33554624) (ELit 33554432) 19%nat)).
      { apply (kblob_of_rdn E M' (EVar 5) B 33554624 33554432 19%nat (pref 33554432 (dropz 33554432 content))).
        - cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        - change (eb E 19%nat) with (gblobs content 19%nat). rewrite (gblobs_cb 10) by lia. reflexivity.
        - exact RLc.
        - lia.
        - lia.
        - replace (length (pref 33554432 (dropz 33554432 content))) with (Z.to_nat 33554432) by lia.
          replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z by lia. exact RD. }
      pose proof (know_ok_cons _ _ _ _ _ KBc HK') as HK2. clear HK' KBc.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr _ =>
        pose proof (regs_after_keeps vals (gblobs content) sr R R' loop_kept ltac:(rewrite HL; vm_compute; reflexivity) HR QK loop_kept_no0) as HR' end.
      rewrite HL in HR'.
      lazymatch type of HK2 with know_ok _ _ _ ?kn =>
        pose proof (env_app_know RSEGS vals (junk_vals R') _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
      clear HK HK2 HR HELD SOKs SOKb VALS HLx extra. subst E.
      grow_vals HL (junk_vals R') 73%nat.
      set (E := Env (vals_ev vals) (gblobs content)) in *.
      lazymatch type of HR' with regs_ok _ ?sr _ =>
        assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd sr (ridx 2) (spx (-128))) (ridx 9) (bx 192)) (ridx 23) (bx 192)) (ridx 19) (ELit 67108864)) R') end.
      { apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [exact HR'|]|]|]|].
        - rewrite Q2. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
        - rewrite Q9. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q23. unfold bx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P5. reflexivity.
        - rewrite Q19. reflexivity. }
      clear HR'. norm_regs HR. rename HK3 into HK. norm_know HK.
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?srf _ =>
      lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
        set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8] ++ srf);
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
        exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
        replace (ENV_RD sp0 p1 mb gm L B e sec cnr (map (edenot E) srf) content) with (xenv E rvl (gblobs content));
        [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_FULL 10) _ HR); [reflexivity | reflexivity |]
                 | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_FULL 10) XB HK) ]
        | ]
      end end.
      + intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
      + match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
      + unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
        cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P5, P6, P7, P8. reflexivity.
    - (* [comment removed for export] *) intros HLc. exfalso. lia.
  Qed.

  Theorem fin10 : forall R M V B e M0 K,
    half 10 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (33554432 <= L < 67108864)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    post_branch 10 M0 K ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG 33554432 V)) K.
  Proof.
    intros R M V B e M0 K ST HL2 HspR HPOST.
    assert (HLdef : L = Z.of_nat (length content)) by reflexivity.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = sec) by reflexivity.
    assert (P8 : vals_ev vals 8 = cnr) by reflexivity.
    assert (VALS : vals = [sp0; p1; mb; gm; Z_to_bv 64 L; B; e; sec; cnr] ++ extra) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB. unfold CEIL in KB.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBs.
    cbn [kentry_ok] in KBs. unfold estart in KBs. cbn [a_base a_off BA LA MBA edenot ev] in KBs. subst E. cbn [ev] in KBs. rewrite P5, P0 in KBs.
    assert (HBtop : (bv_unsigned B + 67112960 <= bv_unsigned sp0 - 8388608)%Z) by (unfold BAND in *; lia).
    clear KBs.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in exact i) (EVar 0) (-8388608)%Z 8388608%Z (-136)%Z 8%nat HK eq_refl ltac:(lia) ltac:(lia)) as SOKs;
      pose proof (kwr_store_ok RSEGS E M kn ltac:(let i := kidx kn (is_kwr_cov (EVar 5) 0%Z 1%Z) in exact i) (EVar 5) 0%Z 67112960%Z 33554624%Z (Z.to_nat 33554432) HK eq_refl ltac:(lia) ltac:(lia)) as SOKb end.
    unfold adenot, v_addi in SOKs, SOKb. cbn [a_base a_off edenot ev] in SOKs, SOKb. subst E. cbn [ev] in SOKs, SOKb.
    rewrite P0 in SOKs. rewrite P5 in SOKb.
    replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z in SOKs by lia.
    replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z in SOKb by lia.
    replace (Z.to_nat 33554432) with (Z.to_nat (67108864 - 33554432)) in SOKb by lia.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      pose proof (kblob_rdn RSEGS E M kn (EVar 5) 192 (ELit 33554432) 18%nat HK ltac:(vm_compute; reflexivity)) as HELD end.
    change (eb E 18%nat) with (gblobs content 18%nat) in HELD. rewrite (gblobs_hb 10) in HELD by lia. change (held_of 10) with 33554432%Z in HELD.
    unfold adenot, v_addi in HELD. cbn [a_base a_off edenot ev] in HELD. subst E. cbn [ev] in HELD. rewrite P5 in HELD.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    apply (chunk_loop path content stdin0 fs0 tid V Hfile (Z.to_nat 33554432) R M (bv_unsigned sp0) (bv_unsigned B + 192) 33554432 67108864 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [|split; [|split; [|split]]]]; regq HR.
    - lia.
    - lia.
    - unfold RS. lia.
    - lia.
    - lia.
    - lia.
    - exact SOKs.
    - apply data_store_ok; unfold RS; lia.
    - exact SOKb.
    - (* [comment removed for export] *) intros HcL. exfalso. lia.
    - (* [comment removed for export] *)
      intros HLc R' M' (Q2 & Q9 & Q23 & Q19 & QK) PM.
      apply (HPOST R' M' V B e).
      pose proof (proj1 PM) as FR.
      (* [comment removed for export] *)
      assert (FRw : frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (bv_unsigned B + 192 + 33554432), 33554432%Z)]).
      { eapply frame_mod_weaken; [|exact FR]. intros a (O1 & O2 & O3 & _). cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [|exact I].
        unfold in_rng in *. rewrite !u_small in * by (unfold RS; lia). lia. }
      lazymatch type of HK with know_ok _ _ _ ?kn =>
        assert (HK' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn (EVar 0) (-136) 8) (ELit 0) 0x208d9 65536) (EVar 5) 33554624 33554432)) end.
      { eapply know_ok_frame3; [exact HK | | | |].
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P0; lia.
        - apply flat_intro; cbn [edenot ev]; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
        - apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia.
        - unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0, P5.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. replace (0 + 0x208d9)%Z with RS by (unfold RS; lia).
          replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
          replace (bv_unsigned B + 33554624)%Z with (bv_unsigned B + 192 + 33554432)%Z by lia. exact FRw. }
      norm_know HK'.
      constructor.
      + exact Q2.
      + rewrite (QK 3%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 4%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 8%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q9. unfold off_of. f_equal; lia.
      + rewrite (QK 18%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite Q19. reflexivity.
      + rewrite (QK 20%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 21%bv) by (cbv; noncert_qtauto). regq HR.
      + rewrite (QK 22%bv) by (cbv; noncert_qtauto). regq HR.
      + exact Q23.
      + (* [comment removed for export] *)
        replace (bv_unsigned B + off_of 10)%Z with (bv_unsigned B + 192)%Z by (unfold off_of; lia).
        eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned B + 192) 33554432); try lia; [|exact PM].
        replace (Z.to_nat 33554432) with (length (pref 33554432 content)) by (pose proof (pref_length 33554432 content ltac:(lia)); lia).
        exact HELD.
      + eapply (pres_loop_post content M0 M M' sp0); [exact PRES | exact PM | lia | lia | lia | lia].
      + exists extra. split; [exact HLx|].
        set (rvl := map EVar (seq 0 41)).
        assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity).
        replace (ENV_RD sp0 p1 mb gm (Z.of_nat (length content)) B e sec cnr extra content) with (xenv E rvl (gblobs content)).
        2: { unfold ENV_RD, xenv. f_equal. apply (f_equal vals_ev). subst rvl. rewrite map_map. subst E. cbn [edenot ev].
             transitivity vals; [apply (map_vals_ev_seq vals HL) | exact VALS]. }
        lazymatch type of HK' with know_ok _ _ ?Mf ?knf =>
          apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_POST 10) XB HK') end.
        match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end.
        apply Forall_nil.
      + exact VS.
  Qed.

  (* [comment removed for export] *)
  Theorem refused10 : forall R M V B e M0 TREF,
    full 10 sp0 p1 mb gm L B e sec cnr content M0 R M V ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (forall R' M' off V', refused_leaf sp0 M0 R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12cd0) M' (seg_rom RSEGS)) (modelG off V')) TREF) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b1c) M (seg_rom RSEGS)) (modelG 67108864 V)) TREF.
  Proof.
    intros R M V B e M0 TREF ST HspR HREF.
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb gm L B e sec cnr extra) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    clearbody vals.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => set (M1 := Mc) in * end.
    (* [comment removed for export] *)
    pose proof (conj HK I) as HKb. run_block_keep scr0 41%nat.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mn _) _) _ =>
      assert (PRES2 : pres M0 Mn sp0)
        by (rewrite EQM; eapply (pres_mem_denot_trans E M0 M1 _ _ sp0 (proj1 HKb)); [subst E; exact P0 | exact HspR | vm_compute; reflexivity | exact PRES]) end.
    clear HKb.
    apply HREF. split; [|split; [|split; [|split]]].
    + regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. subst E. cbn [ev]. rewrite P0. f_equal; lia.
    + regv HR (3 : reg). reflexivity.
    + regv HR (4 : reg). reflexivity.
    + exact PRES2.
    + intros d m Hd Hm.
      lazymatch type of HK with know_ok _ ?E' ?Mc ?kn =>
        let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
        pose proof (kwr_store_ok RSEGS E' Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
      unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST. subst E. cbn [ev] in ST. rewrite P0 in ST.
      replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
  Qed.
End F.
End WithFP2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefReadF10.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim AllocSim FileSim AgentLib MemSplit Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib RefNodes LibKnowFrame LibKnowXfer RefReadLib RefReadDefs RefReadBase RefReadStage. Import RefReadChunk. Import RefRead0. Import RefReadG0. Import RefReadG1. Import RefReadG2. Import RefReadG3. Import RefReadG4. Import RefReadG5. Import RefReadG6. Import RefReadG7. Import RefReadG8. Import RefReadG9. Import RefReadF1. Import RefReadF2. Import RefReadF3. Import RefReadF4. Import RefReadF5. Import RefReadF6. Import RefReadF7. Import RefReadF8. Import RefReadF9. Import RefReadF10.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section Big.
  Context {AMB : Amb}.
  Variables (sp0 p1 mb gm sec cnr : word) (path content : list byte).
  Variables (stdin0 : InputStream) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (RefReadDefs.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition post_cont (k : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, read_post k sp0 p1 mb gm B e sec cnr content M0 R M V ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b84) M (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K.

  Section Stages.
    Variables (M0 : word -> option byte) (K TREF : TSet).
    Hypothesis Hmb0 : (0x52000 <= bv_unsigned mb)%Z.
    Hypothesis Hmb1 : (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z.
    Hypothesis Hmba : (bv_unsigned mb mod 4096 = 0)%Z.
    Hypothesis HspR : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
    Hypothesis HREF : forall R' M' off V', refused_leaf sp0 M0 R' M' ->
      realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12cd0) M' (seg_rom RSEGS)) (modelG off V')) TREF.
    Hypothesis HPOST : forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont k M0 K.

    (* [comment removed for export] *)
    Definition FINAL : TSet := if (L <? 67108864)%Z then K else TREF.

    Lemma HS10 : forall R M V B e, half 10 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (33554432 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 10) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 10) with 33554432%Z.
      destruct (Z.ltb_spec L 67108864) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF10.fin10 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF10.post_branch. apply (HPOST 10); [lia|].
        change (65536 * 2 ^ (10 - 1))%Z with 33554432%Z. change (65536 * 2 ^ 10)%Z with 67108864%Z. lia.
      - (* [comment removed for export] *)
        replace FINAL with TREF by (unfold FINAL; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
        apply (RefReadF10.fill10 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 TREF ST ltac:(lia) HspR).
        unfold RefReadF10.full_branch. intros R' M' V' B' e' ST'. change (cap_of 10) with 67108864%Z.
        exact (RefReadF10.refused10 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 TREF ST' HspR HREF).
    Qed.

    Lemma HS9 : forall R M V B e, half 9 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (16777216 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 9) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 9) with 16777216%Z.
      destruct (Z.ltb_spec L 33554432) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF9.fin9 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF9.post_branch. apply (HPOST 9); [lia|].
        change (65536 * 2 ^ (9 - 1))%Z with 16777216%Z. change (65536 * 2 ^ 9)%Z with 33554432%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF9.fill9 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF9.full_branch. intros R' M' V' B' e' ST'. change (cap_of 9) with 33554432%Z.
        apply (RefReadG9.grow9 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG9.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS10 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS8 : forall R M V B e, half 8 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (8388608 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 8) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 8) with 8388608%Z.
      destruct (Z.ltb_spec L 16777216) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF8.fin8 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF8.post_branch. apply (HPOST 8); [lia|].
        change (65536 * 2 ^ (8 - 1))%Z with 8388608%Z. change (65536 * 2 ^ 8)%Z with 16777216%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF8.fill8 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF8.full_branch. intros R' M' V' B' e' ST'. change (cap_of 8) with 16777216%Z.
        apply (RefReadG8.grow8 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG8.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS9 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS7 : forall R M V B e, half 7 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (4194304 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 7) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 7) with 4194304%Z.
      destruct (Z.ltb_spec L 8388608) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF7.fin7 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF7.post_branch. apply (HPOST 7); [lia|].
        change (65536 * 2 ^ (7 - 1))%Z with 4194304%Z. change (65536 * 2 ^ 7)%Z with 8388608%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF7.fill7 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF7.full_branch. intros R' M' V' B' e' ST'. change (cap_of 7) with 8388608%Z.
        apply (RefReadG7.grow7 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG7.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS8 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS6 : forall R M V B e, half 6 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (2097152 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 6) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 6) with 2097152%Z.
      destruct (Z.ltb_spec L 4194304) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF6.fin6 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF6.post_branch. apply (HPOST 6); [lia|].
        change (65536 * 2 ^ (6 - 1))%Z with 2097152%Z. change (65536 * 2 ^ 6)%Z with 4194304%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF6.fill6 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF6.full_branch. intros R' M' V' B' e' ST'. change (cap_of 6) with 4194304%Z.
        apply (RefReadG6.grow6 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG6.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS7 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS5 : forall R M V B e, half 5 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (1048576 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 5) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 5) with 1048576%Z.
      destruct (Z.ltb_spec L 2097152) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF5.fin5 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF5.post_branch. apply (HPOST 5); [lia|].
        change (65536 * 2 ^ (5 - 1))%Z with 1048576%Z. change (65536 * 2 ^ 5)%Z with 2097152%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF5.fill5 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF5.full_branch. intros R' M' V' B' e' ST'. change (cap_of 5) with 2097152%Z.
        apply (RefReadG5.grow5 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG5.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS6 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS4 : forall R M V B e, half 4 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (524288 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 4) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 4) with 524288%Z.
      destruct (Z.ltb_spec L 1048576) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF4.fin4 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF4.post_branch. apply (HPOST 4); [lia|].
        change (65536 * 2 ^ (4 - 1))%Z with 524288%Z. change (65536 * 2 ^ 4)%Z with 1048576%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF4.fill4 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF4.full_branch. intros R' M' V' B' e' ST'. change (cap_of 4) with 1048576%Z.
        apply (RefReadG4.grow4 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG4.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS5 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS3 : forall R M V B e, half 3 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (262144 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 3) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 3) with 262144%Z.
      destruct (Z.ltb_spec L 524288) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF3.fin3 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF3.post_branch. apply (HPOST 3); [lia|].
        change (65536 * 2 ^ (3 - 1))%Z with 262144%Z. change (65536 * 2 ^ 3)%Z with 524288%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF3.fill3 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF3.full_branch. intros R' M' V' B' e' ST'. change (cap_of 3) with 524288%Z.
        apply (RefReadG3.grow3 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG3.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS4 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS2 : forall R M V B e, half 2 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (131072 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 2) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 2) with 131072%Z.
      destruct (Z.ltb_spec L 262144) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF2.fin2 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF2.post_branch. apply (HPOST 2); [lia|].
        change (65536 * 2 ^ (2 - 1))%Z with 131072%Z. change (65536 * 2 ^ 2)%Z with 262144%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF2.fill2 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF2.full_branch. intros R' M' V' B' e' ST'. change (cap_of 2) with 262144%Z.
        apply (RefReadG2.grow2 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG2.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS3 R'' M'' V'' B'' e'' ST''). lia.
    Qed.

    Lemma HS1 : forall R M V B e, half 1 sp0 p1 mb gm L B e sec cnr content M0 R M V -> (65536 <= L)%Z ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12b54) M (seg_rom RSEGS)) (modelG (held_of 1) V)) FINAL.
    Proof.
      intros R M V B e ST HGE. change (held_of 1) with 65536%Z.
      destruct (Z.ltb_spec L 131072) as [HLT|HGE2].
      - (* [comment removed for export] *)
        replace FINAL with K by (unfold FINAL; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        apply (RefReadF1.fin1 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 K ST ltac:(lia) HspR).
        unfold RefReadF1.post_branch. apply (HPOST 1); [lia|].
        change (65536 * 2 ^ (1 - 1))%Z with 65536%Z. change (65536 * 2 ^ 1)%Z with 131072%Z. lia.
      - (* [comment removed for export] *)
        apply (RefReadF1.fill1 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid Hfile R M V B e M0 FINAL ST ltac:(lia) HspR).
        unfold RefReadF1.full_branch. intros R' M' V' B' e' ST'. change (cap_of 1) with 131072%Z.
        apply (RefReadG1.grow1 sp0 p1 mb gm sec cnr path content stdin0 fs0 tid R' M' V' B' e' M0 FINAL ST' ltac:(lia) Hmb0 Hmb1 Hmba HspR).
        unfold RefReadG1.half_branch. intros R'' M'' V'' B'' e'' ST''. apply (HS2 R'' M'' V'' B'' e'' ST''). lia.
    Qed.
  End Stages.

  Theorem read_big : forall R M VM K TREF,
    read_pre sp0 p1 mb gm sec cnr R M -> vm_pre VM sp0 mb gm ->
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (65536 <= L)%Z ->
    (forall R' M' off V', refused_leaf sp0 M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x12cd0) M' (seg_rom RSEGS)) (modelG off V')) TREF) ->
    (forall k, (1 <= k <= 10)%Z -> (65536 * 2 ^ (k - 1) <= L < 65536 * 2 ^ k)%Z -> post_cont k M K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x12adc) M (seg_rom RSEGS)) (modelG 0 VM))
             (if (L <? 67108864)%Z then K else TREF).
  Proof.
    intros R M VM K TREF RP VP Hpage0 HL64 HREF HPOST.
    pose proof (rp_sp0 _ _ _ _ _ _ _ _ RP) as Hsp. pose proof (rp_b _ _ _ _ _ _ _ _ RP) as Hmb. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm.
    destruct (rp_errno _ _ _ _ _ _ _ _ RP) as [e He].
    change (modelG 0 VM) with (model_pre path VM stdin0 fs0 tid).
    apply (RefRead0.read_full0 sp0 p1 mb gm sec cnr path content VM stdin0 fs0 tid Hfile R M _ e RP HL64 He Hpage0).
    intros R' M' F0 _.
    apply (RefReadG0.grow0 sp0 p1 mb gm sec cnr path content VM stdin0 fs0 tid R' M' e M (FINAL K TREF) F0 VP HL64
             (proj1 Hsp) (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hgm) (proj1 (proj2 Hgm)) (proj2 (proj2 Hgm))).
    unfold RefReadG0.half1_branch. intros R'' M'' V'' B'' e'' ST''.
    apply (HS1 M K TREF (proj1 Hmb) (proj1 (proj2 Hmb)) (proj2 (proj2 Hmb)) (proj1 Hsp) HREF HPOST R'' M'' V'' B'' e'' ST''). lia.
  Qed.
End Big.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
