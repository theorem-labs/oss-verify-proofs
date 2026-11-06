(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MemSplit LibMaskBits.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib SpecConsts SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibKnowFrame RefReadLib RefReadBase RefReadStage RefReadChunkW Ref_code_235f0_2427c.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX RefMemcpyBase RefMemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dropz_dropz : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  dropz a (dropz b l) = dropz (b + a) l.
Proof.
  intros a b l Ha Hb. unfold dropz. rewrite skipn_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pref_chain : forall (len n m : Z) l, (0 <= len)%Z -> (0 <= n)%Z -> (0 <= m)%Z ->
  pref n (dropz len l) ++ pref m (dropz (len + n) l) = pref (n + m) (dropz len l).
Proof.
  intros len n m l Hl Hn Hm. rewrite <- (dropz_dropz n len) by lia. apply pref_app; lia.
Qed.

Lemma pref_0 : forall l, pref 0 l = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_chunk : forall content (len want : Z),
  (0 <= len <= Z.of_nat (length content))%Z -> (len < 2 ^ 62)%Z -> (0 <= want < 2 ^ 62)%Z ->
  let bs := file_read content (Z_to_bv 64 len) (Z_to_bv 64 want) in
  let n := Z.of_nat (length bs) in
  n = Z.min want (Z.of_nat (length content) - len) /\ bs = pref n (dropz len content).
Proof.
  intros content len want Hlen Hlen2 Hwant. cbn zeta.
  rewrite file_read_pref by lia.
  pose proof (pref_length want (dropz len content) ltac:(lia)) as PL.
  pose proof (dropz_length len content ltac:(lia)) as DL.
  split; [lia|].
  destruct (Z.le_gt_cases want (Z.of_nat (length content) - len)) as [Hle|Hgt].
  - f_equal. lia.
  - rewrite (pref_all want) by lia. symmetry. apply pref_all. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mid_regs (R : bvmap 5 word) (sp0 buf len cap : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (sp0 - 128) /\ getr R 9 = Z_to_bv 64 buf /\ getr R 19 = Z_to_bv 64 len
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 RSTAGE.

(* [comment removed for export] *)
Definition loop_post_regs (R R' : bvmap 5 word) (sp0 buf len' : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf
  /\ getr R' 19 = Z_to_bv 64 len'
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition loop_post_mem (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z); (Z_to_bv 64 RSTAGE, 65536%Z)]
  /\ rdn RSEGS M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop_kept_B : forall r, In r loop_kept -> In r loopB_kept /\ r <> 19%bv.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [split; [cbv [loopB_kept In]; noncert_qtauto | intros Hc; apply (f_equal bv_unsigned) in Hc; discriminate Hc]|]). destruct Hr.
Qed.

Lemma loop_kept_callee : forall r, In r loop_kept -> In r callee_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [callee_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma kept_regupd10 : forall X (v : word) r, In r loop_kept -> getr (regupd X 10 v) r = getr X r.
Proof.
  intros X v r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [rewrite getr_other by reg_neq_tac; reflexivity|]). destruct Hr.
Qed.

Lemma post_regs_compose : forall R R2 R' sp0 buf len',
  loop_post_regs R2 R' sp0 buf len' ->
  (forall r, In r loop_kept -> getr R2 r = getr R r) ->
  loop_post_regs R R' sp0 buf len'.
Proof.
  intros R R2 R' sp0 buf len' (P2 & P9 & P19 & PK) HK.
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
  Hypothesis Hbuf : (0x58000 <= buf)%Z.
  Hypothesis Hsp : (sp0 <= 2 ^ 47)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  #[local] Notation M3 := (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 RSTAGE) bs)
                                  (Z_to_bv 64 (buf + len)) bs) (only parsing).

  (* [comment removed for export] *)
  Lemma post_mem_here : (buf + len + n <= sp0 - 136)%Z -> (136 <= sp0)%Z ->
    loop_post_mem content M M3 sp0 buf len (len + n).
  Proof.
    intros Hb Hsp2. pose proof (length_N_to_le_bytes 8 ra) as L8. unfold RSTAGE in *. split.
    - eapply frame_mod_weaken; [|apply frame_three; rewrite ?L8, ?Hbl, ?u_small by lia; lia].
      intros a [O1 [O2 [O3 _]]]. cbn [outside] in *. rewrite L8, Hbl. unfold in_rng, RSTAGE in *. rewrite ?u_small in * by lia.
      replace (len + n - len)%Z with n in O2 by lia. repeat split; lia.
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 136)%Z -> (136 <= sp0)%Z ->
    loop_post_mem content M3 M' sp0 buf (len + n) len' ->
    loop_post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' Hsp2 [FR RD]. pose proof (length_N_to_le_bytes 8 ra) as L8. unfold RSTAGE in *. split.
    - eapply frame_mod_weaken.
      2: { eapply frame_mod_trans; [ | exact FR ]. apply frame_three; rewrite ?L8, ?Hbl, ?u_small by lia; lia. }
      intros a [O1 [O2 [O3 _]]]. cbn [outside app]. rewrite L8, Hbl. unfold in_rng, RSTAGE in *. rewrite !u_small in * by lia.
      repeat split; lia.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn RSEGS M3 M' _ (length bs) (Z_to_bv 64 (buf + len)) FR).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. cbn [outside]. unfold in_rng. rewrite ?Hbl, !u_small by lia. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

(* [comment removed for export] *)
Lemma post_mem_end : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (len <= Z.of_nat (length content))%Z -> (sp0 <= 2 ^ 47)%Z -> (136 <= sp0)%Z ->
  (len = Z.of_nat (length content))%Z ->
  loop_post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl HlL Hsp Hsp' HL.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2. split.
  - eapply frame_mod_weaken; [|eapply frame_mod_trans; apply frame_mod_wbytes; rewrite ?L1, ?L2, u_small by lia; lia].
    intros a [O1 _]. cbn [outside app]. rewrite L1, L2. noncert_qtauto.
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

Section ChunkLoop.
  Context {AMB : Amb}.
  Variables (path content : list byte) (stdin0 : InputStream) (fs0 : Fs) (tid : word) (V : VmMaps).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  #[local] Notation L := (Z.of_nat (length content)) (only parsing).
  #[local] Notation modelG := (RefReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Lemma stage_store_ok : forall m n, (Z.of_nat n <= 65536)%Z -> store_ok RSEGS m (Z_to_bv 64 RSTAGE) n = true.
  Proof. intros m n Hn. apply data_store_ok; unfold RSTAGE; lia. Qed.

  Theorem chunk_loop_mid : forall (fuel : nat) (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    mid_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0x58000 <= buf)%Z -> (buf + cap <= sp0 - 8388608)%Z ->
    (sp0 <= 2 ^ 47)%Z ->
    (len <= L)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok RSEGS M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->
    (* [comment removed for export] *)
    ((cap <= L)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf cap -> getr R' 23 = Z_to_bv 64 buf -> loop_post_mem content M M' sp0 buf len cap ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13a74) M' (seg_rom RSEGS)) (modelG cap V)) K) ->
    (* [comment removed for export] *)
    ((L < cap)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf L -> getr R' 23 = Z_to_bv 64 0 -> loop_post_mem content M M' sp0 buf len L ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13adc) M' (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13aac) M (seg_rom RSEGS)) (modelG len V)) K.
  Proof.
    induction fuel as [|fuel IH]; intros R M sp0 buf len cap K Hfuel (R2 & R9 & R19 & R20 & R21 & R22) Hlen Hcap Hbuf Hbc Hsp HlenL SOKs SOKb HFULL HEND.
    { exfalso. cbn in Hfuel. lia. }
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    pose proof rw_bytes_max_ge17 as HRW.
    (* [comment removed for export] *)
    destruct (walkA R M (seg_rom RSEGS) sp0 buf len cap R2 R19 R21 R9 R20 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A9 & A19 & AK0).
    assert (AK : forall r, In r loop_kept -> getr R1 r = getr R r) by (intros r Hr; apply AK0; right; exact Hr).
    assert (A23 : getr R1 23 = getr R 23) by (apply AK0; left; reflexivity).
    replace (Z_to_bv 64 0x13aac) with (0x13aac : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13ac8))).
    assert (SOK1s : store_ok RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = true)
      by (eapply store_ok_mono; [apply wbytes_grows | exact SOKs]).
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ac8)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (rz_read_file RSEGS R1 (0x24098 : word) M1 (modelG len V) W_24098 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_24098 E_24098).
    - reflexivity.
    - reflexivity.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - lia.
    - rewrite A11. unfold RSTAGE. rewrite u_small by lia. unfold TASK_SIZE. lia.
    - rewrite A11. apply stage_store_ok. lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite modelG_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (mkModelC (fds_file path (Z_to_bv 64 (len + n))) V stdin0 fs0 None (Some tid) None) with (modelG (len + n) V).
      replace (v_addi (0x24098 : word) 4) with (0x2409c : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 RSTAGE) bs).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + (* [comment removed for export] *)
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        destruct (walkBC (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom RSEGS) sp0 buf len
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C19 & C9 & C23 & CK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13adc))).
        (* [comment removed for export] *)
        eapply (rz_close RSEGS R3 (0x24098 : word) M3 (modelG (len + 0) V) W_24098 (Z_to_bv 64 3) _ K F_24098 E_24098).
        * reflexivity.
        * reflexivity.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite modelG_close.
          replace (v_addi (0x24098 : word) 4) with (0x2409c : word) by (apply bv_eq; reflexivity).
          destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom RSEGS) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN4 |]. clear RUN4.
          replace (0x13adc : word) with (Z_to_bv 64 0x13adc) by (apply bv_eq; reflexivity).
          apply (HEND ltac:(lia) R4 M3).
          -- (* [comment removed for export] *)
             split; [exact D2|]. split; [|split].
             ++ rewrite (DK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C9.
             ++ rewrite (DK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite C19. f_equal. lia.
             ++ intros r Hr. destruct (loop_kept_B r Hr) as [HrB _].
                rewrite (DK r) by (cbn [In]; right; exact HrB).
                rewrite (kept_regupd10 _ _ r Hr). rewrite (CK r HrB). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr.
          -- rewrite (DK 23%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C23.
          -- (* [comment removed for export] *)
             subst M3 M1. rewrite <- HLe. apply post_mem_end; lia.
      + (* [comment removed for export] *)
        assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ac8))).
        { subst M2. rewrite rdn_wbytes_out; [exact RD1 | unfold RSTAGE; rewrite !u_small by lia; lia | rewrite u_small by lia; lia | unfold RSTAGE; rewrite u_small by lia; lia]. }
        destruct (walkB (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom RSEGS) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RD2)
          as (R5 & RUN5 & B1 & B2 & B10 & B11 & B12 & B23 & BK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
        (* [comment removed for export] *)
        assert (MC : mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RSTAGE) n bs).
        { constructor.
          - lia.
          - lia.
          - subst M2. apply rdn_wbytes_self. unfold RSTAGE. rewrite u_small by lia. lia.
          - subst M2 M1. eapply store_ok_mono; [eapply mem_grows_trans; apply wbytes_grows|].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - unfold RSTAGE. rewrite !u_small by lia. lia.
          - unfold RSTAGE. rewrite u_small by lia. lia.
          - rewrite u_small by lia. lia. }
        assert (RT : ret_ok (Z_to_bv 64 0x13a60)) by (apply bv_eq; vm_compute; reflexivity).
        destruct (ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RSTAGE) n bs (seg_rom RSEGS) MC R5 (Z_to_bv 64 0x13a60)
                    RT B1 B10 B11 B12) as (R6 & RUN6 & KEEP6).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN6 |]. clear RUN6.
        set (M3 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        assert (BKK : forall r, In r loop_kept -> getr R6 r = getr R r).
        { intros r Hr. destruct (loop_kept_B r Hr) as [HrB _]. rewrite (KEEP6 r (loop_kept_callee r Hr)).
          rewrite (BK r HrB). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        assert (E19 : getr R6 19 = Z_to_bv 64 len).
        { rewrite (KEEP6 19%bv) by (cbv; noncert_qtauto). rewrite (BK 19%bv) by (cbv; noncert_qtauto). gres. exact A19. }
        assert (E9 : getr R6 9 = Z_to_bv 64 buf).
        { rewrite (KEEP6 9%bv) by (cbv; noncert_qtauto). rewrite (BK 9%bv) by (cbv; noncert_qtauto). gres. exact A9. }
        assert (E23 : getr R6 23 = Z_to_bv 64 n) by (rewrite (KEEP6 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (E21 : getr R6 21 = Z_to_bv 64 cap) by (rewrite (BKK 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (E2 : getr R6 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (KEEP6 2%bv) by (cbv; noncert_qtauto); exact B2).
        replace (0x13a60 : word) with (Z_to_bv 64 0x13a60) by (apply bv_eq; reflexivity).
        destruct (Z.eq_dec (len + n) cap) as [Hfull|Hmore].
        * (* [comment removed for export] *)
          destruct (walkB2_full R6 M3 (seg_rom RSEGS) buf len n cap E19 E23 E9 E21 ltac:(lia) ltac:(lia) ltac:(lia) Hfull)
            as (R7 & RUN7 & F19 & F23 & FK).
          replace (Z_to_bv 64 0x13a60) with (0x13a60 : word) by (apply bv_eq; reflexivity).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0x13a74 : word) with (Z_to_bv 64 0x13a74) by (apply bv_eq; reflexivity).
          rewrite Hfull.
          apply (HFULL ltac:(lia) R7 M3).
          -- split; [|split; [|split]].
             ++ rewrite (FK 2%bv) by (first [cbv; noncert_qtauto | intros Hc; apply (f_equal bv_unsigned) in Hc; discriminate Hc]). exact E2.
             ++ rewrite (FK 9%bv) by (first [cbv; noncert_qtauto | intros Hc; apply (f_equal bv_unsigned) in Hc; discriminate Hc]). exact E9.
             ++ exact F19.
             ++ intros r Hr. destruct (loop_kept_B r Hr) as [HrB Hr19]. rewrite (FK r ltac:(right; exact HrB) Hr19). apply BKK, Hr.
          -- exact F23.
          -- subst M3 M2 M1. rewrite <- Hfull. apply post_mem_here; try lia. exact RB.
        * (* [comment removed for export] *)
          destruct (walkB2_more R6 M3 (seg_rom RSEGS) buf len n cap E19 E23 E9 E21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hmore)
            as (R7 & RUN7 & G19 & G23 & G9 & GK).
          replace (Z_to_bv 64 0x13a60) with (0x13a60 : word) by (apply bv_eq; reflexivity).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0x13aac : word) with (Z_to_bv 64 0x13aac) by (apply bv_eq; reflexivity).
          assert (GKK : forall r, In r loop_kept -> getr R7 r = getr R r).
          { intros r Hr. destruct (loop_kept_B r Hr) as [HrB Hr19]. rewrite (GK r ltac:(right; exact HrB) Hr19). apply BKK, Hr. }
          assert (GR3 : mem_grows M M3).
          { subst M3 M2 M1. eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [|apply wbytes_grows]. apply wbytes_grows. }
          apply (IH R7 M3 sp0 buf (len + n)%Z cap K ltac:(lia)).
          -- repeat split.
             ++ rewrite (GK 2%bv) by (first [cbv; noncert_qtauto | intros Hc; apply (f_equal bv_unsigned) in Hc; discriminate Hc]). exact E2.
             ++ exact G9.
             ++ exact G19.
             ++ rewrite (GKK 20%bv) by (cbv; noncert_qtauto). exact R20.
             ++ rewrite (GKK 21%bv) by (cbv; noncert_qtauto). exact R21.
             ++ rewrite (GKK 22%bv) by (cbv; noncert_qtauto). exact R22.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- eapply store_ok_mono; [exact GR3 | exact SOKs].
          -- eapply store_ok_mono; [exact GR3 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros HcL R' M' PR P23 PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact GKK].
             ++ exact P23.
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | | exact PM]; lia.
          -- intros HLc R' M' PR P23 PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact GKK].
             ++ exact P23.
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | | exact PM]; lia.
  Qed.
End ChunkLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frame_mod_split3 : forall M M' (a1 : word) (n1 : Z) (a2 : word) (n2 : Z) (a3 : word) (n3 : Z),
  frame_mod M M' [(a1, n1); (a2, n2); (a3, n3)] ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' [(a2, n2); (a3, n3)].
Proof.
  intros M M' a1 n1 a2 n2 a3 n3 [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a [Ha [Hb' _]]. destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|split; [exact Ha | split; [exact Hb' | exact I]]].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

Lemma frame_mod_split2 : forall M M' (a1 : word) (n1 : Z) (a2 : word) (n2 : Z),
  frame_mod M M' [(a1, n1); (a2, n2)] ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' [(a2, n2)].
Proof.
  intros M M' a1 n1 a2 n2 [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|split; [exact Ha | exact I]].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

(* [comment removed for export] *)
Lemma know_ok_frame2 : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z),
  know_ok RSEGS E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2)] ->
  know_ok RSEGS E M' (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 HK F1 F2 FR.
  destruct (frame_mod_split2 _ _ _ _ _ _ FR) as (Mm & [E1 G1] & [E2 G2]).
  pose proof (flat_u E _ _ F1) as U1. pose proof (flat_u E _ _ F2) as U2.
  eapply know_ok_frame; [eapply know_ok_frame; [exact HK | exact F1 | | exact G1] | exact F2 | | exact G2].
  - intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
  - intros x Hx. apply E2. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U2. lia.
Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) (b3 : expr) (k3 n3 : Z),
  know_ok RSEGS E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 -> flat E (SA b3 k3) n3 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2); (adenot E (SA b3 k3), n3)] ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2) b3 k3 n3).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 b3 k3 n3 HK F1 F2 F3 FR.
  destruct (frame_mod_split3 _ _ _ _ _ _ _ _ FR) as (Mm & [E1 G1] & FR2).
  pose proof (flat_u E _ _ F1) as U1.
  eapply (know_ok_frame2 E Mm M' _ b2 k2 n2 b3 k3 n3); [ | exact F2 | exact F3 | exact FR2 ].
  eapply know_ok_frame; [exact HK | exact F1 | | exact G1].
  intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x58000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
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
  (0x58000 <= bv_unsigned a)%Z -> rdn RSEGS M a 1 = Some [b] -> M a = Some b.
Proof.
  intros M a b Ha H. cbn [rdn] in H. destruct (M a) as [b'|] eqn:Hm.
  - injection H as ->. reflexivity.
  - rewrite seg_rom_high in H by exact Ha. discriminate.
Qed.

(* [comment removed for export] *)
Lemma kblob_of_rdn : forall E M (e : expr) (a : word) (off n : Z) (k : nat) (bs : list byte),
  edenot E e = a -> eb E k = bs -> Z.of_nat (length bs) = n ->
  (0x58000 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + n < 2 ^ 64)%Z ->
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
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (0x58000 <= buf + len)%Z -> (buf + len' <= bv_unsigned sp0 - 136)%Z -> (len <= len')%Z ->
  pres M0 M' sp0.
Proof.
  intros content M0 M M' sp0 buf len len' P [[EQ _] _] Hsp Hlo Hhi Hll x Hx.
  pose proof (u64_range sp0) as U.
  rewrite <- (P x Hx). apply EQ. cbn [outside]. unfold in_rng, rd_cell, RSTAGE in *. rewrite !u_small by lia.
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma stack_writable_grows : forall M M' sp0, mem_grows M M' -> stack_writable M sp0 -> stack_writable M' sp0.
Proof. intros M M' sp0 G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma group_writable_grows : forall M M' gm, mem_grows M M' -> group_writable M gm -> group_writable M' gm.
Proof. intros M M' gm G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma meta_writable_grows : forall M M' mb, mem_grows M M' -> meta_writable M mb -> meta_writable M' mb.
Proof. intros M M' mb G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

(* [comment removed for export] *)
Lemma content_at_buf : forall content M M' (sp0 buf held : Z),
  (0 <= held <= Z.of_nat (length content))%Z -> (0x58000 <= buf)%Z -> (buf + Z.of_nat (length content) <= sp0 - 136)%Z -> (sp0 <= 2 ^ 63)%Z ->
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
    intros i Hi. rewrite (u_small buf) by lia. cbn [outside]. unfold in_rng, RSTAGE. rewrite !u_small by lia. repeat split; lia.
  - replace (Z_to_bv 64 buf + nat_to_word (Z.to_nat held)) with (Z_to_bv 64 (buf + held)); [exact RD|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
