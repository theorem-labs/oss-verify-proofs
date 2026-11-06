(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits SumWalkTac RefMemcpyLib U1MemcpyBase SumMemcpyBase SumMemcpy RefNodes RefReadLib SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1SpecConsts U1RBase U1ReadW U1Memcpy U1_code_e3138_e4138 .
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FXALL1.
Context {fx : FPState}.

Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma dropz_dropz : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  dropz a (dropz b l) = dropz (b + a) l.
Proof.
  intros a b l Ha Hb. unfold dropz. rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma pref_chain : forall (len n m : Z) l, (0 <= len)%Z -> (0 <= n)%Z -> (0 <= m)%Z ->
  pref n (dropz len l) ++ pref m (dropz (len + n) l) = pref (n + m) (dropz len l).
Proof.
  intros len n m l Hl Hn Hm. rewrite <- (dropz_dropz n len) by lia. apply pref_app; lia.
Qed.

Lemma pref_0 : forall l, pref 0 l = [].
Proof. intros. reflexivity. Qed.

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

Definition head_regs (R : bvmap 5 word) (sp0 buf len cap : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (sp0 - 128) /\ getr R 9 = Z_to_bv 64 buf /\ getr R 19 = Z_to_bv 64 len
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 RS.

Definition post_regs (R R' : bvmap 5 word) (sp0 buf len' : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf /\ getr R' 19 = Z_to_bv 64 len'
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

Definition post_mem (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 RS, 65536%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z)]
  /\ rdn RSEGS M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

Lemma post_regs_compose : forall R R2 R' sp0 buf len',
  post_regs R2 R' sp0 buf len' ->
  (forall r, In r loop_kept -> getr R2 r = getr R r) ->
  post_regs R R' sp0 buf len'.
Proof.
  intros R R2 R' sp0 buf len' (P2 & P9 & P19 & PK) HK.
  repeat split; try assumption. intros r Hr. rewrite (PK r Hr). apply HK, Hr.
Qed.

Lemma kept_regupd10 : forall X (v : word) r, In r loop_kept -> getr (regupd X 10 v) r = getr X r.
Proof.
  intros X v r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [rewrite getr_other by reg_neq_tac; reflexivity|]). destruct Hr.
Qed.

Lemma frame_two : forall M (a1 a2 : word) bs1 bs2,
  (bv_unsigned a1 + Z.of_nat (length bs1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes (wbytes M a1 bs1) a2 bs2) [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))].
Proof.
  intros M a1 a2 bs1 bs2 H1 H2.
  change [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))] with ([(a1, Z.of_nat (length bs1))] ++ [(a2, Z.of_nat (length bs2))]).
  eapply frame_mod_trans; apply frame_mod_wbytes; assumption.
Qed.

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
  Hypothesis Hbuf : (0x124000 <= buf)%Z.
  Hypothesis Hsp : (0x124000 <= sp0 - 136)%Z.
  Hypothesis Hsp2 : (sp0 <= 2 ^ 63)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  #[local] Notation M3 := (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 RS) bs)
                                  (Z_to_bv 64 (buf + len)) bs) (only parsing).

  Lemma post_mem_here : (buf + len + n <= sp0 - 136)%Z ->
    post_mem content M M3 sp0 buf len (len + n).
  Proof.
    intros Hb. pose proof (length_N_to_le_bytes 8 ra) as L8. split.
    - eapply frame_mod_weaken; [|apply frame_three; rewrite ?L8, ?Hbl; unfold RS; rewrite ?u_small by lia; lia].
      intros a Ha. cbn [outside] in *. rewrite L8, Hbl. replace (len + n - len)%Z with n in Ha by lia.
      destruct Ha as (O1 & O2 & O3 & _). unfold in_rng in *. unfold RS in *. rewrite !u_small in * by lia.
      repeat split; lia.
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 136)%Z ->
    post_mem content M3 M' sp0 buf (len + n) len' ->
    post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' [FR RD]. pose proof (length_N_to_le_bytes 8 ra) as L8. split.
    - eapply frame_mod_weaken.
      2: { eapply frame_mod_trans; [ | exact FR ]. apply frame_three; rewrite ?L8, ?Hbl; unfold RS; rewrite ?u_small by lia; lia. }
      intros a (O1 & O2 & O3 & _). cbn [outside app]. rewrite L8, Hbl. unfold in_rng in *. unfold RS in *.
      rewrite !u_small in * by lia.
      repeat split; lia.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn RSEGS M3 M' _ (length bs) (Z_to_bv 64 (buf + len)) FR).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. cbn [outside]. unfold in_rng. unfold RS.
          rewrite ?Hbl, !u_small by lia. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

Lemma post_mem_end : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (len <= Z.of_nat (length content))%Z -> (sp0 <= 2 ^ 63)%Z -> (0x124000 <= sp0 - 136)%Z ->
  (len = Z.of_nat (length content))%Z ->
  post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl HlL Hsp Hsp' HL.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2. split.
  - eapply frame_mod_weaken; [|apply frame_two; rewrite ?L1, ?L2, u_small by lia; lia].
    intros a (O1 & _). cbn [outside]. rewrite L1, L2. tauto.
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

Section ChunkLoop.
  Context {AMB : Amb}.
  Variables (path content : list byte) (mo : Model).
  Hypothesis Hfile : fs_lookup (m_fs mo) path = Some content.
  Hypothesis Hh : m_halted mo = None.
  Hypothesis Hlz : m_vm_lazy mo = [].

  Let L : Z := Z.of_nat (length content).

  Theorem chunk_loop : forall (fuel : nat) (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    head_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0x124000 <= buf)%Z -> (buf + cap <= sp0 - 144)%Z ->
    (0x124000 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 47)%Z ->
    (len <= L)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok RSEGS M (Z_to_bv 64 RS) (Z.to_nat 65536) = true ->
    store_ok RSEGS M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->

    ((cap <= L)%Z -> forall R' M',
        post_regs R R' sp0 buf cap -> getr R' 23 = Z_to_bv 64 buf -> post_mem content M M' sp0 buf len cap ->
        srealizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x658d0) M' (seg_rom RSEGS)) (at_off path mo cap)) K) ->

    ((L < cap)%Z -> forall R' M',
        post_regs R R' sp0 buf L -> getr R' 23 = Z_to_bv 64 0 -> post_mem content M M' sp0 buf len L ->
        srealizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x65938) M' (seg_rom RSEGS)) (closed3 mo)) K) ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65908) M (seg_rom RSEGS)) (at_off path mo len)) K.
  Proof.
    induction fuel as [|fuel IH]; intros R M sp0 buf len cap K Hfuel (R2 & R9 & R19 & R20 & R21 & R22) Hlen Hcap Hbuf Hbc
      Hsp Hsp2 HlenL SOKs SOKrs SOKb HFULL HEND.
    { exfalso. cbn in Hfuel. lia. }
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    pose proof rw_bytes_max_ge17 as HRW.

    destruct (walkH R M (seg_rom RSEGS) sp0 buf len cap R2 R9 R19 R20 R21 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A9 & A19 & AK).
    replace (Z_to_bv 64 0x65908) with (0x65908 : word) by (apply bv_eq; reflexivity).
    eapply srz_msteps; [exact Hh | exact Hlz | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x65924))).
    assert (GR1 : mem_grows M M1) by apply wbytes_grows.
    assert (SOK1s : store_ok RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = true)
      by (eapply store_ok_mono; [exact GR1 | exact SOKs]).
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65924)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).

    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (srz_read_file RSEGS R1 (0xe3ba4 : word) M1 (at_off path mo len) W_e3b70 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_e3b70 E_e3b70).
    - exact Hh.
    - exact Hlz.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - lia.
    - lia.
    - rewrite A11. unfold RS, TASK_SIZE. rewrite u_small by lia. lia.
    - rewrite A11. eapply store_ok_mono; [exact GR1|].
      apply (store_ok_sub RSEGS M (Z_to_bv 64 RS) (Z_to_bv 64 RS) (Z.to_nat 65536)); [ | exact SOKrs | lia | ];
        unfold RS; rewrite u_small by lia; lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite at_off_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (with_fds (fds_file path (Z_to_bv 64 (len + n))) mo) with (at_off path mo (len + n)).
      replace (v_addi (0xe3ba4 : word) 4) with (0xe3ba8 : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 RS) bs).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      +
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        destruct (walkR0 (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom RSEGS) sp0 buf len
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C19 & C9 & C23 & CK).
        eapply srz_msteps; [exact Hh | exact Hlz | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x65938))).

        eapply (srz_close RSEGS R3 (0xe3ba4 : word) M3 (at_off path mo (len + 0)) W_e3b70 (Z_to_bv 64 3) _ K F_e3b70 E_e3b70).
        * exact Hh.
        * exact Hlz.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite at_off_close.
          replace (v_addi (0xe3ba4 : word) 4) with (0xe3ba8 : word) by (apply bv_eq; reflexivity).
          destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom RSEGS) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply srz_msteps; [exact Hh | exact Hlz | exact RUN4 |]. clear RUN4.
          replace (0x65938 : word) with (Z_to_bv 64 0x65938) by (apply bv_eq; reflexivity).
          apply (HEND ltac:(lia) R4 M3).
          --
             split; [exact D2|]. split; [|split].
             ++ rewrite (DK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C9.
             ++ rewrite (DK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite C19. f_equal. lia.
             ++ intros r Hr. rewrite (DK r) by (cbn [In]; right; right; right; exact Hr).
                rewrite (kept_regupd10 _ _ r Hr). rewrite (CK r Hr). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr.
          -- rewrite (DK 23%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C23.
          --
             subst M3 M1. rewrite <- HLe. apply post_mem_end; lia.
      +
        assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65924))).
        { subst M2. rewrite rdn_wbytes_out; [exact RD1 | .. ]; unfold RS; rewrite ?u_small by lia; lia. }
        destruct (walkRn (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom RSEGS) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RD2)
          as (R5 & RUN5 & B1 & B2 & B10 & B11 & B12 & B9 & B19 & B23 & BK).
        eapply srz_msteps; [exact Hh | exact Hlz | exact RUN5 |]. clear RUN5.

        assert (MC : U1MemcpyBase.mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) n bs).
        { constructor.
          - lia.
          - lia.
          - subst M2. apply rdn_wbytes_self. unfold RS. rewrite u_small by lia. lia.
          - subst M2. eapply store_ok_mono; [apply wbytes_grows|]. eapply store_ok_mono; [exact GR1|].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - unfold RS. rewrite !u_small by lia. right. lia.
          - unfold RS. rewrite u_small by lia. lia.
          - rewrite u_small by lia. lia. }
        destruct (ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) n bs (seg_rom RSEGS) MC R5 (Z_to_bv 64 0x658bc)
                    ltac:(apply ret_ok_even; rewrite u_small by lia; reflexivity) B1 B10 B11 B12) as (R6 & RUN6 & K6).
        replace u1_memcpy_entry with (0xe2b9c : word) in RUN6 by (apply bv_eq; reflexivity).
        eapply srz_msteps; [exact Hh | exact Hlz | exact RUN6 |]. clear RUN6.
        set (M3 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        assert (GR3 : mem_grows M M3).
        { subst M3 M2 M1. eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [|apply wbytes_grows]. apply wbytes_grows. }
        assert (BKK : forall r, In r loop_kept -> getr R6 r = getr R r).
        { intros r Hr. rewrite (K6 r) by (cbv [loop_kept In] in Hr; cbv [callee_kept In];
            repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]); destruct Hr).
          rewrite (BK r Hr). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        assert (C9' : getr R6 9 = Z_to_bv 64 buf) by (rewrite (K6 9%bv) by (cbv; noncert_qtauto); exact B9).
        assert (C19' : getr R6 19 = Z_to_bv 64 len) by (rewrite (K6 19%bv) by (cbv; noncert_qtauto); exact B19).
        assert (C23' : getr R6 23 = Z_to_bv 64 n) by (rewrite (K6 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (C21' : getr R6 21 = Z_to_bv 64 cap) by (rewrite (BKK 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (C2' : getr R6 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (K6 2%bv) by (cbv; noncert_qtauto); exact B2).
        replace (Z_to_bv 64 0x658bc) with (0x658bc : word) by (apply bv_eq; reflexivity).
        destruct (Z.eq_dec (len + n) cap) as [Hfull|Hmore].
        *
          destruct (walkC_full R6 M3 (seg_rom RSEGS) buf len n cap C9' C19' C23' C21' ltac:(lia) ltac:(lia) Hfull Hcap ltac:(lia))
            as (R7 & RUN7 & E23 & E19 & EK).
          eapply srz_msteps; [exact Hh | exact Hlz | exact RUN7 |]. clear RUN7.
          replace (0x658d0 : word) with (Z_to_bv 64 0x658d0) by (apply bv_eq; reflexivity).
          rewrite Hfull.
          apply (HFULL ltac:(lia) R7 M3).
          -- split; [rewrite (EK 2%bv) by (cbv; noncert_qtauto); exact C2'|].
             split; [rewrite (EK 9%bv) by (cbv; noncert_qtauto); exact C9'|].
             split; [exact E19|].
             intros r Hr. rewrite (EK r) by (cbn [In]; right; right; right; exact Hr). apply BKK, Hr.
          -- exact E23.
          -- subst M3 M2 M1. rewrite <- Hfull. apply post_mem_here; try lia. exact RB.
        *
          destruct (walkC_head R6 M3 (seg_rom RSEGS) buf len n cap C9' C19' C23' C21' ltac:(lia) ltac:(lia) ltac:(lia) Hcap ltac:(lia))
            as (R7 & RUN7 & E9 & E19 & EK).
          eapply srz_msteps; [exact Hh | exact Hlz | exact RUN7 |]. clear RUN7.
          replace (0x65908 : word) with (Z_to_bv 64 0x65908) by (apply bv_eq; reflexivity).
          assert (EKK : forall r, In r loop_kept -> getr R7 r = getr R r).
          { intros r Hr. rewrite (EK r) by (cbn [In]; right; right; exact Hr). apply BKK, Hr. }
          apply (IH R7 M3 sp0 buf (len + n)%Z cap K ltac:(lia)).
          -- repeat split.
             ++ rewrite (EK 2%bv) by (cbv; noncert_qtauto). exact C2'.
             ++ exact E9.
             ++ exact E19.
             ++ rewrite (EKK 20%bv) by (cbv; noncert_qtauto). exact R20.
             ++ rewrite (EKK 21%bv) by (cbv; noncert_qtauto). exact R21.
             ++ rewrite (EKK 22%bv) by (cbv; noncert_qtauto). exact R22.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- eapply store_ok_mono; [exact GR3 | exact SOKs].
          -- eapply store_ok_mono; [exact GR3 | exact SOKrs].
          -- eapply store_ok_mono; [exact GR3 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros HcL R' M' PR P23 PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact EKK].
             ++ exact P23.
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | | exact RB | | | exact PM]; lia.
          -- intros HLc R' M' PR P23 PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact EKK].
             ++ exact P23.
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | | exact RB | | | exact PM]; lia.
  Qed.
End ChunkLoop.

Lemma content_at_buf : forall content M M' (sp0 buf held : Z),
  (0 <= held <= Z.of_nat (length content))%Z -> (0x124000 <= buf)%Z -> (buf + Z.of_nat (length content) <= sp0 - 136)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS M (Z_to_bv 64 buf) (Z.to_nat held) = Some (pref held content) ->
  post_mem content M M' sp0 buf held (Z.of_nat (length content)) ->
  rdn RSEGS M' (Z_to_bv 64 buf) (length content) = Some content.
Proof.
  intros content M M' sp0 buf held Hh Hb Hbl Hsp HELD [FR RD].
  replace (length content) with (Z.to_nat held + Z.to_nat (Z.of_nat (length content) - held))%nat by lia.
  rewrite <- (pref_dropz_app held content) at 2. rewrite <- (pref_all (Z.of_nat (length content) - held) (dropz held content))
    by (rewrite dropz_length by lia; lia).
  apply SeqExec.rdn_app.
  - rewrite (frame_mod_rdn RSEGS M M' _ (Z.to_nat held) (Z_to_bv 64 buf) FR); [exact HELD| |rewrite u_small by lia; lia].
    intros i Hi. rewrite (u_small buf) by lia. cbn [outside]. unfold in_rng, RS. rewrite !u_small by lia. repeat split; lia.
  - replace (Z_to_bv 64 buf + nat_to_word (Z.to_nat held)) with (Z_to_bv 64 (buf + held)); [exact RD|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

End FXALL1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
