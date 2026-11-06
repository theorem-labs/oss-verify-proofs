(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_freeopt ECH_C5_stmt ECH_C5_small ECH_C5_popfree ECH_C13_stmt ECH_C13_small ECH_C13_ext.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition EF_R1 : Z := 0x26c0e8.  Definition EF_R2 : Z := 0x26c0fc.  Definition EF_R4 : Z := 0x26c118.
Definition EF_R5 : Z := 0x26c12c.  Definition EF_R6 : Z := 0x26c140.  Definition EF_R7 : Z := 0x26c150.
Definition EF_T1 : Z := 0xdf170.
Definition ECHS_FILE : Z := 0x364d2.
Definition ef_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XE.
  Context {HCEIL : HeapCeil}.
  Lemma EXTobj_LB_mono : forall LB LB' m p X, EXTobj LB m p X -> (forall b, In b LB -> In b LB') -> EXTobj LB' m p X.
  Proof. intros LB LB' m p X (HC & HIN & OF) SUB. split; [exact HC|]. split; [apply SUB; exact HIN| eapply ofield_LB_mono; eauto]. Qed.

  Lemma EXTs_owned : forall LB m ps es b,
    Forall2 (fun p X => EXTobj LB m p X) ps es -> In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB.
  Proof.
    intros LB m ps es b F2. induction F2 as [|p X ps' es' E F IH]; cbn [concat map combine fst snd]; [intros []|].
    intros Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
    exact (EXTobj_owned_law LB m p X E b Hb).
  Qed.

  Lemma EXTs_frame : forall LB LB1 LB' SP m m' ps es,
    Forall2 (fun p X => EXTobj LB m p X) ps es ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB1) ->
    (forall b, In b LB1 -> In b LB') ->
    xpres LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => EXTobj LB' m' p X) ps es.
  Proof.
    intros LB LB1 LB' SP m m' ps es F2. induction F2 as [|p X ps' es' E F IH]; intros KEEP SUB XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply EXTobj_LB_mono; [| exact SUB]. eapply EXTobj_frame_law; [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact SUB| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.
End XE.

(* [comment removed for export] *)
Section LAWS.
  Context {HCEIL : HeapCeil}.

  Lemma ENTRYobj_owned_law : EP_owned entrep ENTRYobj blocks_ENTRY.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & O1 & O2 & O3 & O4 & XS) b Hb.
    unfold blocks_ENTRY in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    assert (OB : forall P o, ofield LB P o -> In b (blocks_of P o) -> In b LB).
    { intros P [[i n]|] OF K; cbn in OF, K; [| destruct K]. destruct K as [<-|[]]. destruct OF as (_ & _ & K). exact K. }
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O1 Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O2 Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O3 Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O4 Hb)|].
    revert XS Hb. unfold EXTS, blocks_EXTS. destruct (en_exts_o x) as [[K es]|]; intros XS Hb; [| destruct Hb].
    destruct XS as (_ & SO & _ & F2). apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    - eapply SKobj_owned; [exact SO| exact Hb].
    - eapply EXTs_owned; [exact F2| exact Hb].
  Qed.

  Lemma ENTRYobj_frame_law : ENTRYobj_frame.
  Proof.
    unfold ENTRYobj_frame, EP_frame. intros LB LB' m m' p x SP EO KEEP XP BEL.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & HIN & O1 & O2 & O3 & O4 & XS).
    assert (OWN := ENTRYobj_owned_law LB m p x EO).
    assert (OFR : forall P o, ofield LB P o -> (forall b, In b (blocks_of P o) -> In b LB') -> ofield LB' P o).
    { intros P [[i n]|] OF K; cbn in OF |- *; [| exact OF]. destruct OF as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|]. apply K. left. reflexivity. }
    unfold ENTRYobj. split.
    { exists pad1, pad2, pad3, pad4. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
      eapply xpres_rw_cells'; [exact XP| exact HC| | constructor].
      right; right. exists (en_id x, p, ENTRY_SIZE). split; [apply KEEP; left; reflexivity|]. unfold entry_cells.
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    split; [apply KEEP; left; reflexivity|].
    unfold blocks_ENTRY in KEEP.
    split; [apply (OFR _ _ O1); intros b Hb; apply KEEP; right; apply in_or_app; left; exact Hb|].
    split; [apply (OFR _ _ O2); intros b Hb; apply KEEP; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
    split; [apply (OFR _ _ O3); intros b Hb; apply KEEP; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb|].
    split; [apply (OFR _ _ O4); intros b Hb; apply KEEP; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb|].
    assert (KX : forall b, In b (blocks_EXTS (en_exts x) (en_exts_o x)) -> In b LB') by (intros b Hb; apply KEEP; right; do 4 (apply in_or_app; right); exact Hb).
    clear KEEP. revert XS KX. unfold EXTS, blocks_EXTS. destruct (en_exts_o x) as [[K es]|] eqn:EQX; intros XS KX; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply SKobj_frame; [exact SO| intros b Hb; apply KX; apply in_or_app; left; exact Hb| exact XP].
    - split; [exact LEN|]. eapply (EXTs_frame LB LB' LB' SP m m'); [exact F2| intros b Hb; apply KX; apply in_or_app; right; exact Hb| auto| exact XP|].
      intros b Hb. apply BEL. unfold blocks_ENTRY. right. do 4 (apply in_or_app; right). unfold blocks_EXTS. rewrite EQX. apply in_or_app. right. exact Hb.
  Qed.
End LAWS.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Section E.
    (* [comment removed for export] *)
    Variables (E : entrep) (pad1 pad2 pad3 pad4 : list byte).
    Let EC := entry_cells E pad1 pad2 pad3 pad4.
    Hypothesis L1 : length pad1 = 6%nat. Hypothesis L2 : length pad2 = 4%nat. Hypothesis L3 : length pad3 = 6%nat. Hypothesis L4 : length pad4 = 4%nat.
    Hypothesis RPN : 0 <= en_pname E < 2^64. Hypothesis RPB : 0 <= en_pub E < 2^64. Hypothesis RSU : 0 <= en_suites E < 2^64.
    Hypothesis REN : 0 <= en_encoded E < 2^64. Hypothesis RXS : 0 <= en_exts E < 2^64.

    Local Ltac prep HDR := unfold EC, entry_cells, wz, b8 in HDR.

    (* [comment removed for export] *)
    Lemma e_seg1 :
      forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
        rw_cells rsegs m a EC -> 0 < a -> a + ENTRY_SIZE <= lo ->
        stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
        evt rsegs (fun ms' => exists m1,
            ms' = MS (mkR (Z_to_bv 64 EF_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                         (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 ECHS_FILE) (Z_to_bv 64 87) a3 a4 a5 a6 a7
                         (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
            /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
            /\ stk rsegs m1 lo (bv_unsigned sp + -32)
            /\ rw_cells rsegs m1 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)
            /\ rw_cells rsegs m1 a EC)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom rsegs)).
    Proof.
      intros until lo. intros HDR POS BL ST CEIL LO MI. unfold P_ossl_echstore_entry_free, P_CRYPTO_free, EF_R1, ECHS_FILE.
      prep HDR. unfold ENTRY_SIZE in *.
      pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add length] in HB.
      hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
      carve_frame 32%nat ST.
      do 7 step. st1. do 6 step. finish.
      all: unfold EC, entry_cells, wz, b8; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma e_segF :
      forall (RA RA' line fld : Z) (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
        (RA = EF_R1 /\ RA' = EF_R2 /\ fld = en_pub E /\ line = 88) \/ (RA = EF_R4 /\ RA' = EF_R5 /\ fld = en_suites E /\ line = 91) ->
        rw_cells rsegs m a EC -> 0 < a -> a + ENTRY_SIZE < 2^64 -> mem_inv rsegs m ->
        evt rsegs (fun ms' =>
            ms' = MS (mkR (Z_to_bv 64 RA') (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                         (Z_to_bv 64 fld) (Z_to_bv 64 ECHS_FILE) (Z_to_bv 64 line) a3 a4 a5 a6 a7
                         (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs))
          (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc (Z_to_bv 64 RA)) fc None m (seg_rom rsegs)).
    Proof.
      intros until a. intros CASES HDR POS AB MI. unfold P_CRYPTO_free, ECHS_FILE.
      prep HDR. unfold ENTRY_SIZE in *. pose proof (word_range sp) as SPR.
      destruct CASES as [(-> & -> & -> & ->)|(-> & -> & -> & ->)]; unfold EF_R1, EF_R2, EF_R4, EF_R5.
      - replace (ret_pc (Z_to_bv 64 0x26c0e8)) with (Z_to_bv 64 0x26c0e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        st1. do 4 step. apply evt_done. reflexivity.
      - replace (ret_pc (Z_to_bv 64 0x26c118)) with (Z_to_bv 64 0x26c118) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        st1. do 4 step. apply evt_done. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma e_seg3 :
      forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
        rw_cells rsegs m a EC -> 0 < a -> a + ENTRY_SIZE <= lo ->
        stk rsegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
        evt rsegs (fun ms' => exists u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
            ms' = MS (mkR (Z_to_bv 64 EF_R4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 s0x (Z_to_bv 64 a)
                         (Z_to_bv 64 (en_encoded E)) (Z_to_bv 64 ECHS_FILE) (Z_to_bv 64 90) b3 b4 b5 b6 b7
                         (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                     F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
            /\ munch [(lo, bv_unsigned sp + -32)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
            /\ stk rsegs m1 lo (bv_unsigned sp + -32) /\ rw_cells rsegs m1 a EC)
          (MS (mkR (Z_to_bv 64 EF_R2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc (Z_to_bv 64 EF_R2)) fc None m (seg_rom rsegs)).
    Proof.
      intros until lo. intros HDR POS BL ST CEIL LO MI. unfold EF_R2, EF_R4, P_CRYPTO_free, ECHS_FILE.
      replace (ret_pc (Z_to_bv 64 0x26c0fc)) with (Z_to_bv 64 0x26c0fc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      prep HDR. unfold ENTRY_SIZE in *.
      hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      pose proof (munch_refl [(lo, bv_unsigned sp + -32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      st1. step.
      eapply evt_cut.
      { pose proof pkeyfree_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
          try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold FR_EVP_PKEY_free; lia); try lia. }
      land MU WM.
      st1. do 4 step. finish.
      all: unfold EC, entry_cells, wz, b8; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma e_seg5 :
      forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
        rw_cells rsegs m a EC -> 0 < a -> a + ENTRY_SIZE < 2^64 -> mem_inv rsegs m ->
        evt rsegs (fun ms' => exists ra',
            ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                         (Z_to_bv 64 (en_exts E)) (Z_to_bv 64 P_sk_OSSL_ECHEXT_freefunc_thunk) a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs) /\ ra' = Z_to_bv 64 EF_R6)
          (MS (mkR (Z_to_bv 64 EF_R5) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc (Z_to_bv 64 EF_R5)) fc None m (seg_rom rsegs)).
    Proof.
      intros until a. intros HDR POS AB MI. unfold EF_R5, EF_R6, P_OPENSSL_sk_set_thunks, P_sk_OSSL_ECHEXT_freefunc_thunk, ECHS_FILE.
      replace (ret_pc (Z_to_bv 64 0x26c12c)) with (Z_to_bv 64 0x26c12c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      prep HDR. unfold ENTRY_SIZE in *. pose proof (word_range sp) as SPR.
      st1. do 4 step. apply evt_done. eexists. split; reflexivity.
    Qed.
  End E.

  (* [comment removed for export] *)
  Lemma e_seg6n :
    forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      GOT_echfree m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 ra',
          ms' = MS (mkR ra' sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 EF_R7) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp) /\ GOT_echfree m1)
        (MS (mkR (Z_to_bv 64 EF_R6) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 P_sk_OSSL_ECHEXT_freefunc_thunk) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros GG ST CEIL LO MI.
    unfold P_sk_OSSL_ECHEXT_freefunc_thunk, EF_R6, EF_R7. unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz in GG.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { pose proof skset_thunks_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    do 4 step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    finish.
    all: unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma e_seg6s :
    forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (h lo : Z) (K : skrep),
      SKobj LB m h K -> SK_below h K lo -> GOT_echfree m -> (h + SK_SIZE <= 0x10000 \/ 0x311000 <= h) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 ra',
          ms' = MS (mkR ra' sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 h) (Z_to_bv 64 P_ossl_echext_free) b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (h, h + SK_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ SKobj LB m1 h (sk_with_thunk K O_SK_FREETH P_sk_OSSL_ECHEXT_freefunc_thunk) /\ GOT_echfree m1 /\ ra' = Z_to_bv 64 EF_R7)
        (MS (mkR (Z_to_bv 64 EF_R6) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) (Z_to_bv 64 P_sk_OSSL_ECHEXT_freefunc_thunk) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros SO BEL GG HOFF ST CEIL LO MI.
    unfold EF_R6, EF_R7, P_OPENSSL_sk_pop_free. unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz in GG |- *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (h, h + SK_SIZE)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold SK_SIZE in MU, HOFF.
    eapply evt_cut.
    { pose proof skset_thunks_spec as Q; hnf in Q; eapply Q with (lo := lo) (LB := LB) (K := K); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold P_sk_OSSL_ECHEXT_freefunc_thunk; lia); try lia. }
    intros ms_ PO_; unfold skset_post, SK_SIZE in PO_; revert ms_ PO_.
    land MU WM.
    do 4 step.
    finish.
    all: try reflexivity; unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma e_seg7 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 rax : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells rsegs m (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u1,
          ms' = MS (mkR ra sp gp tp t0 u1 t2 s0 s1
                       (Z_to_bv 64 a) (Z_to_bv 64 ECHS_FILE) (Z_to_bv 64 93) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EF_R7) fc None m (seg_rom rsegs)).
  Proof.
    intros until a. intros FR MI. unfold EF_R7, ECHS_FILE, P_CRYPTO_free. unfold ef_frame in FR.
    pose proof (word_range sp) as SPR.
    do 3 step. do 4 st1. step. step. step. apply evt_done. eexists. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ndx_l : forall (l1 l2 : list block) b, List.NoDup (map blk_id (l1 ++ l2)) -> In b l2 -> ~ In b l1.
Proof. intros l1 l2 b ND H2 H1. exact (nodup_ids_app_ne l1 l2 b b ND H1 H2 eq_refl). Qed.
Lemma ndx_r : forall (l1 l2 : list block) b, List.NoDup (map blk_id (l1 ++ l2)) -> In b l1 -> ~ In b l2.
Proof. intros l1 l2 b ND H1 H2. exact (nodup_ids_app_ne l1 l2 b b ND H1 H2 eq_refl). Qed.
Lemma nd_tail : forall (l1 l2 : list block), List.NoDup (map blk_id (l1 ++ l2)) -> List.NoDup (map blk_id l2).
Proof. intros l1 l2 ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND. exact ND. Qed.

Section KEEP.
  Context {HCEIL : HeapCeil}.
  Lemma ofield_keep : forall LB LB' P o, ofield LB P o -> (forall b, In b (blocks_of P o) -> In b LB') -> ofield LB' P o.
  Proof.
    intros LB LB' P [[i n]|] OF K; cbn in OF |- *; [| exact OF]. destruct OF as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. apply K. left. reflexivity.
  Qed.
  Lemma ofield_in : forall LB P i n, ofield LB P (Some (i, n)) -> In (i, P, n) LB.
  Proof. intros LB P i n (A1 & A2 & A3). exact A3. Qed.
  Lemma ofield_owned : forall LB P o b, ofield LB P o -> In b (blocks_of P o) -> In b LB.
  Proof. intros LB P [[i n]|] b OF Hb; cbn in OF, Hb; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj2 (proj2 OF)). Qed.
  Lemma EXTS_keep : forall LB LB' SP m m' P xs,
    EXTS LB m P xs -> (forall b, In b (blocks_EXTS P xs) -> In b LB') -> xpres LB' SP [] m m' ->
    (forall b, In b (blocks_EXTS P xs) -> blk_addr b + blk_size b <= SP) -> EXTS LB' m' P xs.
  Proof.
    intros LB LB' SP m m' P xs XS KEEP XP BEL. revert XS KEEP BEL. unfold EXTS, blocks_EXTS.
    destruct xs as [[K es]|]; intros XS KEEP BEL; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply SKobj_frame; [exact SO| intros b Hb; apply KEEP; apply in_or_app; left; exact Hb| exact XP].
    - split; [exact LEN|]. eapply (EXTs_frame LB LB' LB' SP m m'); [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| auto| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
  Lemma EXTS_owned : forall LB m P xs b, EXTS LB m P xs -> In b (blocks_EXTS P xs) -> In b LB.
  Proof.
    intros LB m P xs b. unfold EXTS, blocks_EXTS. destruct xs as [[K es]|]; intros XS Hb; [| destruct Hb].
    destruct XS as (_ & SO & _ & F2). apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [eapply SKobj_owned; eauto| eapply EXTs_owned; eauto].
  Qed.
End KEEP.

Lemma perm_chain5 {A} : forall (hd : A) (B1 B2 B3 B4 B5 L L2 L3 L4 L5 L6 L7 : list A),
  Permutation (B1 ++ L2) L -> Permutation (B2 ++ L3) L2 -> Permutation (B4 ++ L4) L3 -> Permutation (B3 ++ L5) L4 ->
  Permutation (B5 ++ L6) L5 -> Permutation (hd :: L7) L6 ->
  Permutation ((hd :: B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ L7) L.
Proof.
  intros hd B1 B2 B3 B4 B5 L L2 L3 L4 L5 L6 L7 P1 P2 P3 P4 P5 P6.
  assert (Q : Permutation L (B1 ++ B2 ++ B4 ++ B3 ++ B5 ++ hd :: L7)).
  { eapply Permutation_trans; [apply Permutation_sym; exact P1|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P2|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P3|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P4|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P5|]. apply Permutation_app_head.
    apply Permutation_sym. exact P6. }
  apply Permutation_sym. eapply Permutation_trans; [exact Q|].
  change ((hd :: B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ L7) with (hd :: (B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ L7).
  assert (R : Permutation (B1 ++ B2 ++ B4 ++ B3 ++ B5 ++ hd :: L7) ((B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ hd :: L7)).
  { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    rewrite (app_assoc B4 B3), (app_assoc B3 B4). apply Permutation_app_tail. apply Permutation_app_comm. }
  eapply Permutation_trans; [exact R|]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma ofield_match : forall {HCEIL : HeapCeil} LB P o,
  ofield LB P o -> match o with None => P = 0 | Some (id, n) => In (id, P, n) LB end.
Proof. intros HC LB P [[i n]|] OF; cbn in OF |- *; [exact (proj2 (proj2 OF))| exact OF]. Qed.

Lemma e_blocks_SK_with_thunk {HCEIL : HeapCeil} : forall a K w f, blocks_SK a (sk_with_thunk K w f) = blocks_SK a K.
Proof. intros. reflexivity. Qed.
Lemma e_sk_elems_with_thunk {HCEIL : HeapCeil} : forall K w f, sk_elems (sk_with_thunk K w f) = sk_elems K.
Proof. intros. reflexivity. Qed.
Lemma e_sk_free_thunk_set {HCEIL : HeapCeil} : forall K f, sk_free_thunk (sk_with_thunk K O_SK_FREETH f) = f.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma entryfree_spec : entryfree_stmt H.
  Proof.
    unfold entryfree_stmt, efree_stmt_at. intros until errv.
    intros A0 EO ND HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM GG RAE. subst a0.
    unfold ENTRYFREE_STACK, FR_ossl_echstore_entry_free, SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free,
      CFREE_STACK, RFREE_STACK, FR_EVP_PKEY_free in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall q L b, In b (hs_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC) & EIN & O1 & O2 & O3 & O4 & XS).
    pose proof (HB _ EIN) as PBL. cbn [blk_addr blk_size fst snd] in PBL. unfold ENTRY_SIZE in PBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP EIN) as PBR. cbn [blk_addr blk_size fst snd] in PBR. unfold ENTRY_SIZE in PBR.
    destruct PBR as (POS & _ & _ & _ & POFF). box POFF.
    assert (OWN := ENTRYobj_owned_law LB m p x EO).
    assert (BELx : forall b, In b (blocks_ENTRY p x) -> blk_addr b + blk_size b <= hceil) by (intros b Hb; apply HB; apply OWN; exact Hb).
    (* [comment removed for export] *)
    assert (FRNG : forall P o, ofield LB P o -> 0 <= P < 2^64).
    { intros P [[i n]|] OF; cbn in OF; [| lia]. destruct OF as (F1 & F2 & F3). pose proof (HB _ F3) as K. cbn [blk_addr blk_size fst snd] in K. lia. }
    pose proof (FRNG _ _ O1) as RPN. pose proof (FRNG _ _ O2) as RPB. pose proof (FRNG _ _ O3) as RSU. pose proof (FRNG _ _ O4) as REN.
    assert (RXS : 0 <= en_exts x < 2^64).
    { revert XS. unfold EXTS. destruct (en_exts_o x) as [[K es]|]; intros XS; [| lia].
      destruct XS as (X1 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (HB _ KIN) as KB. cbn [blk_addr blk_size fst snd] in KB. unfold SK_SIZE in KB. lia. }
    subst tp. rewrite errno_RATP in ERR.
    unfold blocks_ENTRY in ND.
    set (Bpn := blocks_of (en_pname x) (en_pname_o x)) in *. set (Bpub := blocks_of (en_pub x) (en_pub_o x)) in *.
    set (Bsu := blocks_of (en_suites x) (en_suites_o x)) in *. set (Benc := blocks_of (en_encoded x) (en_encoded_o x)) in *.
    set (BX := blocks_EXTS (en_exts x) (en_exts_o x)) in *.
    pose proof ND as ND0. cbn [map] in ND0. inversion ND0 as [|i0 l0 NI NDt]; subst i0 l0. clear ND0.
    assert (NOTHD : forall Fr, (forall b, In b Fr -> In b (Bpn ++ Bpub ++ Bsu ++ Benc ++ BX)) -> ~ In (en_id x, p, ENTRY_SIZE) Fr).
    { intros Fr SUB K. apply NI. rewrite in_map_iff. exists (en_id x, p, ENTRY_SIZE). split; [reflexivity| apply SUB; exact K]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply (e_seg1 x pad1 pad2 pad3 pad4) with (lo := lo); try eassumption; unfold ENTRY_SIZE; try lia|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & EC1).
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (GG1 : GOT_echfree m1) by (eapply GOT_echfree_across; [exact MU1| exact WM1| unfold A_got_ossl_echext_free; cbn; lia| exact GG]).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (XS1 : EXTS LB m1 (en_exts x) (en_exts_o x)).
    { eapply EXTS_keep; [exact XS| intros b Hb; eapply EXTS_owned; [exact XS| exact Hb]| exact XP1|].
      intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (cfree_opt_spec H HH) as CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (P := (en_pname x)) (o := (en_pname_o x)); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP1| exact KREL| exact AUX1| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1| exact (ofield_match _ _ _ O1)].
      all: try first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR1]. }
    clear CF. intros [ms2 mo2] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r02 & r12 & r22 & q02 & q12 & q22 & q32 & q42 & q52 & q62 & q72 & r32 & r42 & r52 & r62 & m2 & st2 & LB2 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & PERM2 & SUB2 & XP2 & HEAP2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    assert (KEEP2 : forall b, In b LB -> ~ In b (blocks_of (en_pname x) (en_pname_o x)) -> In b LB2) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM2| exact Hb| exact Nb]).
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP2).

    assert (EIN2 : In (en_id x, p, ENTRY_SIZE) LB2).
    { apply KEEP2; [exact EIN|]. apply NOTHD. intros b Hb. apply in_or_app. left. exact Hb. }
    assert (NX2 : forall b, In b (Bpub ++ Bsu ++ Benc ++ BX) -> ~ In b Bpn) by (intros b Hb; exact (ndx_l _ _ _ NDt Hb)).
    assert (O2b : ofield LB2 (en_pub x) (en_pub_o x)).
    { eapply ofield_keep; [exact O2|]. intros b Hb. apply KEEP2; [eapply ofield_owned; [exact O2| exact Hb]|]. apply NX2. apply in_or_app. left. exact Hb. }
    assert (O3b : ofield LB2 (en_suites x) (en_suites_o x)).
    { eapply ofield_keep; [exact O3|]. intros b Hb. apply KEEP2; [eapply ofield_owned; [exact O3| exact Hb]|]. apply NX2. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (O4b : ofield LB2 (en_encoded x) (en_encoded_o x)).
    { eapply ofield_keep; [exact O4|]. intros b Hb. apply KEEP2; [eapply ofield_owned; [exact O4| exact Hb]|]. apply NX2. do 2 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
    assert (XS2 : EXTS LB2 m2 (en_exts x) (en_exts_o x)).
    { eapply EXTS_keep; [exact XS1| | exact XP2|].
      - intros b Hb. apply KEEP2; [eapply EXTS_owned; [exact XS| exact Hb]|]. apply NX2. do 3 (apply in_or_app; right). exact Hb.
      - intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)) by (eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia| constructor]).
    assert (EC2 : rw_cells rsegs m2 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply xpres_rw_cells'; [exact XP2| exact EC1| | constructor]. right; right. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN2|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG2 : GOT_echfree m2) by (eapply GOT_echfree_xpres; [exact XP2| constructor| exact GG1]).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply (e_segF x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS) with (RA := EF_R1); [left; repeat split; reflexivity| exact EC2| exact POS| unfold ENTRY_SIZE; lia| exact MI2]|].
    intros ms2b ->.
    (* [comment removed for export] *)
    pose proof (cfree_opt_spec H HH) as CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB2) (s := st2) (P := (en_pub x)) (o := (en_pub_o x)); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP2| exact KREL2| exact AUX2| exact ST2| exact CEIL| exact MI2| exact IM2| exact GM2| exact (ofield_match _ _ _ O2b)].
      all: try first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR2]. }
    clear CF. intros [ms3 mo3] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r03 & r13 & r23 & q03 & q13 & q23 & q33 & q43 & q53 & q63 & q73 & r33 & r43 & r53 & r63 & m3 & st3 & LB3 &
                    -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & PERM3 & SUB3 & XP3 & HEAP3 & IM3 & GM3).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST3, XP3 by lia. rewrite errno_RATP in ERR3.
    assert (KEEP3 : forall b, In b LB2 -> ~ In b (blocks_of (en_pub x) (en_pub_o x)) -> In b LB3) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM3| exact Hb| exact Nb]).
    assert (HB3 := HH_blocks_below H HH _ _ _ HEAP3).

    pose proof (nd_tail _ _ NDt) as NDt2.
    assert (EIN3 : In (en_id x, p, ENTRY_SIZE) LB3).
    { apply KEEP3; [exact EIN2|]. apply NOTHD. intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (NX3 : forall b, In b (Bsu ++ Benc ++ BX) -> ~ In b Bpub) by (intros b Hb; exact (ndx_l _ _ _ NDt2 Hb)).
    assert (O3c : ofield LB3 (en_suites x) (en_suites_o x)).
    { eapply ofield_keep; [exact O3b|]. intros b Hb. apply KEEP3; [eapply ofield_owned; [exact O3b| exact Hb]|]. apply NX3. apply in_or_app. left. exact Hb. }
    assert (O4c : ofield LB3 (en_encoded x) (en_encoded_o x)).
    { eapply ofield_keep; [exact O4b|]. intros b Hb. apply KEEP3; [eapply ofield_owned; [exact O4b| exact Hb]|]. apply NX3. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (XS3 : EXTS LB3 m3 (en_exts x) (en_exts_o x)).
    { eapply EXTS_keep; [exact XS2| | exact XP3|].
      - intros b Hb. apply KEEP3; [eapply EXTS_owned; [exact XS2| exact Hb]|]. apply NX3. do 2 (apply in_or_app; right). exact Hb.
      - intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)) by (eapply xpres_rw_cells'; [exact XP3| exact FR2| left; cbn; lia| constructor]).
    assert (EC3 : rw_cells rsegs m3 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply xpres_rw_cells'; [exact XP3| exact EC2| | constructor]. right; right. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN3|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG3 : GOT_echfree m3) by (eapply GOT_echfree_xpres; [exact XP3| constructor| exact GG2]).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| eapply (e_seg3 x pad1 pad2 pad3 pad4) with (lo := lo); try eassumption; unfold ENTRY_SIZE; try lia|].
    intros ms3b (w0 & w1 & w2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3b & -> & MU3b & WM3b & MI3b & ST3b & EC3b).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU3b by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3b by lia.
    assert (HP3b : hs_RHEAP H st3 LB3 m3b).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP3| exact MU3b| exact WM3b|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX3b : hs_rauxv_ok H m3b B).
    { eapply (HH_rauxv_frame H HH); [exact AUX3| exact MU3b| exact WM3b|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m3 m3b _ _ ERR3) in MU3b as ERR3b; [| exact WM3b| unfold RERRNO; cbn; lia].
    apply (rw_cells_transport rsegs _ m3 m3b _ _ FR3) in MU3b as FR3b; [| exact WM3b| cbn; lia].
    assert (IM3b : IMPL_mem m3b) by (eapply IMPL_across; [exact MU3b| exact WM3b| unfold A_malloc_impl; cbn; lia| exact IM3]).
    assert (GM3b : GOT_mem m3b) by (eapply GOT_across; [exact MU3b| exact WM3b| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM3]).
    assert (GG3b : GOT_echfree m3b) by (eapply GOT_echfree_across; [exact MU3b| exact WM3b| unfold A_got_ossl_echext_free; cbn; lia| exact GG3]).
    assert (XP3b : xpres LB3 (bv_unsigned sp) [] m3 m3b).
    { eapply xpres_of_munch; [exact MU3b| exact WM3b| | exact HB3]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (XS3b : EXTS LB3 m3b (en_exts x) (en_exts_o x)).
    { eapply EXTS_keep; [exact XS3| intros b Hb; eapply EXTS_owned; [exact XS3| exact Hb]| exact XP3b|].
      intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    (* [comment removed for export] *)
    pose proof (cfree_opt_spec H HH) as CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB3) (s := st3) (P := (en_encoded x)) (o := (en_encoded_o x)); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP3b| exact KREL3| exact AUX3b| exact ST3b| exact CEIL| exact MI3b| exact IM3b| exact GM3b| exact (ofield_match _ _ _ O4c)].
      all: try first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR3b]. }
    clear CF. intros [ms4 mo4] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r04 & r14 & r24 & q04 & q14 & q24 & q34 & q44 & q54 & q64 & q74 & r34 & r44 & r54 & r64 & m4 & st4 & LB4 &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & PERM4 & SUB4 & XP4 & HEAP4 & IM4 & GM4).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4.
    assert (KEEP4 : forall b, In b LB3 -> ~ In b (blocks_of (en_encoded x) (en_encoded_o x)) -> In b LB4) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM4| exact Hb| exact Nb]).
    assert (HB4 := HH_blocks_below H HH _ _ _ HEAP4).

    pose proof (nd_tail _ _ NDt2) as NDt3. pose proof (nd_tail _ _ NDt3) as NDt4.
    assert (EIN4 : In (en_id x, p, ENTRY_SIZE) LB4).
    { apply KEEP4; [exact EIN3|]. apply NOTHD. intros b Hb. do 3 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
    assert (O3d : ofield LB4 (en_suites x) (en_suites_o x)).
    { eapply ofield_keep; [exact O3c|]. intros b Hb. apply KEEP4; [eapply ofield_owned; [exact O3c| exact Hb]|].
      intros Kb. exact (ndx_r _ _ _ NDt3 Hb (in_or_app _ _ _ (or_introl Kb))). }
    assert (XS4 : EXTS LB4 m4 (en_exts x) (en_exts_o x)).
    { eapply EXTS_keep; [exact XS3b| | exact XP4|].
      - intros b Hb. apply KEEP4; [eapply EXTS_owned; [exact XS3b| exact Hb]|]. exact (ndx_l _ _ _ NDt4 Hb).
      - intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)) by (eapply xpres_rw_cells'; [exact XP4| exact FR3b| left; cbn; lia| constructor]).
    assert (EC4 : rw_cells rsegs m4 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply xpres_rw_cells'; [exact XP4| exact EC3b| | constructor]. right; right. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN4|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG4 : GOT_echfree m4) by (eapply GOT_echfree_xpres; [exact XP4| constructor| exact GG3b]).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply (e_segF x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS) with (RA := EF_R4); [right; repeat split; reflexivity| exact EC4| exact POS| unfold ENTRY_SIZE; lia| exact MI4]|].
    intros ms4b ->.
    (* [comment removed for export] *)
    pose proof (cfree_opt_spec H HH) as CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB4) (s := st4) (P := (en_suites x)) (o := (en_suites_o x)); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP4| exact KREL4| exact AUX4| exact ST4| exact CEIL| exact MI4| exact IM4| exact GM4| exact (ofield_match _ _ _ O3d)].
      all: try first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR4]. }
    clear CF. intros [ms5 mo5] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r05 & r15 & r25 & q05 & q15 & q25 & q35 & q45 & q55 & q65 & q75 & r35 & r45 & r55 & r65 & m5 & st5 & LB5 &
                    -> & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5 & PERM5 & SUB5 & XP5 & HEAP5 & IM5 & GM5).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia. rewrite errno_RATP in ERR5.
    assert (KEEP5 : forall b, In b LB4 -> ~ In b (blocks_of (en_suites x) (en_suites_o x)) -> In b LB5) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM5| exact Hb| exact Nb]).
    assert (HB5 := HH_blocks_below H HH _ _ _ HEAP5).

    assert (EIN5 : In (en_id x, p, ENTRY_SIZE) LB5).
    { apply KEEP5; [exact EIN4|]. apply NOTHD. intros b Hb. do 2 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
    assert (XS5 : EXTS LB5 m5 (en_exts x) (en_exts_o x)).
    { eapply EXTS_keep; [exact XS4| | exact XP5|].
      - intros b Hb. apply KEEP5; [eapply EXTS_owned; [exact XS4| exact Hb]|]. exact (ndx_l _ _ _ NDt3 (in_or_app _ _ _ (or_intror Hb))).
      - intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)) by (eapply xpres_rw_cells'; [exact XP5| exact FR4| left; cbn; lia| constructor]).
    assert (EC5 : rw_cells rsegs m5 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply xpres_rw_cells'; [exact XP5| exact EC4| | constructor]. right; right. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN5|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG5 : GOT_echfree m5) by (eapply GOT_echfree_xpres; [exact XP5| constructor| exact GG4]).
    (* [comment removed for export] *)
    assert (XP05 : xpres LB5 (bv_unsigned sp) [] m m5).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP1| lia| intros b Hb; apply SUB2, SUB3, SUB4, SUB5; exact Hb| auto]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| intros b Hb; apply SUB3, SUB4, SUB5; exact Hb| auto]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP3| lia| intros b Hb; apply SUB4, SUB5; exact Hb| auto]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP3b| lia| intros b Hb; apply SUB4, SUB5; exact Hb| auto]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP4| lia| intros b Hb; apply SUB5; exact Hb| auto]|].
      eapply xpres_weaken; [exact XP5| lia| auto| auto]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL5| eapply (e_seg5 x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS); [exact EC5| exact POS| unfold ENTRY_SIZE; lia| exact MI5]|].
    intros ms5b (rax & -> & ->).
    (* [comment removed for export] *)
    assert (MID : hs_SR H (fun c => exists (rax2 w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 : word) m6 st6 LB6,
                 cfg_ms c = MS (mkR rax2 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) w0 w1 w2 sp (Z_to_bv 64 p)
                                    c0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                               F (Z_to_bv 64 EF_R7) fc None m6 (seg_rom rsegs)
                 /\ hs_KREL H st6 (cfg_model c) /\ hs_MPRES H mo5 (cfg_model c) /\ mem_inv rsegs m6 /\ stk rsegs m6 lo (bv_unsigned sp + -32)
                 /\ rw_cells rsegs m6 RERRNO [C4 errv] /\ hs_rauxv_ok H m6 B
                 /\ hs_RHEAP H st6 LB6 m6 /\ In (en_id x, p, ENTRY_SIZE) LB6
                 /\ Permutation (BX ++ LB6) LB5 /\ (forall b, In b LB6 -> In b LB5)
                 /\ xpres LB6 (bv_unsigned sp) [] m m6 /\ IMPL_mem m6 /\ GOT_mem m6 /\ GOT_echfree m6
                 /\ rw_cells rsegs m6 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra))
             (mkCfg (MS (mkR (Z_to_bv 64 EF_R6) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) r05 r15 r25 sp (Z_to_bv 64 p)
                       (Z_to_bv 64 (en_exts x)) (Z_to_bv 64 P_sk_OSSL_ECHEXT_freefunc_thunk) q25 q35 q45 q55 q65 q75
                       (Z_to_bv 64 ECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 r35 r45 r55 r65)
                    F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m5 (seg_rom rsegs)) mo5)).
    { pose proof XS5 as XS5'. unfold EXTS in XS5'.
      assert (NDX : List.NoDup (map blk_id BX)) by (exact (nd_tail _ _ (nd_tail _ _ (nd_tail _ _ (nd_tail _ _ NDt))))).
      destruct (en_exts_o x) as [[K es]|] eqn:EXO; rewrite ?EXO in XS5'.
      - (* [comment removed for export] *)
        destruct XS5' as (HPOS & SO & LEN & F2).
        set (h := en_exts x) in *.
        set (EB := concat (map (fun px : Z * extrep => blocks_EXT (fst px) (snd px)) (combine (sk_elems K) es))) in *.
        assert (BXE : BX = blocks_SK h K ++ EB) by (unfold BX, blocks_EXTS; rewrite ?EXO; reflexivity).
        rewrite BXE in NDX.
        pose proof SO as SO0. destruct SO0 as (_ & _ & KIN & KNC & KCAP & _ & _ & KDAT).
        pose proof (HB5 _ KIN) as KBL. cbn [blk_addr blk_size fst snd] in KBL. unfold SK_SIZE in KBL.
        pose proof (HH_RHEAP_block_range H HH _ _ _ _ HEAP5 KIN) as KBR. cbn [blk_addr blk_size fst snd] in KBR. unfold SK_SIZE in KBR.
        destruct KBR as (_ & _ & _ & _ & KOFF).
        assert (PK : blk_id (en_id x, p, ENTRY_SIZE) <> blk_id (sk_id K, h, SK_SIZE)).
        { intros E. apply NI. rewrite in_map_iff. exists (sk_id K, h, SK_SIZE). split; [symmetry; exact E|].
          do 4 (apply in_or_app; right). rewrite BXE. apply in_or_app. left. left. reflexivity. }
        cbn [blk_id fst snd] in PK.
        pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HEAP5 EIN5 KIN PK) as DPK. cbn [blk_addr blk_size fst snd] in DPK. unfold ENTRY_SIZE, SK_SIZE in DPK.
        assert (BEL : SK_below h K lo).
        { split; [unfold SK_SIZE; lia|]. destruct KDAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [left; exact C0| right].
          pose proof (HB5 _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL. lia. }
        eapply (sr_evt_krel H HH); [exact KREL5| eapply e_seg6s with (lo := lo) (LB := LB5) (K := K); rewrite ?unsigned_lit by lia;
                                     [exact SO| exact BEL| exact GG5| unfold SK_SIZE; exact KOFF| exact ST5| exact CEIL| lia| exact MI5]|].
        intros ms6a (y0 & y1 & y2 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & rax6 & -> & MU6a & WM6a & MI6a & ST6a & SO6a & GG6a & ->).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU6a, ST6a by lia. unfold SK_SIZE in MU6a.
        box KOFF. box DPK.
        assert (XPh : xpres (hs_lb_remove H (sk_id K) LB5) (bv_unsigned sp + -32) [] m5 m6a).
        { eapply (xpres_of_munch_block H HH) with (hb := (sk_id K, h, SK_SIZE)); [exact HEAP5| exact KIN| lia| exact MU6a| exact WM6a|].
          cbn [blk_addr blk_size blk_id fst snd]. unfold SK_SIZE.
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
        assert (HP6a : hs_RHEAP H st5 LB5 m6a).
        { eapply (HH_RHEAP_frame H HH); [exact HEAP5| exact MU6a| exact WM6a|].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (sk_id K, h, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; lia]. }
        assert (AUX6a : hs_rauxv_ok H m6a B).
        { eapply (HH_rauxv_frame H HH); [exact AUX5| exact MU6a| exact WM6a|]. unfold RAUXV_CELL.
          apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 KOFF| apply Forall_nil]. }
        apply (rw_cells_transport rsegs _ m5 m6a _ _ ERR5) in MU6a as ERR6a; [| exact WM6a| unfold RERRNO; blia1 KOFF].
        assert (IM6a : IMPL_mem m6a) by (eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; blia1 KOFF| exact IM5]).
        assert (GM6a : GOT_mem m6a) by (eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; blia1 KOFF| exact GM5]).
        apply (rw_cells_transport rsegs _ m5 m6a _ _ FR5) in MU6a as FR6a; [| exact WM6a| cbn; lia].
        assert (F26a : Forall2 (fun q X => EXTobj LB5 m6a q X) (sk_elems K) es).
        { eapply (EXTs_frame LB5 (hs_lb_remove H (sk_id K) LB5) LB5 (bv_unsigned sp + -32) m5 m6a); [exact F2| | exact (SUBL _ _)| exact XPh|].
          - intros b Hb. fold EB in Hb.
            apply (proj2 (proj2 (proj2 (lb_remove_exact H HH _ _ _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HEAP5) KIN)) b)).
            split; [eapply EXTs_owned; [exact F2| exact Hb]|].
            intros E. eapply (nodup_ids_app_ne (blocks_SK h K) EB); [exact NDX| left; reflexivity| exact Hb| symmetry; exact E].
          - intros b Hb. fold EB in Hb.
            assert (HbX : In b BX) by (rewrite BXE; apply in_or_app; right; exact Hb).
            pose proof (BELx b ltac:(unfold blocks_ENTRY; rewrite ?EXO; right; do 4 (apply in_or_app; right); exact HbX)). lia. }
        (* [comment removed for export] *)
        pose proof (popfree_exts_spec H HH) as PF. unfold popfree_exts_stmt, skpopfree_stmt_gen in PF.
        specialize (PF (extfree_spec H HH) EXTobj_frame_law EXTobj_owned_law GOT_echfree_frame ltac:(unfold P_ossl_echext_free; lia) ltac:(reflexivity)).
        eapply (sr_seq H HH).
        { eapply PF with (a := h) (K := sk_with_thunk K O_SK_FREETH P_sk_OSSL_ECHEXT_freefunc_thunk) (xs := es) (lo := lo) (B := B) (LB := LB5) (s := st5) (errv := errv);
            rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?unsigned_lit, ?errno_RATP by lia; try reflexivity.
          all: try first [exact SO6a| exact LEN| exact F26a| exact NDX| exact HP6a| exact KREL5| exact AUX6a| exact ST6a| exact CEIL| exact ERR6a| exact MI6a| exact IM6a| exact GM6a| exact GG6a].
          all: try (unfold is_sk_freefunc_thunk; left; reflexivity).
          all: unfold SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, RFREE_STACK, EF_R7; try lia.
          all: rewrite unsigned_lit by lia; reflexivity. }
        clear PF. intros [ms6 mo6] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c0' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & v3 & v4 & v5 & v6 & m6 & st6 & LB6 &
                        -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & PERM6 & HP6 & XP6 & IM6 & GM6 & GG6).
        rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM6. fold EB in PERM6.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6.
        replace (ret_pc (Z_to_bv 64 EF_R7)) with (Z_to_bv 64 EF_R7) by (symmetry; apply ret_pc_even; [unfold EF_R7; lia| reflexivity]).
        pose proof PERM6 as P6. rewrite app_assoc in P6.
        assert (SUB65 : forall b, In b LB6 -> In b LB5) by (intros b Hb; eapply Permutation_in; [exact P6| apply in_or_app; right; exact Hb]).
        assert (EIN6 : In (en_id x, p, ENTRY_SIZE) LB6).
        { eapply perm_in_rest; [exact P6| exact EIN5|]. apply NOTHD. intros b Hb. do 4 (apply in_or_app; right). rewrite BXE. exact Hb. }
        assert (SUBR : forall b, In b LB6 -> In b (hs_lb_remove H (sk_id K) LB5)).
        { eapply (perm_rest_sub_remove H HH); [exact HEAP5| exact P6|]. apply in_or_app. left. left. reflexivity. }
        apply (sr_done H HH). cbn [cfg_ms cfg_model].
        exists (Z_to_bv 64 EF_R7), v0, v1, v2, c0', c1', c2', c3', c4', c5', c6', c7', v3, v4, v5, v6, m6, st6, LB6.
        split; [reflexivity|]. split; [exact KREL6|]. split; [exact MP6|]. split; [exact MI6|]. split; [exact ST6|].
        split; [exact ERR6|]. split; [exact AUX6|]. split; [exact HP6|]. split; [exact EIN6|].
        split; [rewrite BXE; first [exact P6| rewrite app_assoc; exact P6| rewrite <- app_assoc; exact P6]|]. split; [exact SUB65|].
        split.
        { eapply xpres_trans; [eapply xpres_weaken; [exact XP05| lia| exact SUB65| auto]|].
          eapply xpres_trans; [eapply xpres_weaken; [exact XPh| lia| exact SUBR| auto]|].
          eapply xpres_weaken; [exact XP6| lia| auto| auto]. }
        split; [exact IM6|]. split; [exact GM6|]. split; [exact GG6|].
        eapply xpres_rw_cells'; [exact XP6| exact FR6a| left; cbn; lia| constructor].
      - (* [comment removed for export] *)
        assert (BXE : BX = []) by (unfold BX, blocks_EXTS; rewrite ?EXO; reflexivity).
        rewrite XS5' in *.
        eapply (sr_evt_krel H HH); [exact KREL5| eapply e_seg6n with (lo := lo); rewrite ?unsigned_lit by lia; [exact GG5| exact ST5| exact CEIL| lia| exact MI5]|].
        intros ms6 (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6 & rax6 & -> & MU6 & WM6 & MI6 & ST6 & GG6).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU6, ST6 by lia.
        apply (sr_done H HH). cbn [cfg_ms cfg_model].
        exists rax6, y0, y1, y2, (Z_to_bv 64 0), c1, c2, c3, c4, c5, c6, c7, y3, y4, y5, y6, m6, st5, LB5.
        split; [reflexivity|]. split; [exact KREL5|]. split; [apply (mpres_refl H HH)|]. split; [exact MI6|]. split; [exact ST6|].
        split; [eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6| unfold RERRNO; cbn; lia]|].
        split. { eapply (HH_rauxv_frame H HH); [exact AUX5| exact MU6| exact WM6|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        split. { eapply (HH_RHEAP_frame H HH); [exact HEAP5| exact MU6| exact WM6|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [exact EIN5|]. rewrite BXE. cbn [app]. split; [apply Permutation_refl|]. split; [auto|].
        split. { eapply xpres_trans; [exact XP05|]. eapply xpres_of_munch; [exact MU6| exact WM6| | exact HB5]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [eapply IMPL_across; [exact MU6| exact WM6| unfold A_malloc_impl; cbn; lia| exact IM5]|].
        split; [eapply GOT_across; [exact MU6| exact WM6| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM5]|].
        split; [exact GG6|].
        eapply rw_cells_transport; [exact FR5| exact MU6| exact WM6| cbn; lia]. }
    (* [comment removed for export] *)
    eapply (sr_seq H HH); [exact MID|].
    intros [ms6 mo6] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (rax2 & k0 & k1 & k2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & k3 & k4 & k5 & k6 & m6 & st6 & LB6 &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & HP6 & EIN6 & PERMX & SUB65 & XPM & IM6 & GM6 & GG6 & FR6).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply e_seg7; [exact FR6| exact MI6]|].
    intros ms7 (u1' & ->).
    unfold ef_frame in FR6.
    pose proof (stk_release rsegs m6 lo _ _ ST6 FR6 ltac:(lia)) as ST7. cbn [cells_size csize Nat.add] in ST7.
    replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in ST7 by lia.
    (* [comment removed for export] *)
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB6) (s := st6) (p := en_id x) (n := ENTRY_SIZE); try reflexivity.
      all: try first [exact HP6| exact KREL6| exact EIN6| exact AUX6| exact SPB| exact ST7| exact CEIL| exact MI6| exact IM6| exact GM6| exact RAE].
      all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR6]. }
    intros [ms8 mo8] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m8 & st8 &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & IM8 & GM8).
    rewrite errno_RATP in ERR8.
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, e0, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, m8, st8, (hs_lb_remove H (en_id x) LB6).
    split; [reflexivity|]. split; [exact KREL8|].
    split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP3| eapply (mpres_trans H HH); [exact MP4| eapply (mpres_trans H HH); [exact MP5| eapply (mpres_trans H HH); [exact MP6| exact MP8]]]]]|].
    split; [exact MI8|]. split; [exact ST8|]. split; [rewrite errno_RATP; exact ERR8|]. split; [exact AUX8|].
    split.
    { unfold blocks_ENTRY. fold Bpn Bpub Bsu Benc BX.
      apply (perm_chain5 (en_id x, p, ENTRY_SIZE) Bpn Bpub Bsu Benc BX LB LB2 LB3 LB4 LB5 LB6);
        [exact PERM2| exact PERM3| exact PERM4| exact PERM5| exact PERMX| eapply (lb_remove_perm H HH); [exact HP6| exact EIN6]]. }
    split; [exact HEAP8|].
    split. { eapply xpres_trans; [eapply xpres_weaken; [exact XPM| lia| exact (SUBL _ _)| auto]| exact XP8]. }
    split; [exact IM8|]. split; [exact GM8|].
    eapply GOT_echfree_xpres; [exact XP8| constructor| exact GG6].
  Qed.

  (* [comment removed for export] *)
  Lemma popfree_entries_spec : popfree_entries_stmt H.
  Proof. unfold popfree_entries_stmt. apply (skpopfree_spec H HH). Qed.
End W.
