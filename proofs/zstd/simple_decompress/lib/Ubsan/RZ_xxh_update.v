(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_imgfacts RZ_libc_iface RZ_frame_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section UPDATE.
  Hypothesis MEMCPY : zd_memcpyZ_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP STA IN : Z) (inb : list byte) (msz lo : Z).
  Hypothesis RMS : 0 <= msz < 32.
  Hypothesis RSTA : 4096 <= STA.  Hypothesis RSTA2 : STA + 88 <= 2^47.
  Hypothesis RSTA8 : STA mod 8 = 0.
  Hypothesis ST : stk usegs m lo SP.
  Hypothesis RLO : 4096 <= lo.  Hypothesis LO : lo <= SP - 96.  Hypothesis RSP : SP <= 2^47.
  Hypothesis SS : STA + 88 <= lo \/ SP <= STA.
  Hypothesis MI : mem_inv usegs m.

  Notation W := [(STA, STA + 88); (SP - 96, SP)].
  Notation POST := (zd_xxh_update_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP STA lo m).
  Notation len := (zlen inb).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -80)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition FRINV (m1 : fmem) : Prop :=
    (exists j8, rw_cells usegs m1 (SP + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk usegs m1 lo (SP + -80) /\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Lemma p_epi : forall m1 csh jm' msz' j2' (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    FRINV m1 ->
    rw_cells usegs m1 STA csh -> cells_size csh = 40%nat ->
    rw_cells usegs m1 (STA + 40) [CB 32 jm'; C4 (Z_to_bv 64 msz'); CB 12 j2'] -> 0 <= msz' < 32 ->
    evt usegs POST (STpc 0x2cfb8 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros m1 csh jm' msz' j2' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
           ([j8 FR1] & ST1 & MU1 & WM1 & MI1) HC HSZ MTC RM.
    do 10 zstep.
    release_frame FR1 ST1 SP.
    zstep. zstep.
    apply evt_done. unfold zd_xxh_update_post.
    do 14 eexists. exists m1, msz'. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [| exact RM].
    assert (ALL : rw_cells usegs m1 STA (csh ++ [CB 32 jm'; C4 (Z_to_bv 64 msz'); CB 12 j2'])).
    { apply (proj2 (ZdWalkKit.rw_cells_app _ _ _ _ _)). split; [exact HC|]. rewrite HSZ. exact MTC. }
    change (csh ++ [CB 32 jm'; C4 (Z_to_bv 64 msz'); CB 12 j2']) with (csh ++ [CB 32 jm'] ++ [C4 (Z_to_bv 64 msz'); CB 12 j2']) in ALL.
    rewrite app_assoc in ALL.
    apply (rw_cells_merge usegs m1 STA [] (csh ++ [CB 32 jm']) _) in ALL. cbn [app] in ALL.
    rewrite cells_size_app, HSZ in ALL. change (40 + cells_size [CB 32 jm'])%nat with 72%nat in ALL.
    unfold xxh_state, xxh_cells. do 2 eexists. exact ALL.
  Qed.

  (* [comment removed for export] *)
  Lemma mtc_split : forall mm jm' v j2', rw_cells usegs mm (STA + 40) [CB 32 jm'; C4 v; CB 12 j2'] ->
    rw_cells usegs mm (STA + 40) [CB 32 jm'] /\ rw_cells usegs mm (STA + 72) [C4 v; CB 12 j2'].
  Proof.
    intros mm jm' v j2' H. apply (proj1 (ZdWalkKit.rw_cells_app _ _ _ [CB 32 _] _)) in H. destruct H as [H1 H2].
    cbn [cells_size csize Nat.add] in H2. replace (STA + 40 + Z.of_nat 32) with (STA + 72) in H2 by lia. split; assumption.
  Qed.
  Lemma mtc_join : forall mm jm' v j2', rw_cells usegs mm (STA + 40) [CB 32 jm'] -> rw_cells usegs mm (STA + 72) [C4 v; CB 12 j2'] ->
    rw_cells usegs mm (STA + 40) [CB 32 jm'; C4 v; CB 12 j2'].
  Proof.
    intros mm jm' v j2' H1 H2. apply (proj2 (ZdWalkKit.rw_cells_app _ _ _ [CB 32 _] _)). split; [exact H1|].
    cbn [cells_size csize Nat.add]. replace (STA + 40 + Z.of_nat 32) with (STA + 72) by lia. exact H2.
  Qed.

  Section NONNULL.
  Hypothesis INB : bytes_at usegs m IN inb.
  Hypothesis RIN : 4096 <= IN.  Hypothesis RIN2 : IN + len <= 2^47.
  Hypothesis DSI : STA + 88 <= IN \/ IN + len <= STA.
  Hypothesis DIS : IN + len <= lo \/ SP <= IN.
  Variables (jt jv jm j2 : list byte).
  Hypothesis HEADC : rw_cells usegs m STA [CB 8 jt; CB 32 jv].
  Hypothesis MTC : rw_cells usegs m (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 msz); CB 12 j2].

  Lemma inb_suffix : forall mm p, bytes_at usegs mm IN inb -> 0 <= p <= len ->
    bytes_at usegs mm (IN + p) (skipn (Z.to_nat p) inb) /\ length (skipn (Z.to_nat p) inb) = Z.to_nat (len - p).
  Proof.
    intros mm p H Hp. rewrite <- (firstn_skipn (Z.to_nat p) inb) in H.
    apply (proj1 (bytes_at_app usegs mm IN _ _)) in H. destruct H as [_ H].
    rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia. split; [exact H|]. rewrite length_skipn. lia.
  Qed.
  Lemma inb_prefix : forall mm k, bytes_at usegs mm IN inb -> 0 <= k <= len ->
    bytes_at usegs mm IN (firstn (Z.to_nat k) inb) /\ length (firstn (Z.to_nat k) inb) = Z.to_nat k.
  Proof.
    intros mm k H Hk. rewrite <- (firstn_skipn (Z.to_nat k) inb) in H.
    apply (proj1 (bytes_at_app usegs mm IN _ _)) in H. destruct H as [H _]. split; [exact H|]. apply firstn_length_le. lia.
  Qed.

  Lemma inb_sub : forall mm p k, bytes_at usegs mm IN inb -> 0 <= p -> 0 <= k -> p + k <= len ->
    exists bs, bytes_at usegs mm (IN + p) bs /\ zlen bs = k.
  Proof.
    intros mm p k H Hp Hk Hpk. destruct (inb_suffix mm p H ltac:(lia)) as [S SL].
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat p) inb)) in S.
    apply (proj1 (bytes_at_app usegs mm (IN + p) _ _)) in S. destruct S as [S _].
    eexists. split; [exact S|]. rewrite firstn_length_le by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_tail : forall m1 csh jm' j2' p (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    FRINV m1 -> bytes_at usegs m1 IN inb ->
    rw_cells usegs m1 STA csh -> cells_size csh = 40%nat ->
    rw_cells usegs m1 (STA + 40) [CB 32 jm'; C4 (Z_to_bv 64 0); CB 12 j2'] ->
    0 <= p <= len -> len - p < 32 ->
    evt usegs POST (STpc 0x2cfa0 m1 x1 x5 x6 x7 (Z_to_bv 64 STA) (Z_to_bv 64 (STA + 40)) x10 (Z_to_bv 64 (IN + p)) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (IN + len)) x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros m1 csh jm' j2' p x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31
           FI INB1 HC HSZ MTC1 RP RL.
    pose proof FI as ([j8 FR1] & ST1 & MU1 & WM1 & MI1).
    assert (LENP : zlen inb = len) by reflexivity.
    zstep. if_cases K; zify_cond K.
    - eapply (p_epi m1 csh jm' 0); try eassumption; lia.
    - zstep. zstep. zstep. zstep.
      replace (IN + len - (IN + p)) with (len - p) by lia.
      destruct (inb_suffix m1 p INB1 RP) as [SUF SUFL].
      destruct (mtc_split _ _ _ _ MTC1) as [MC TC]. clear MTC1.
      destruct (cb_carve usegs m1 (STA + 40) 32 jm' 0 (len - p) MC ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & M1 & M2 & M3).
      replace (STA + 40 + 0) with (STA + 40) in * by lia.
      call (MEMCPY (STA + 40) (IN + p) (len - p));
        [ exact SUF | exact SUFL | exact M2 | lia | exact MI1 | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      rename PC into M2'.
      replace (STA + 40) with (STA + 40 + 0) in M2' by lia.
      replace (STA + 40 + (len - p)) with (STA + 40 + 0 + (len - p)) in M3 by lia.
      destruct (cb_uncarve usegs _ (STA + 40) 32 0 (len - p) _ _ _ _ _ _ M1 M2' M3 ltac:(lia) ltac:(lia) ltac:(lia)) as [jm2 MC2].
      pose proof (mtc_join _ _ _ _ MC2 TC) as MTC2.
      zstep.
      eapply (p_epi _ csh jm2 (len - p)); try eassumption; try lia.
      split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| eassumption].
  Qed.
  (* [comment removed for export] *)
  Lemma p_loop : forall (n : nat) m1 wt w0 w1 w2 w3 jm' j2' p
      (x1 x5 x6 x7 x15 x16 x17 x19 x20 x22 x23 x28 x29 x30 x31 : word),
    len - p <= Z.of_nat n ->
    FRINV m1 -> bytes_at usegs m1 IN inb ->
    rw_cells usegs m1 STA [C8 wt; C8 w0; C8 w1; C8 w2; C8 w3] ->
    rw_cells usegs m1 (STA + 40) [CB 32 jm'; C4 (Z_to_bv 64 0); CB 12 j2'] ->
    0 <= p -> p + 32 <= len ->
    evt usegs POST (STpc 0x2cd98 m1 x1 x5 x6 x7 (Z_to_bv 64 STA) (Z_to_bv 64 (STA + 40)) (Z_to_bv 64 (STA + 16)) (Z_to_bv 64 (IN + p))
                         (Z_to_bv 64 (STA + 24)) (Z_to_bv 64 (IN + len + -32)) (Z_to_bv 64 18446744073709551607) x15 x16 x17
                         (Z_to_bv 64 (IN + len)) x19 x20 (Z_to_bv 64 (STA + 8)) x22 x23 x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros m1 wt w0 w1 w2 w3 jm' j2' p x1 x5 x6 x7 x15 x16 x17 x19 x20 x22 x23 x28 x29 x30 x31
           RN FI INB1 HC MTC1 RP RPL; [exfalso; lia|].
    destruct FI as ([j8 FR1] & ST1 & MU1 & WM1 & MI1).
    destruct (inb_sub m1 p 32 INB1 RP ltac:(lia) RPL) as (qb & QB & QBL).
    remember (IN + p) as Q eqn:EQ.
    Time kx_autoLx [0x2cd98; 0x2cfa0] 400%nat
      [KZRange STA 4096 (2^47); KZRange IN 4096 (2^47); KZRange len 0 (2^47); KZRange (IN + len) 4096 (2^47);
       KZRange Q 4096 (2^47); KZRange (Q + 32) 4096 (2^47);
       KZWr STA 40; KZDisj STA 88 Q 32]
      [(Q, 32)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d27c) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: kx_abs.
    all: rewrite ?Z.mod_small in * by lia.
    all: subst Q; replace (IN + p + 32) with (IN + (p + 32)) by lia.
    all: first [ eapply (IH _ _ _ _ _ _ _ _ (p + 32)); try eassumption; try lia;
                 split; [eexists; exact FR1|]; split; [exact ST1|]; split; [exact MU1|]; split; [exact WM1| exact KXMI]
               | eapply (p_tail _ _ _ _ (p + 32)); try eassumption; try reflexivity; try lia;
                 split; [eexists; exact FR1|]; split; [exact ST1|]; split; [exact MU1|]; split; [exact WM1| exact KXMI] ].
  Qed.
  (* [comment removed for export] *)
  Lemma p_mid : forall m1 wt w0 w1 w2 w3 jm' j2' p Q
      (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x19 x20 x22 x23 x28 x29 x30 x31 : word),
    FRINV m1 -> bytes_at usegs m1 IN inb ->
    rw_cells usegs m1 STA [C8 wt; C8 w0; C8 w1; C8 w2; C8 w3] ->
    rw_cells usegs m1 (STA + 40) [CB 32 jm'; C4 (Z_to_bv 64 0); CB 12 j2'] ->
    0 <= p <= len -> Q = IN + p ->
    evt usegs POST (STpc 0x2cd44 m1 x1 x5 x6 x7 (Z_to_bv 64 STA) (Z_to_bv 64 (STA + 40)) x10 (Z_to_bv 64 Q) (Z_to_bv 64 len)
                         x13 x14 x15 x16 x17 (Z_to_bv 64 IN) x19 x20 (Z_to_bv 64 (STA + 8)) x22 x23 x28 x29 x30 x31).
  Proof.
    intros m1 wt w0 w1 w2 w3 jm' j2' p Q x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x19 x20 x22 x23 x28 x29 x30 x31
           FI INB1 HC MTC1 RP EQ. subst Q.
    pose proof FI as ([j8 FR1] & ST1 & MU1 & WM1 & MI1).
    kx_autoLx [0x2cd98; 0x2cfa0] 100%nat
      [KZRange STA 4096 (2^47); KZRange IN 4096 (2^47); KZRange len 0 (2^47); KZRange (IN + len) 4096 (2^47);
       KZRange p 0 (2^47); KZRange (IN + p) 4096 (2^47); KZWr STA 40]
      [].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d27c) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: kx_abs.
    all: rewrite ?Z.mod_small in * by lia.
    all: first [ eapply (p_tail m1 _ jm' j2' p); try eassumption; try reflexivity; lia
               | eapply (p_loop (Z.to_nat (len - p)) m1 wt w0 w1 w2 w3 jm' j2' p); try eassumption; lia ].
  Qed.
  (* [comment removed for export] *)
  Lemma p_stripe : forall m1 wt jv' jm' j2' (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 : word),
    FRINV m1 -> bytes_at usegs m1 IN inb ->
    rw_cells usegs m1 STA [C8 wt; CB 32 jv'] ->
    rw_cells usegs m1 (STA + 40) [CB 32 jm'; C4 (Z_to_bv 64 msz); CB 12 j2'] ->
    0 < msz -> 32 - msz <= len ->
    evt usegs POST (STpc 0x2cb04 m1 x1 x5 x6 x7 (Z_to_bv 64 STA) (Z_to_bv 64 (STA + 40)) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 IN) x19 x20 (Z_to_bv 64 (STA + 8)) (Z_to_bv 64 (-1 * IN + -1)) (Z_to_bv 64 len) x28 x29 x30 x31).
  Proof.
    intros m1 wt jv' jm' j2' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 FI INB1 HC MTC1 RM0 RML.
    destruct FI as ([j8 FR1] & ST1 & MU1 & WM1 & MI1).
    kx_autoLx [0x2cd44] 300%nat
      [KZRange STA 4096 (2^47); KZRange IN 4096 (2^47); KZRange len 0 (2^47); KZRange (IN + len) 4096 (2^47); KZRange msz 1 31;
       KZWr STA 40; KZWr (STA + 40) 48; KZWord (STA + 40 + 32) 4 msz]
      [(STA, 40); (STA + 40, 48)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d27c) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    eapply (p_mid _ _ _ _ _ _ _ _ (32 - msz) _); try eassumption; try lia.
    split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1| exact KXMI].
  Qed.

  Lemma update_nonnull :
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STA) (Z_to_bv 64 IN) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_UPDATE) fc None m (seg_rom usegs)).
  Proof.
    unfold PZD_XXH_UPDATE.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof ST as (LO0 & _ & _).
    pose proof (stk_not_ro _ _ _ MI ST ltac:(lia)) as NRS.
    pose proof (rw_cells_not_ro _ _ _ MI HEADC ltac:(cbn; lia)) as NR1. cbn [cells_size csize Nat.add] in NR1.
    pose proof (rw_cells_not_ro _ _ _ MI MTC ltac:(cbn; lia)) as NR2. cbn [cells_size csize Nat.add] in NR2.
    carve_frame 80%nat ST.
    kx_autoLx [0x2cd44] 400%nat
      [KZImg 0x10fe0 0x11060; KZRange STA 4096 (2^47); KZRange SP 4096 (2^47); KZRange IN 4096 (2^47); KZRange len 0 (2^47);
       KZRange (IN + len) 4096 (2^47); KZRange msz 0 31; KZAlign STA 8;
       KZWr (SP - 80) 80; KZWr STA 40; KZWr (STA + 40) 48; KZWord (STA + 40 + 32) 4 msz;
       KZDisj STA 88 IN len; KZDisj (SP - 80) 80 IN len; KZDisj (SP - 80) 80 STA 88;
       KZDisj (SP - 80) 80 69432 512; KZDisj STA 88 69432 512]
      [(IN, len); (STA, 40); (STA + 40, 48); (SP - 80, 80)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d27c) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem.
    all: kx_abs.
    all: rewrite ?Z.mod_small in * by lia.
    all: assert (FI : forall mm j8, rw_cells usegs mm (SP + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                  stk usegs mm lo (SP + -80) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> FRINV mm)
           by (intros mm j8 A1 A2 A3 A4 A5; split; [eexists; exact A1|]; split; [exact A2|]; split; [exact A3|]; split; [exact A4| exact A5]).
    - (* [comment removed for export] *)
      assert (E0 : msz = 0) by lia. rewrite E0 in MTC.
      destruct (cb32_as_c8s usegs _ STA _ _ HEADC) as (w0 & w1 & w2 & w3 & HC2).
      eapply (p_mid _ _ _ _ _ _ _ _ 0 IN); try eassumption; try lia. eapply FI; eassumption.
    - (* [comment removed for export] *)
      replace (STA + msz + 40) with (STA + 40 + msz) by lia. replace (-1 * msz + 32) with (32 - msz) by lia.
      destruct (inb_prefix _ (32 - msz) INB ltac:(lia)) as [PRE PREL].
      destruct (mtc_split _ _ _ _ MTC) as [MC TC]. clear MTC.
      destruct (cb_carve usegs _ (STA + 40) 32 jm msz (32 - msz) MC ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & M1 & M2 & M3).
      call (MEMCPY (STA + 40 + msz) IN (32 - msz));
        [ exact PRE | exact PREL | exact M2 | lia | exact KXMI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      rename PC into M2'.
      destruct (cb_uncarve usegs _ (STA + 40) 32 msz (32 - msz) _ _ _ _ _ _ M1 M2' M3 ltac:(lia) ltac:(lia) ltac:(lia)) as [jm2 MC2].
      pose proof (mtc_join _ _ _ _ MC2 TC) as MTC2.
      eapply p_stripe; try eassumption; try lia. eapply FI; eassumption.
    - (* [comment removed for export] *)
      replace (STA + msz + 40) with (STA + 40 + msz) by lia.
      assert (PREL : length inb = Z.to_nat len) by lia.
      destruct (mtc_split _ _ _ _ MTC) as [MC TC]. clear MTC.
      destruct (cb_carve usegs _ (STA + 40) 32 jm msz len MC ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & M1 & M2 & M3).
      call (MEMCPY (STA + 40 + msz) IN len);
        [ exact INB | exact PREL | exact M2 | lia | exact KXMI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      rename PC into M2'.
      destruct (cb_uncarve usegs _ (STA + 40) 32 msz len _ _ _ _ _ _ M1 M2' M3 ltac:(lia) ltac:(lia) ltac:(lia)) as [jm2 MC2].
      pose proof (mtc_join _ _ _ _ MC2 TC) as MTC2.
      zstep. rewrite sx32w_small by lia.
      zstep. zstep. zstep.
      eapply (p_epi _ _ jm2 (msz + len)); try eassumption; try reflexivity; try lia.
      eapply FI; eassumption.
  Qed.
  End NONNULL.
  (* [comment removed for export] *)
  Lemma update_null : xxh_state m STA msz ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STA) (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_UPDATE) fc None m (seg_rom usegs)).
  Proof.
    intros XS. unfold PZD_XXH_UPDATE.
    destruct XS as (j1 & j2 & XC). unfold xxh_cells in XC.
    apply (rw_cells_split_CB usegs _ _ [] _ _ _ [40; 32]%nat) in XC; [| reflexivity]. cbn [mk_CB_cells app] in XC.
    apply (proj1 (ZdWalkKit.rw_cells_app _ _ _ [CB 40 _] _)) in XC. destruct XC as [HC MTC]. cbn [cells_size csize Nat.add] in MTC.
    replace (STA + Z.of_nat 40) with (STA + 40) in MTC by lia.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof ST as (LO0 & _ & _).
    carve_frame 80%nat ST.
    do 10 zs.
    zstep. if_true. zstep. if_true.
    eapply (p_epi _ _ _ msz); try eassumption; try reflexivity; try lia.
    split; [eexists; exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
  Qed.
End UPDATE.

Theorem zd_xxh_update_proof : zd_memcpyZ_stmt -> zd_xxh_update_stmt.
Proof.
  intros MEMCPY. intros until lo. intros XS RMS RSTA RSTA8 RSTA2 INCASE ST RLO LO RSP SS MI -> ->.
  destruct INCASE as [[-> ->] | (INB & -> & RIN & RIN2 & DSI & DIS)].
  - eapply update_null; eassumption.
  - destruct XS as (j1 & j2 & XC). unfold xxh_cells in XC.
    apply (rw_cells_split_CB usegs _ _ [] _ _ _ [8; 32; 32]%nat) in XC; [| reflexivity]. cbn [mk_CB_cells app] in XC.
    apply (proj1 (ZdWalkKit.rw_cells_app _ _ _ [CB 8 _; CB 32 _] _)) in XC. destruct XC as [HEADC MTC]. cbn [cells_size csize Nat.add] in MTC.
    replace (STA + Z.of_nat 40) with (STA + 40) in MTC by lia.
    eapply update_nonnull; eassumption.
Qed.
Print Assumptions zd_xxh_update_proof.
