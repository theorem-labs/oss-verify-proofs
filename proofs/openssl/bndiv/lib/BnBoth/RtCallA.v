(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition icall_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (Σ : rts RT) (OW LB : list block) (lo D N : Z) (m : mem)
    (Qm : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono bsegs m m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (D <= a < D + N)) m m'
    /\ Qm m'.

Lemma AH_same' : forall Σ OW LB m m', AHEAP Σ OW LB m -> ART RT Σ m' -> AHEAP Σ OW LB m'.
Proof. intros Σ OW LB m m' (_ & H) HA. exact (conj HA H). Qed.

(* [comment removed for export] *)
Lemma blk_checked_dst : forall Σ OW LB m sp b d n,
  AHEAP Σ OW LB m -> In b (OW ++ LB) -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b -> 0 <= n ->
  checked_dst RT Σ m sp d n.
Proof.
  intros Σ OW LB m sp b d n H Hb H1 H2 Hn. pose proof (AH_acc _ _ _ _ b H Hb) as (WRB & ACCB). pose proof (AH_live _ _ _ _ b H Hb) as INL.
  split; [intros _; split; [eapply acc_sub; [exact ACCB | lia | lia] | left; exists (blk_addr b), (blk_size b); split; [exact INL | lia]] |].
  split; [intros i Hi; right; right; left; exists (blk_addr b), (blk_size b); split; [exact INL | lia] |].
  destruct WRB as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
  replace (d + i) with (blk_addr b + (d - blk_addr b + i)) by lia. apply W2. lia.
Qed.

Lemma blk_checked_src : forall Σ OW LB m sp lo b s n,
  AHEAP Σ OW LB m -> In b (OW ++ LB) -> blk_addr b <= s -> s + n <= blk_addr b + blk_size b -> ACEIL <= lo ->
  checked_src RT Σ m sp lo s n.
Proof.
  intros Σ OW LB m sp lo b s n H Hb H1 H2 CEIL. pose proof (AH_acc _ _ _ _ b H Hb) as (_ & ACCB). pose proof (AH_live _ _ _ _ b H Hb) as INL.
  pose proof (AH_range_gen _ _ _ _ b H Hb) as (_ & _ & _ & BC & _).
  split; [intros _; split; [eapply acc_sub; [exact ACCB | lia | lia] | left; exists (blk_addr b), (blk_size b); split; [exact INL | lia]] | left; lia].
Qed.

(* [comment removed for export] *)
Lemma asan_memcpy_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo d s : Z) (bs : list byte) (bd bsrc : block),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= d -> d + Z.of_nat (length bs) <= blk_addr bd + blk_size bd ->
  In bsrc (OW ++ LB) -> blk_addr bsrc <= s -> s + Z.of_nat (length bs) <= blk_addr bsrc + blk_size bsrc ->
  bytes_at bsegs m s bs -> (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) -> Z.of_nat (length bs) < 2^40 ->
  a0 = wz d -> a1 = wz s -> a2 = wz (Z.of_nat (length bs)) ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_asan_memcpy) fc None m (seg_rom bsegs))))
            (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz d) Σ OW LB lo d (Z.of_nat (length bs)) m
                              (fun m' => bytes_at bsegs m' d bs /\ wr_at bsegs m' d (Z.of_nat (length bs))))).
Proof.
  intros until bsrc. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 INS S1 S2 SRC DISJ HN -> -> ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
  pose proof (AH_range_gen _ _ _ _ bsrc HEAP INS) as (BS0 & _ & _ & BSC & _).
  pose proof (blk_checked_dst Σ OW LB m sp bd d _ HEAP IND D1 D2 ltac:(lia)) as CD.
  eapply cps_conseq; [ eapply (rc_asan_memcpy RT (@ar_RC AR) Σ PMc) with (d := d) (s := s) (bs := bs) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - unfold BnHeapA.ACEIL in *. lia.
  - unfold BnHeapA.ACEIL in *. lia.
  - exact HN.
  - exact SRC.
  - exact (blk_checked_src Σ OW LB m sp lo bsrc s _ HEAP INS S1 S2 CEIL).
  - exact CD.
  - exact DISJ.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact (AH_same' _ _ _ _ _ HEAP ART2)|]. split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    split; [exact BZ|]. destruct CD as (_ & _ & W). exact (wr_at_transport bsegs m m2 d _ W WM2).
Qed.

(* [comment removed for export] *)
Lemma asan_memset_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo d n : Z) (c : byte) (bd : block),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= d -> d + n <= blk_addr bd + blk_size bd -> 0 <= n < 2^40 ->
  a0 = wz d -> a1 = wz (bv_unsigned c) -> a2 = wz n ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_asan_memset) fc None m (seg_rom bsegs))))
            (ASTA RT Σ PMc (icall_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz d) Σ OW LB lo d n m
                              (fun m' => bytes_at bsegs m' d (repeat c (Z.to_nat n)) /\ wr_at bsegs m' d n))).
Proof.
  intros until bd. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 HN -> -> ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
  pose proof (blk_checked_dst Σ OW LB m sp bd d n HEAP IND D1 D2 ltac:(lia)) as CD.
  eapply cps_conseq; [ eapply (rc_asan_memset RT (@ar_RC AR) Σ PMc) with (d := d) (n := n) (c := c) (lo := lo); try reflexivity | intros c0 Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - unfold BnHeapA.ACEIL in *. lia.
  - lia.
  - exact CD.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c0 Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold icall_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact (AH_same' _ _ _ _ _ HEAP ART2)|]. split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    split; [exact BZ|]. destruct CD as (_ & _ & W). exact (wr_at_transport bsegs m m2 d _ W WM2).
Qed.

End WithRT.
