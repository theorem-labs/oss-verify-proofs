From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require RoAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Prog Require Import memset_c memset_ro_c memset_ro.
Import ListNotations.
Open Scope Z_scope.

(* calloc's clear of a block of 4096 bytes or more: musl's mal0_clear (the tail page is cleared with memset, then
   the page loop reads two 8-byte words at a time from the top of each page down and, at the first nonzero pair,
   clears with memset the page from its start up to the end of that pair), then the tail-called memset of what is
   left at the start of the block. The walk
   runs from calloc+0x64 (0x17b34) to the return of the tail-called memset, and ends in the same postcondition as
   CallocRun.run_clear (the arm below 4096 bytes).
   Ported from mbedtls/fuzz_pkcs7 lib/U/HP_calloc.v on ossv/recipes 4b6f0df50aa (rcalloc_clear, rcc_outer,
   rcc_inner, rcc_final, rcc_after_memset, rblk_chunk, rblk_read8): link's calloc is the same 78 instructions
   (calloc at 0x3f960 there, 0x17ad0 here; memset at 0x46e44 there, 0x1f894 here). The writable block is carried as
   Frame.stk instead of wr_at plus a premise on the image, and memset is link's frame-v3 contract memset_ro_holds
   (RoAdapt.not_ro, MemNorm.ro_agree), as in CallocRun.run_clear. *)

Definition czeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Ltac ulit := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.
Ltac ulit_in H := repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.

Lemma czeros_join : forall m a k l,
  bytes_at rsegs m a (czeros k) -> bytes_at rsegs m (a + Z.of_nat k) (czeros l) -> bytes_at rsegs m a (czeros (k + l)).
Proof.
  intros m a k l B1 B2. unfold czeros. rewrite repeat_app.
  apply (proj2 (bytes_at_app rsegs m a (repeat (Z_to_bv 8 0) k) (repeat (Z_to_bv 8 0) l))).
  split; [exact B1|]. rewrite repeat_length. exact B2.
Qed.

Lemma le8_bytes : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma le8_zero : forall w : word, bv_unsigned w = 0 -> le8 w = czeros 8.
Proof. intros w H. rewrite <- (Z_to_bv_bv_unsigned w), H. first [reflexivity | vm_compute; reflexivity]. Qed.

Lemma stk_wr_at : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof.
  intros m lo hi (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
  destruct (H (lo + i) ltac:(lia)) as [W _]. exact W.
Qed.

Lemma nro_sub : forall A n b len, RoAdapt.not_ro rsegs A n -> A <= b -> b + len <= A + n -> RoAdapt.not_ro rsegs b len.
Proof.
  intros A n b len H H1 H2 i Hi. replace (b + i) with (A + (b - A + i)) by lia. apply H. lia.
Qed.

(* a part of the block, carved out for a memset *)
Lemma blk_chunk : forall m A n b len, stk rsegs m A (A + n) -> A <= b -> 0 <= len -> b + len <= A + n ->
  exists junk, rw_cells rsegs m b [CB (Z.to_nat len) junk].
Proof.
  intros m A n b len BK H1 H2 H3.
  destruct (stk_split rsegs m A b (A + n) BK ltac:(lia)) as [_ S1].
  destruct (stk_split rsegs m b (b + len) (A + n) S1 ltac:(lia)) as [S2 _].
  destruct (stk_carve rsegs m b (b + len) (Z.to_nat len) S2 ltac:(lia)) as [_ [junk J]].
  exists junk. replace (b + len - Z.of_nat (Z.to_nat len)) with b in J by lia. exact J.
Qed.

(* one 8-byte word of the block, read *)
Lemma blk_read8 : forall m A n a, stk rsegs m A (A + n) -> A <= a -> a + 8 <= A + n ->
  exists w : word, bytes_at rsegs m a (le8 w) /\ ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m A n a BK H1 H2.
  destruct (stk_split rsegs m A a (A + n) BK ltac:(lia)) as [_ S1].
  destruct (stk_split rsegs m a (a + 8) (A + n) S1 ltac:(lia)) as [S2 _].
  destruct (stk_bytes rsegs m a (a + 8) S2 ltac:(lia)) as (bs & L & B).
  replace (Z.to_nat (a + 8 - a)) with 8%nat in L by lia.
  exists (le_bytes_to_word bs). rewrite (le8_bytes bs L). split; [exact B|].
  pose proof (bytes_at_read rsegs m a bs 0 8 B ltac:(lia) ltac:(lia)) as R.
  assert (E8 : firstn 8 (skipn (Z.to_nat 0) bs) = bs).
  { change (skipn (Z.to_nat 0) bs) with bs. apply firstn_all2. rewrite L. apply Nat.le_refl. }
  rewrite Z.add_0_r, E8 in R. exact R.
Qed.

(* the state the walk carries between memsets: the frame of calloc, the block (present and writable), the
   footprint and the read-only agreement *)
Definition bk (m0 m : word -> option byte) (sp A n : Z) (junk : list byte) (rao s0o s1o : word) : Prop :=
  rw_cells rsegs m sp [CB 8 junk; C8 s1o; C8 s0o; C8 rao] /\ stk rsegs m A (A + n) /\
  munch [(A, A + n)] m0 m /\ wmono rsegs m0 m /\ MemNorm.ro_agree rsegs m.

Lemma bk_init : forall m sp A n junk rao s0o s1o,
  rw_cells rsegs m sp [CB 8 junk; C8 s1o; C8 s0o; C8 rao] -> stk rsegs m A (A + n) -> MemNorm.ro_agree rsegs m ->
  bk m m sp A n junk rao s0o s1o.
Proof.
  intros m sp A n junk rao s0o s1o FR BK RO.
  split; [exact FR|]. split; [exact BK|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact RO].
Qed.

(* after a memset of [b, b + len) inside the block *)
Lemma after_ms : forall m0 m m2 sp A n junk rao s0o s1o b len,
  bk m0 m sp A n junk rao s0o s1o -> A <= b -> 0 <= len -> b + len <= A + n -> A + n <= sp ->
  munch [(b, b + len)] m m2 -> wmono rsegs m m2 -> MemNorm.ro_agree rsegs m2 ->
  rw_cells rsegs m2 b [CB (Z.to_nat len) (repeat (Z_to_bv 8 0) (Z.to_nat len))] ->
  bk m0 m2 sp A n junk rao s0o s1o.
Proof.
  intros m0 m m2 sp A n junk rao s0o s1o b len (FR & BK & MU0 & WM0 & _) H1 H2 H3 H4 MU WM RO RW.
  split; [|split; [|split; [|split]]].
  - eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
    cbn [disjoint_from]. split; [right; lia | exact I].
  - destruct (stk_split rsegs m A b (A + n) BK ltac:(lia)) as [S1 S23].
    destruct (stk_split rsegs m b (b + len) (A + n) S23 ltac:(lia)) as [_ S3].
    apply (stk_merge rsegs m2 A b (A + n)); [| | lia].
    + eapply stk_transport_disjoint; [exact S1 | exact MU | exact WM |].
      cbn [disjoint_from]. split; [left; lia | exact I].
    + apply (stk_merge rsegs m2 b (b + len) (A + n)); [| | lia].
      * pose proof (stk_of_rw_cells rsegs m2 b _ RW) as S. cbn [cells_size csize] in S.
        rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
      * eapply stk_transport_disjoint; [exact S3 | exact MU | exact WM |].
        cbn [disjoint_from]. split; [right; lia | exact I].
  - eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
    intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx _]. split; [lia | exact I].
  - eapply wmono_trans; [exact WM0 | exact WM].
  - exact RO.
Qed.

(* the zeroed tail grows by the part a memset cleared *)
Lemma zs_after_ms : forall m m2 b r A n,
  b <= r -> r <= A + n ->
  bytes_at rsegs m r (czeros (Z.to_nat (A + n - r))) ->
  munch [(b, r)] m m2 ->
  rw_cells rsegs m2 b [CB (Z.to_nat (r - b)) (repeat (Z_to_bv 8 0) (Z.to_nat (r - b)))] ->
  bytes_at rsegs m2 b (czeros (Z.to_nat (A + n - b))).
Proof.
  intros m m2 b r A n H1 H2 ZS MU RW.
  replace (Z.to_nat (A + n - b)) with (Z.to_nat (r - b) + Z.to_nat (A + n - r))%nat by lia.
  apply czeros_join.
  - destruct RW as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - rewrite Z2Nat.id by lia. replace (b + (r - b)) with r by lia.
    eapply bytes_at_transport; [exact ZS | exact MU |]. cbn [disjoint_from]. split; [right; lia | exact I].
Qed.

Section W.
Variables (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (rao s0o s1o s0 : word) (junk : list byte) (m0 : word -> option byte) (A n : Z).
Hypothesis HS0 : bv_unsigned s0 = A.
Hypothesis HA0 : 0 < A.
Hypothesis HAS : A + n <= bv_unsigned sp.
Hypothesis HN0 : 0 <= n.
Hypothesis NRO : RoAdapt.not_ro rsegs A n.

Definition big_post : machine_state -> Prop :=
  memset_post_ro rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    s0 (Z_to_bv 64 0) (Z_to_bv 64 n) m0.

(* 0x17bc0: memset(p, 0, k), tail-called after the frame is released; [p + k, p + n) is zero already *)
Lemma big_final : forall rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m k,
  bk m0 m (bv_unsigned sp) A n junk rao s0o s1o -> 0 <= k <= n ->
  bytes_at rsegs m (A + k) (czeros (Z.to_nat (n - k))) ->
  evt rsegs big_post
    (MS (mkR rax sp gp tp t0 t1 t2 s0 (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17bc0) fc None m (seg_rom rsegs)).
Proof.
  intros rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m k BKS Hk ZS.
  pose proof BKS as (FR & BK & MU0 & WM0 & RO).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound _ _ _ _ FR) as BF. cbn [cells_size csize Nat.add] in BF.
  do 8 step.
  destruct (blk_chunk m A n A k BK ltac:(lia) ltac:(lia) ltac:(lia)) as [jk CH].
  eapply evt_mono.
  { eapply memset_ro_holds.
    - rewrite HS0. ulit. exact CH.
    - rewrite HS0. ulit. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      apply (nro_sub A n); [exact NRO | lia | lia].
    - exact RO. }
  intros ms' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & RO' & RW).
  rewrite HS0 in MU, RW. ulit_in MU. ulit_in RW. rewrite Z.mod_0_l in RW by lia.
  unfold big_post, memset_post_ro. do 14 eexists. exists m'. split; [reflexivity|].
  rewrite HS0. ulit. rewrite Z.mod_0_l by lia.
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU].
           intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  split; [eapply wmono_trans; [exact WM0 | exact WM]|].
  split; [exact RO'|].
  unfold rw_cells, cells_at. split; [split|].
  - cbn [cells_wf cell_wf]. rewrite repeat_length. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    change (repeat (Z_to_bv 8 0) (Z.to_nat n)) with (czeros (Z.to_nat n)).
    replace (Z.to_nat n) with (Z.to_nat k + Z.to_nat (n - k))%nat by lia.
    apply czeros_join.
    + destruct RW as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
    + rewrite Z2Nat.id by lia. eapply bytes_at_transport; [exact ZS | exact MU |].
      unfold czeros. rewrite repeat_length. cbn [disjoint_from]. split; [right; lia | exact I].
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    pose proof (stk_wr_at m A (A + n) BK) as W. replace (A + n - A) with n in W by lia.
    eapply wr_at_transport; [exact W | exact WM].
Qed.

(* 0x17b8c, the inner loop of one page [b, b + 4096): r is the current word pair's end, [r, p + n) is zero *)
Definition inner_post (ra t0 t1 t2 s1 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (b : Z)
    : machine_state -> Prop :=
  fun ms' => exists r' (a3' a4' : word),
    bytes_at rsegs m r' (czeros (Z.to_nat (A + n - r'))) /\ b <= r' <= A + n /\
    ((b < r' /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r') (Z_to_bv 64 b) (Z_to_bv 64 (r' - b)) a3' a4' a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x17b68) fc None m (seg_rom rsegs)) \/
     (r' = b /\
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 b) (Z_to_bv 64 0) a3' a4' a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x17ba8) fc None m (seg_rom rsegs))).

Lemma big_inner : forall (j : nat) ra t0 t1 t2 s1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m b r,
  stk rsegs m A (A + n) -> A <= b -> r <= A + n -> r - b = 16 * Z.of_nat j -> (1 <= j)%nat ->
  bytes_at rsegs m r (czeros (Z.to_nat (A + n - r))) ->
  evt rsegs (inner_post ra t0 t1 t2 s1 a5 a6 a7 t3 t4 t5 t6 m b)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 b) (Z_to_bv 64 (r - b)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b8c) fc None m (seg_rom rsegs)).
Proof.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  induction j as [|j IH]; intros ra t0 t1 t2 s1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m b r BK HB HR HJ J1 ZS; [lia|].
  destruct (blk_read8 m A n (r + -16) BK ltac:(lia) ltac:(lia)) as (w1 & B1 & R1).
  destruct (blk_read8 m A n (r + -8) BK ltac:(lia) ltac:(lia)) as (w2 & B2 & R2).
  pose proof (zr_word w1) as W1R. pose proof (zr_word w2) as W2R. pose proof (zr_lor _ _ W1R W2R) as LR.
  unfold inr64 in W1R, W2R, LR.
  step. step. step. step.
  if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - apply evt_done. unfold inner_post. exists r. do 2 eexists.
    split; [exact ZS|]. split; [lia|]. left. split; [lia | reflexivity].
  - apply Z.lor_eq_0_iff in K. destruct K as [K1 K2].
    rewrite (le8_zero w1 K1) in B1. rewrite (le8_zero w2 K2) in B2.
    assert (ZS' : bytes_at rsegs m (r + -16) (czeros (Z.to_nat (A + n - (r + -16))))).
    { replace (Z.to_nat (A + n - (r + -16))) with (8 + (8 + Z.to_nat (A + n - r)))%nat by lia.
      apply czeros_join; [exact B1|]. replace (r + -16 + Z.of_nat 8) with (r + -8) by lia.
      apply czeros_join; [exact B2|]. replace (r + -8 + Z.of_nat 8) with r by lia. exact ZS. }
    step. step. step.
    if_cases K3; zify_cond K3; ulit_in K3;
      try (change 18446744073709551615 with (Z.ones 64) in K3; rewrite Z.land_ones, Z.mod_small in K3 by lia);
      rewrite ?unsigned_lit in K3 by lia.
    + replace (r - b + -16) with (r + -16 - b) by lia.
      apply (IH ra t0 t1 t2 s1 _ _ a5 a6 a7 t3 t4 t5 t6 m b (r + -16) BK HB); [lia | lia | | exact ZS'].
      destruct j; [lia | lia].
    + apply evt_done. unfold inner_post. exists b. do 2 eexists.
      split; [replace b with (r + -16) by lia; exact ZS'|]. split; [lia|].
      right. split; [reflexivity|]. replace (r + -16) with b by lia. replace (r - b + -16) with 0 by lia. reflexivity.
Qed.

(* 0x17b80, the head of the page loop: q is the end of the next page down, [q, p + n) is zero *)
Lemma big_outer : forall (N : nat) rax t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m q,
  bk m0 m (bv_unsigned sp) A n junk rao s0o s1o ->
  A + 4096 <= q -> q <= A + n -> q - A <= 4096 * Z.of_nat N ->
  bytes_at rsegs m q (czeros (Z.to_nat (A + n - q))) ->
  evt rsegs big_post
    (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b80) fc None m (seg_rom rsegs)).
Proof.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  induction N as [|N IH]; intros rax t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m q BKS HQ1 HQ2 HN ZS; [lia|].
  pose proof BKS as (FR & BK & MU0 & WM0 & RO).
  step. step. step.
  try replace (q + -2048 + -2048) with (q - 4096) by lia. try replace (q + -4096) with (q - 4096) by lia.
  set (b := q - 4096) in *. assert (Hb : b = q - 4096) by reflexivity. clearbody b.
  replace (Z_to_bv 64 4096) with (Z_to_bv 64 (q - b)) by (f_equal; lia).
  eapply evt_cut.
  { apply (big_inner 256 rax t0 t1 t2 s1 a3 a4 a5 a6 a7 t3 t4 t5 t6 m b q BK); [lia | lia | lia | lia | exact ZS]. }
  intros ms' (r' & a3' & a4' & ZS' & HB' & [[LT ->] | [Er ->]]).
  - (* a nonzero pair below r': memset(b, 0, r' - b) *)
    step. ulit. replace (r' - (r' - b)) with b by lia. step. step.
    destruct (blk_chunk m A n b (r' - b) BK ltac:(lia) ltac:(lia) ltac:(lia)) as [jk CH].
    eapply evt_cut.
    { eapply memset_ro_holds.
      - ulit. exact CH.
      - ulit. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        apply (nro_sub A n); [exact NRO | lia | lia].
      - exact RO. }
    intros ms'' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & RO2 & RW).
    ulit_in MU. ulit_in RW. rewrite Z.mod_0_l in RW by lia.
    replace (b + (r' - b)) with r' in MU by lia.
    rewrite (ret_pc_even 0x17b74) by first [lia | reflexivity].
    pose proof (after_ms m0 m m2 (bv_unsigned sp) A n junk rao s0o s1o b (r' - b) BKS ltac:(lia) ltac:(lia) ltac:(lia)
      HAS ltac:(replace (b + (r' - b)) with r' by lia; exact MU) WM RO2 RW) as BK2.
    pose proof (zs_after_ms m m2 b r' A n ltac:(lia) ltac:(lia) ZS' MU RW) as ZSb.
    clear ZS ZS' RW CH MU WM FR BK MU0 WM0 RO.
    step. rewrite HS0. ulit. step. ulit. step.
    assert (SH12 : Z.shiftr (b - A) 12 = (b - A) / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite ?SH12.
    if_cases K; zify_cond K; rewrite ?SH12 in K; rewrite ?unsigned_lit in K by (Z.div_mod_to_equations; lia).
    + apply (big_final _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (b - A) BK2); [lia|].
      replace (A + (b - A)) with b by lia. replace (n - (b - A)) with (A + n - b) by lia. exact ZSb.
    + apply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 b BK2); [Z.div_mod_to_equations; lia | lia | lia | exact ZSb].
  - (* every pair of the page is zero: memset(b, 0, 0) *)
    subst r'. step. ulit. replace (b - 0) with b by lia. step. step.
    destruct (blk_chunk m A n b 0 BK ltac:(lia) ltac:(lia) ltac:(lia)) as [jk CH].
    eapply evt_cut.
    { eapply memset_ro_holds.
      - ulit. exact CH.
      - ulit. cbn [cells_size csize]. intros i Hi. lia.
      - exact RO. }
    intros ms'' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & RO2 & RW).
    ulit_in MU. ulit_in RW. rewrite Z.mod_0_l in RW by lia.
    rewrite (ret_pc_even 0x17bb4) by first [lia | reflexivity].
    pose proof (after_ms m0 m m2 (bv_unsigned sp) A n junk rao s0o s1o b 0 BKS ltac:(lia) ltac:(lia) ltac:(lia)
      HAS MU WM RO2 RW) as BK2.
    assert (ZSb : bytes_at rsegs m2 b (czeros (Z.to_nat (A + n - b)))).
    { eapply bytes_at_transport; [exact ZS' | exact MU |]. unfold czeros. rewrite repeat_length.
      cbn [disjoint_from]. split; [right; lia | exact I]. }
    clear ZS ZS' RW CH MU WM FR BK MU0 WM0 RO.
    step. rewrite HS0. ulit. step. ulit. step.
    assert (SH12 : Z.shiftr (b - A) 12 = (b - A) / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite ?SH12.
    if_cases K; zify_cond K; rewrite ?SH12 in K; rewrite ?unsigned_lit in K by (Z.div_mod_to_equations; lia).
    + apply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 b BK2); [Z.div_mod_to_equations; lia | lia | lia | exact ZSb].
    + apply (big_final _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (b - A) BK2); [lia|].
      replace (A + (b - A)) with b by lia. replace (n - (b - A)) with (A + n - b) by lia. exact ZSb.
Qed.

End W.

Lemma land_ldiff_distr : forall x a b, Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof.
  intros x a b. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
  destruct (Z.testbit x k), (Z.testbit a k), (Z.testbit b k); reflexivity.
Qed.

Lemma land_pgmask : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096. pose proof (Z.div_mod x 4096 ltac:(lia)). lia.
Qed.

(* calloc+0x64 (0x17b34) with s0 = p, s1 = n >= 4096 *)
Lemma run_clear_big : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk blk : list byte) (rao s0o s1o : word) (mn : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  4096 <= mn ->
  rw_cells rsegs m (bv_unsigned s0) [CB (Z.to_nat mn) blk] ->
  RoAdapt.not_ro rsegs (bv_unsigned s0) mn ->
  MemNorm.ro_agree rsegs m ->
  0 < bv_unsigned s0 -> bv_unsigned s0 + mn <= bv_unsigned sp ->
  evt rsegs (memset_post_ro rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               s0 (Z_to_bv 64 0) (Z_to_bv 64 mn) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 mn) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17b34) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk blk rao s0o s1o mn FR Hmn BLK NRO RO HA0 HAS.
  set (A := bv_unsigned s0) in *. assert (HS0 : bv_unsigned s0 = A) by reflexivity. clearbody A.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (stk_of_rw_cells rsegs m A _ BLK) as BK. cbn [cells_size csize] in BK.
  rewrite Nat.add_0_r, Z2Nat.id in BK by lia.
  pose proof (bk_init m (bv_unsigned sp) A mn junk rao s0o s1o FR BK RO) as BKS.
  change (memset_post_ro rao (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
            s0 (Z_to_bv 64 0) (Z_to_bv 64 mn) m)
    with (big_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rao s0o s1o s0 m mn).
  step. ulit. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
  assert (NR : 0 <= mn / 4096 < 2 ^ 52) by (Z.div_mod_to_equations; lia).
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - exfalso. Z.div_mod_to_equations. lia.
  - do 6 step. rewrite ?HS0.
    set (i0 := (A + mn) mod 4096). set (pp0 := A + mn - i0).
    assert (I0 : 0 <= i0 < 4096) by (subst i0; apply Z.mod_pos_bound; lia).
    ulit.
    assert (E2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (A + mn) 52))) 52 = i0).
    { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst i0. Z.div_mod_to_equations. nia. }
    rewrite ?E2.
    rewrite ?land_pgmask by lia. fold i0. fold pp0.
    assert (PP : A + 4096 <= pp0 + 4096 /\ pp0 <= A + mn /\ A <= pp0) by (subst pp0 i0; Z.div_mod_to_equations; lia).
    destruct (blk_chunk m A mn pp0 i0 BK ltac:(lia) ltac:(lia) ltac:(lia)) as [jk CH].
    step.
    eapply evt_cut.
    { eapply memset_ro_holds.
      - ulit. exact CH.
      - ulit. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        apply (nro_sub A mn); [exact NRO | lia | lia].
      - exact RO. }
    intros ms'' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & RO2 & RW).
    ulit_in MU. ulit_in RW. rewrite Z.mod_0_l in RW by lia.
    rewrite (ret_pc_even 0x17b58) by first [lia | reflexivity].
    pose proof (after_ms m m m2 (bv_unsigned sp) A mn junk rao s0o s1o pp0 i0 BKS ltac:(lia) ltac:(lia) ltac:(lia)
      HAS MU WM RO2 RW) as BK2.
    assert (ZSb : bytes_at rsegs m2 pp0 (czeros (Z.to_nat (A + mn - pp0)))).
    { destruct RW as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      replace (A + mn - pp0) with i0 by lia. exact B. }
    clear RW CH MU WM FR BK RO BKS.
    step. rewrite ?HS0. ulit. step. ulit. step.
    assert (SH12 : Z.shiftr (pp0 - A) 12 = (pp0 - A) / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite ?SH12.
    if_cases K2; zify_cond K2; rewrite ?SH12 in K2; rewrite ?unsigned_lit in K2 by (Z.div_mod_to_equations; lia).
    + eapply big_outer with (N := Z.to_nat mn) (m := m2) (q := pp0) (A := A) (n := mn) (junk := junk);
        first [exact HS0 | exact HAS | exact NRO | exact HA0 | exact BK2 | exact ZSb | lia | Z.div_mod_to_equations; lia].
    + step.
      eapply big_final with (m := m2) (k := pp0 - A) (A := A) (n := mn) (junk := junk);
        first [exact HS0 | exact HAS | exact NRO | exact HA0 | exact BK2 | lia | idtac].
      replace (A + (pp0 - A)) with pp0 by lia. replace (mn - (pp0 - A)) with (A + mn - pp0) by lia. exact ZSb.
Qed.
