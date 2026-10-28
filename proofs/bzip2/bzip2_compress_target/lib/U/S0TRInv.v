(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec CatSim StoreOk Frame Hoare ShapeAlg Spec AgentLib RefMemcpyLib U.S0MemcpyBase U.S0Memcpy.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0StdioDefs U.S0ExitBase U.S0Exit U.S0Printf0 U.S0PrintfBufBase U.S0PrintfBuf.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0TRDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface.GlueEqv.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Notation F0 := (bvmap_empty : bvmap 5 word) (only parsing).
Notation FC0 := (Z_to_bv 32 0) (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma MS_mkst : forall R pc m, MS R F0 pc FC0 None m (seg_rom s0segs) = mkst R pc m (seg_rom s0segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  getr R 1 = x1 /\ getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\ getr R 10 = x10
  /\ getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\ getr R 23 = x23
  /\ getr R 24 = x24 /\ getr R 25 = x25 /\ getr R 26 = x26 /\ getr R 27 = x27.
Proof. intros. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma mkR_of_keeps : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 R',
  keeps (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) R' ->
  mkR_of R' = mkR x1 x2 x3 x4 (getr R' 5) (getr R' 6) (getr R' 7) x8 x9 x10 (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14)
                  (getr R' 15) (getr R' 16) (getr R' 17) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31).
Proof.
  intros. unfold mkR_of.
  pose proof (getr_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as G.
  cbv zeta in G. cps_destruct G as (G1&G2&G3&G4&G8&G9&G10&G18&G19&G20&G21&G22&G23&G24&G25&G26&G27).
  rewrite (H 1%bv), (H 2%bv), (H 3%bv), (H 4%bv), (H 8%bv), (H 9%bv), (H 10%bv), (H 18%bv), (H 19%bv), (H 20%bv), (H 21%bv),
          (H 22%bv), (H 23%bv), (H 24%bv), (H 25%bv), (H 26%bv), (H 27%bv) by (cbv; tauto).
  rewrite G1, G2, G3, G4, G8, G9, G10, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mkR_of_keeps_cs : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 R',
  keeps_cs (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) R' ->
  mkR_of R' = mkR x1 x2 x3 x4 (getr R' 5) (getr R' 6) (getr R' 7) x8 x9 (getr R' 10) (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14)
                  (getr R' 15) (getr R' 16) (getr R' 17) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31).
Proof.
  intros. unfold mkR_of.
  pose proof (getr_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as G.
  cbv zeta in G. cps_destruct G as (G1&G2&G3&G4&G8&G9&G10&G18&G19&G20&G21&G22&G23&G24&G25&G26&G27).
  rewrite (H 1%bv), (H 2%bv), (H 3%bv), (H 4%bv), (H 8%bv), (H 9%bv), (H 18%bv), (H 19%bv), (H 20%bv), (H 21%bv),
          (H 22%bv), (H 23%bv), (H 24%bv), (H 25%bv), (H 26%bv), (H 27%bv) by (cbv; tauto).
  rewrite G1, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma memcpy_cps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (MD : Model) (dst src n : Z) (bs junk : list byte) (K : TSet),
    a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 src -> a2 = Z_to_bv 64 n ->
    (exists z, ra = Z_to_bv 64 z /\ 0 <= z < 2 ^ 64 /\ z mod 2 = 0) ->
    rw_cells s0segs m dst [CB (Z.to_nat n) junk] ->
    bytes_at s0segs m src bs -> Z.of_nat (length bs) = n ->
    (src + n <= dst \/ dst + n <= src) -> (dst + n < 2 ^ 64) -> (src + n < 2 ^ 64) ->
    m_halted MD = None -> m_vm_lazy MD = [] ->
    mem_inv s0segs m ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(dst, dst + n)] m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        rw_cells s0segs m' dst [CB (Z.to_nat n) bs] -> bytes_at s0segs m' src bs ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                    F0 (ret_pc ra) FC0 None m' (seg_rom s0segs)) MD) K) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F0 (Z_to_bv 64 0x306ac) FC0 None m (seg_rom s0segs)) MD) K.
Proof.
  intros until K. (intros -> -> ->; cps_intros (z & -> & Hz & Hev); intros DST SRC LEN SEP ND NS Hh Hl MI HK).
  pose proof (rw_cells_bound s0segs m dst _ DST) as B1. cbn [cells_size csize Nat.add] in B1.
  pose proof (bytes_at_bound s0segs m src bs SRC) as B2.
  assert (HOK : mcH m (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs).
  { constructor.
    - lia.
    - lia.
    - pose proof (bytes_at_rdn s0segs m src bs 0 (length bs) SRC ltac:(lia)) as R.
      replace (src + Z.of_nat 0)%Z with src in R by lia. cbn [skipn] in R. rewrite firstn_all in R. unfold wa in R. exact R.
    - destruct DST as [_ W]. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W.
      pose proof (wr_at_store_ok s0segs m dst _ 0 (length bs) W ltac:(lia) ltac:(lia)) as S.
      replace (dst + 0)%Z with dst in S by lia. unfold wa in S. exact S.
    - rewrite !u64_lit by lia. lia.
    - rewrite !u64_lit by lia. lia.
    - rewrite !u64_lit by lia. lia. }
  set (R := mkR (Z_to_bv 64 z) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  cps_destruct (ref_memcpy m (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs (seg_rom s0segs) HOK R (Z_to_bv 64 z))
    as (R' & RUN & KEEP).
  { apply ret_ok_even. rewrite u64_lit by lia. exact Hev. }
  1-4: subst R; reflexivity.
  (* [comment removed for export] *)
  rewrite MS_mkst. replace (Z_to_bv 64 0x306ac) with (0x306ac%bv : word) by (apply bv_eq; reflexivity).
  eapply (rz_msteps s0segs); [exact Hh | exact Hl | exact RUN |].
  apply (realizes_getr_ext s0segs (mkR_of R')); [intros r; apply getr_mkR_of|].
  subst R. rewrite (mkR_of_keeps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R' KEEP). rewrite <- MS_mkst.
  rewrite (ret_pc_even z Hz Hev) in HK.
  rewrite <- write_to_mem_wbytes. change (Z_to_bv 64 dst) with (wa dst).
  eapply HK.
  - (* [comment removed for export] *) apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
  - apply wmono_write. apply wmono_refl.
  - apply mem_inv_store; [exact MI|]. destruct HOK. exact Hdst.
  - (* [comment removed for export] *)
    pose proof (rw_cells_write s0segs m dst [CB (Z.to_nat n) junk] 0 (CB (Z.to_nat n) junk) (CB (Z.to_nat n) bs) DST eq_refl eq_refl) as RW.
    cbn [cbytes cell_upd] in RW. replace (dst + Z.of_nat 0)%Z with dst in RW by lia. apply RW. cbn. lia.
  - (* [comment removed for export] *)
    destruct SEP.
    + apply bytes_at_write_other; [exact SRC| lia | lia | lia].
    + apply bytes_at_write_other; [exact SRC| lia | lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pres (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a : Z, 0 <= a < 2 ^ 64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview s0segs m (wa a) <> None -> wview s0segs m' (wa a) <> None).

Lemma pres_refl : forall P m, pres P m m.
Proof. intros P m a _ _. auto. Qed.

Lemma pres_trans : forall P m1 m2 m3, pres P m1 m2 -> pres P m2 m3 -> pres P m1 m3.
Proof.
  intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2].
  split; [congruence|auto].
Qed.

Lemma pres_mono : forall (P Q : Z -> Prop) m m', (forall a, 0 <= a < 2 ^ 64 -> Q a -> P a) -> pres P m m' -> pres Q m m'.
Proof. intros P Q m m' HPQ H a Ha HQ. apply H; auto. Qed.

Lemma pres_of_heap_pres : forall L LB SP m m', heap_pres s0segs L LB SP m m' -> pres (client_addr L LB SP) m m'.
Proof. intros L LB SP m m' H. exact H. Qed.

Lemma pres_of_munch : forall W m m', munch W m m' -> wmono s0segs m m' -> pres (outside W) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split.
  - apply MU. rewrite wa_unsigned by lia. exact Ho.
  - apply WM.
Qed.

(* [comment removed for export] *)
Fixpoint lit_regions (rs : list (Z * Z)) : list (word * Z) :=
  match rs with [] => [] | (lo, n) :: rs' => (Z_to_bv 64 lo, n) :: lit_regions rs' end.
Fixpoint out_regions (rs : list (Z * Z)) (a : Z) : Prop :=
  match rs with [] => True | (lo, n) :: rs' => ~ (lo <= a < lo + n) /\ out_regions rs' a end.

Lemma outside_lit_regions : forall rs a, 0 <= a < 2 ^ 64 ->
  Forall (fun r => 0 <= fst r < 2 ^ 64) rs ->
  out_regions rs a -> OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame.outside (wa a) (lit_regions rs).
Proof.
  induction rs as [|[lo n] rs IH]; intros a Ha Hrs Ho; cbn in *; [exact I|].
  apply Forall_cons_iff in Hrs as [H1 H2]. cbn in H1. destruct Ho as [Hn Ho]. split.
  - unfold in_rng. rewrite wa_unsigned by lia. rewrite u64_lit by lia. exact Hn.
  - apply IH; assumption.
Qed.

Lemma mem_grows_wmono : forall m m', mem_grows m m' -> wmono s0segs m m'.
Proof.
  intros m m' G x Hx. unfold wview in *.
  destruct (m' x) eqn:E'; [discriminate|].
  destruct (m x) eqn:E; [exfalso; apply (G x); congruence|]. exact Hx.
Qed.

Lemma pres_of_frame_mod : forall rs m m',
  Forall (fun r => 0 <= fst r < 2 ^ 64) rs ->
  frame_mod m m' (lit_regions rs) -> pres (out_regions rs) m m'.
Proof.
  intros rs m m' Hrs [E G] a Ha Ho. split.
  - apply E. apply outside_lit_regions; assumption.
  - apply mem_grows_wmono. exact G.
Qed.

(* [comment removed for export] *)
Lemma pres_bytes_at : forall P m m' A bs,
  pres P m m' -> bytes_at s0segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at s0segs m' A bs.
Proof.
  (intros P m m' A bs HP; cps_intros (H0 & H1 & HB); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma pres_wr_at : forall P m m' A n,
  pres P m m' -> wr_at s0segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at s0segs m' A n.
Proof.
  (intros P m m' A n HP; cps_intros (H0 & H1 & HW); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma pres_rw_cells : forall P m m' A cs,
  pres P m m' -> rw_cells s0segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells s0segs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply pres_wr_at; eauto.
Qed.

Lemma pres_stk : forall P m m' lo hi,
  pres P m m' -> stk s0segs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk s0segs m' lo hi.
Proof.
  intros P m m' lo hi HP ST HS. cps_destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HS; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma pres_img_pristine : forall P m m' lo hi,
  pres P m m' -> img_pristine m lo hi -> (forall a, lo <= a < hi -> P a) -> 0 <= lo -> hi <= 2 ^ 64 ->
  img_pristine m' lo hi.
Proof.
  intros P m m' lo hi HP H HS Hlo Hhi a Ha. destruct (HP a ltac:(lia) ltac:(apply HS; lia)) as [E _].
  rewrite E. apply H. exact Ha.
Qed.

Lemma pres_rdn : forall P m m' (a : Z) n,
  pres P m m' -> (forall x, a <= x < a + Z.of_nat n -> P x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn s0segs m' (wa a) n = rdn s0segs m (wa a) n.
Proof.
  intros P m m' a n HP HS Ha Hn. destruct n as [|n']; [reflexivity|].
  unfold wa. apply rdn_ext; rewrite u64_lit by lia; [lia|].
  intros x Hx.
  pose proof (bv_unsigned_in_range 64 x).
  destruct (HP (bv_unsigned x) ltac:(lia) ltac:(apply HS; lia)) as [E _].
  unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_pristine : forall m A (n : nat) bs,
  img_pristine m A (A + Z.of_nat n) -> image_bytes s0segs A n = Some bs ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  rdn s0segs m (Z_to_bv 64 A) n = Some bs.
Proof.
  intros m A n bs HP HI HA HN.
  pose proof (bytes_at_pristine m A n bs HP HI HA HN) as B.
  pose proof (image_bytes_length s0segs n A bs HI) as L.
  pose proof (bytes_at_rdn s0segs m A bs 0 n B ltac:(lia)) as R.
  replace (A + Z.of_nat 0)%Z with A in R by lia. subst n. unfold skipn in R. rewrite firstn_all in R. exact R.
Qed.

Lemma rdn_of_rw_C8 : forall m a v, rw_cells s0segs m a [C8 v] -> rdn s0segs m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).
Proof.
  intros m a v [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
  pose proof (bytes_at_rdn s0segs m a (le8 v) 0 8 B ltac:(rewrite length_le8; lia)) as R.
  replace (a + Z.of_nat 0)%Z with a in R by lia. exact R.
Qed.

Lemma rdn_of_rw_C4 : forall m a v, rw_cells s0segs m a [C4 v] -> rdn s0segs m (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 v).
Proof.
  intros m a v [[_ B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
  pose proof (bytes_at_rdn s0segs m a (le4 v) 0 4 B ltac:(rewrite length_le4; lia)) as R.
  replace (a + Z.of_nat 0)%Z with a in R by lia. exact R.
Qed.

Lemma rdn_of_bytes_at : forall m a bs, bytes_at s0segs m a bs -> rdn s0segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs B. pose proof (bytes_at_rdn s0segs m a bs 0 (length bs) B ltac:(lia)) as R.
  replace (a + Z.of_nat 0)%Z with a in R by lia. unfold skipn in R. rewrite firstn_all in R. exact R.
Qed.

Lemma store_ok_of_stk : forall m lo hi A (n : nat),
  stk s0segs m lo hi -> lo <= A -> A + Z.of_nat n <= hi -> store_ok s0segs m (Z_to_bv 64 A) n = true.
Proof.
  intros m lo hi A n ST H1 H2.
  pose proof (wr_at_of_stk m lo hi A (Z.of_nat n) ST H1 H2 ltac:(lia)) as W.
  pose proof (wr_at_store_ok s0segs m A (Z.of_nat n) 0 n W ltac:(lia) ltac:(lia)) as S.
  replace (A + 0)%Z with A in S by lia. exact S.
Qed.

(* [comment removed for export] *)
Lemma find_segment_ro0 : forall a, (0x10000 <= a < 0x13000)%Z -> find_segment s0segs a 1 = Some Ubsan_segment_000.
Proof.
  intros a H. unfold s0segs, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  cbn [find_segment seg_base seg_size Ubsan_segment_000].
  change (Z.of_N 65536) with 65536%Z. change (Z.of_N 12288) with 12288%Z.
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + 1) (65536 + 12288)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma find_segment_ro1 : forall a, (0x13000 <= a < 0x32000)%Z -> find_segment s0segs a 1 = Some Ubsan_segment_001.
Proof.
  intros a H. unfold s0segs, Ubsan.M.loaded_segments, Ubsan_loaded_segments.
  rewrite 1 find_segment_skip; try (cbn; lia).
  cbn [find_segment seg_base seg_size Ubsan_segment_001].
  change (Z.of_N 77824) with 77824%Z. change (Z.of_N 126976) with 126976%Z.
  destruct (Z.leb_spec 77824 a); destruct (Z.leb_spec (a + 1) (77824 + 126976)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma mem_inv_pristine_ro : forall m, mem_inv s0segs m -> img_pristine m 0x10000 0x32000.
Proof.
  intros m MI a Ha. destruct (m (wa a)) as [b|] eqn:E; [|reflexivity].
  exfalso. pose proof (MI _ _ E) as R. unfold ro_addr in R. rewrite wa_unsigned in R by lia.
  destruct (Z.lt_ge_cases a 0x13000).
  - rewrite find_segment_ro0 in R by lia. cbn in R. discriminate.
  - rewrite find_segment_ro1 in R by lia. cbn in R. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
End ACeilS1.


(* [comment removed for export] *)
Ltac solve_img :=
  lazymatch goal with |- image_bytes ?sg ?A ?n = Some ?e =>
    let v := eval vm_compute in (image_bytes sg A n) in
    lazymatch v with Some ?l => unify e l; vm_compute; reflexivity end end.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma rdn_pristine_eq : forall m A (n : nat) bs bs',
  img_pristine m A (A + Z.of_nat n) -> image_bytes s0segs A n = Some bs' -> map bv_unsigned bs' = map bv_unsigned bs ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  rdn s0segs m (Z_to_bv 64 A) n = Some bs.
Proof.
  intros m A n bs bs' HP HI HE HA HN. rewrite <- (bytes_eq_of_unsigned _ _ HE). eapply rdn_pristine; eauto.
Qed.

Lemma rw_cells_pristine_eq : forall m A (n : nat) bs bs',
  img_pristine m A (A + Z.of_nat n) -> (0x32000 <= A)%Z -> (A + Z.of_nat n <= 0x66000)%Z ->
  image_bytes s0segs A n = Some bs' -> map bv_unsigned bs' = map bv_unsigned bs ->
  rw_cells s0segs m A [CB n bs].
Proof.
  intros m A n bs bs' HP H1 H2 HI HE. rewrite <- (bytes_eq_of_unsigned _ _ HE). eapply rw_cells_pristine; eauto.
Qed.

(* [comment removed for export] *)
Lemma rw_C8_pristine : forall m A v bs',
  img_pristine m A (A + 8) -> (0x32000 <= A)%Z -> (A + 8 <= 0x66000)%Z ->
  image_bytes s0segs A 8 = Some bs' -> map bv_unsigned bs' = map bv_unsigned (le8 (Z_to_bv 64 v)) ->
  rw_cells s0segs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v bs' HP H1 H2 HI HE.
  pose proof (rw_cells_pristine_eq m A 8 (le8 (Z_to_bv 64 v)) bs' HP H1 H2 HI HE) as [[_ B] W].
  split; [split; [exact (conj I I)|]|]; cbn [cells_bytes cbytes cells_size csize app Nat.add] in *; assumption.
Qed.
Lemma rw_C4_pristine : forall m A v bs',
  img_pristine m A (A + 4) -> (0x32000 <= A)%Z -> (A + 4 <= 0x66000)%Z ->
  image_bytes s0segs A 4 = Some bs' -> map bv_unsigned bs' = map bv_unsigned (le4 (Z_to_bv 64 v)) ->
  rw_cells s0segs m A [C4 (Z_to_bv 64 v)].
Proof.
  intros m A v bs' HP H1 H2 HI HE.
  pose proof (rw_cells_pristine_eq m A 4 (le4 (Z_to_bv 64 v)) bs' HP H1 H2 HI HE) as [[_ B] W].
  split; [split; [exact (conj I I)|]|]; cbn [cells_bytes cbytes cells_size csize app Nat.add] in *; assumption.
Qed.
Lemma rw_C1_pristine : forall m A v bs',
  img_pristine m A (A + 1) -> (0x32000 <= A)%Z -> (A + 1 <= 0x66000)%Z ->
  image_bytes s0segs A 1 = Some bs' -> map bv_unsigned bs' = [v mod 256]%Z ->
  rw_cells s0segs m A [C1 (Z_to_bv 8 v)].
Proof.
  intros m A v bs' HP H1 H2 HI HE.
  assert (HE' : map bv_unsigned bs' = map bv_unsigned [Z_to_bv 8 v]).
  { rewrite HE. cbn. rewrite Z_to_bv_unsigned. reflexivity. }
  pose proof (rw_cells_pristine_eq m A 1 [Z_to_bv 8 v] bs' HP H1 H2 HI HE') as [[_ B] W].
  split; [split; [exact (conj I I)|]|]; cbn [cells_bytes cbytes cells_size csize app Nat.add] in *; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition S_IVS : list (Z * Z) :=
  [(0x32000, 0x33f90); (0x34078, 0x34090); (0x34091, 0x340d9); (0x440d9, 0x440e0); (0x440e1, 0x44110);
   (0x441f8, 0x641e8); (0x64220, 0x64450); (0x64471, 0x64478)]%Z.
(* [comment removed for export] *)
Definition OFL : Z := 0x64890.

Fixpoint in_ivs (l : list (Z * Z)) (a : Z) : Prop :=
  match l with [] => False | (lo, hi) :: l' => (lo <= a < hi)%Z \/ in_ivs l' a end.

Definition pristine_on (l : list (Z * Z)) (m : word -> option byte) : Prop :=
  forall a, in_ivs l a -> m (wa a) = None.

Record statics (sp0 tid : Z) (m : word -> option byte) : Prop := STATICS {
  st_img : pristine_on S_IVS m;
  st_tid : rw_cells s0segs m 0x44138 [C4 (Z_to_bv 64 tid)];
  st_can : exists gw : word, rw_cells s0segs m 0x64450 [C8 gw];   (* [comment removed for export] *)
  st_ofl : rw_cells s0segs m OFL [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)];
  st_mf  : exists junk8 : list byte,                                (* [comment removed for export] *)
           rw_cells s0segs m (sp0 - 128)
             [CB 8 junk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sp0 + 32));
              C8 (Z_to_bv 64 0x13580); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (sp0 + 8)); C8 (Z_to_bv 64 0x28c48)]
}.

Definition statics_addr (sp0 a : Z) : Prop :=
  in_ivs S_IVS a \/ (0x44138 <= a < 0x4413c)%Z \/ (0x64450 <= a < 0x64458)%Z \/ (OFL <= a < OFL + 16)%Z \/ (sp0 - 128 <= a < sp0 - 48)%Z.

Lemma statics_pres : forall P sp0 tid m m',
  pres P m m' -> (forall a, statics_addr sp0 a -> P a) -> (0x7fff80000000 <= sp0 <= 0x800000000000)%Z ->
  statics sp0 tid m -> statics sp0 tid m'.
Proof.
  intros P sp0 tid m m' HP HS Hsp [I T C O F]. constructor.
  - intros a Ha. assert (R : (0 <= a < 2 ^ 64)%Z) by (cbn in Ha; lia).
    destruct (HP a R ltac:(apply HS; left; exact Ha)) as [E _]. rewrite E. apply I. exact Ha.
  - eapply pres_rw_cells; [exact HP | exact T |]. cbn. intros a Ha. apply HS. right; left. lia.
  - destruct C as [gw C]. exists gw. eapply pres_rw_cells; [exact HP | exact C |]. cbn. intros a Ha. apply HS. right; right; left. lia.
  - eapply pres_rw_cells; [exact HP | exact O |]. unfold OFL. cbn. intros a Ha. apply HS. right; right; right; left. unfold OFL. lia.
  - destruct F as [junk8 F]. exists junk8. eapply pres_rw_cells; [exact HP | exact F |]. cbn. intros a Ha. apply HS. right; right; right; right. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma statics_client : forall sp0 LB SP a, (SP <= sp0 - 128)%Z -> statics_addr sp0 a -> client_addr S0_layout LB SP a.
Proof.
  intros sp0 LB SP a HSP Ha. unfold client_addr, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp].
  unfold statics_addr, OFL in Ha. cbn [in_ivs S_IVS] in Ha. lia.
Qed.

Definition S_IVS1 : list (Z * Z) :=
  [(0x32000, 0x33f90); (0x34078, 0x34090); (0x34091, 0x340d9); (0x440d9, 0x440e0); (0x440e1, 0x440e4); (0x440e5, 0x44110);
   (0x441f8, 0x641e8); (0x64220, 0x64230); (0x64234, 0x64238); (0x64240, 0x64248); (0x64250, 0x64348); (0x64350, 0x64450);
   (0x64471, 0x64478)]%Z.

Definition ax_cells (m : word -> option byte) : Prop :=
  rw_cells s0segs m 0x64230 [C4 (Z_to_bv 64 1)] /\ rw_cells s0segs m 0x64238 [C8 (Z_to_bv 64 0x64240)]
  /\ rw_cells s0segs m 0x64248 [C8 (Z_to_bv 64 0x2916c)] /\ rw_cells s0segs m 0x64348 [C8 (Z_to_bv 64 0x139a8)].

Definition ax_addr (a : Z) : Prop :=
  (0x64230 <= a < 0x64234 \/ 0x64238 <= a < 0x64240 \/ 0x64248 <= a < 0x64250 \/ 0x64348 <= a < 0x64350)%Z.

Record statics1 (sp0 tid : Z) (m : word -> option byte) : Prop := STATICS1 {
  s1_img : pristine_on S_IVS1 m;
  s1_tid : rw_cells s0segs m 0x44138 [C4 (Z_to_bv 64 tid)];
  s1_can : exists gw : word, rw_cells s0segs m 0x64450 [C8 gw];
  s1_ofl : rw_cells s0segs m OFL [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)];
  s1_mf  : exists junk8 : list byte,
           rw_cells s0segs m (sp0 - 128)
             [CB 8 junk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sp0 + 32));
              C8 (Z_to_bv 64 0x13580); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (sp0 + 8)); C8 (Z_to_bv 64 0x28c48)];
  s1_ax  : ax_cells m
}.

Definition core1_addr (sp0 a : Z) : Prop :=
  in_ivs S_IVS1 a \/ (0x44138 <= a < 0x4413c)%Z \/ (0x64450 <= a < 0x64458)%Z \/ (OFL <= a < OFL + 16)%Z \/ (sp0 - 128 <= a < sp0 - 48)%Z.

Definition statics1_addr (sp0 a : Z) : Prop := core1_addr sp0 a \/ ax_addr a.

Lemma ax_cells_pres : forall P m m', pres P m m' -> (forall a, ax_addr a -> P a) -> ax_cells m -> ax_cells m'.
Proof.
  (intros P m m' HP HS; cps_intros (A1 & A2 & A3 & A4)). unfold ax_cells, ax_addr in *.
  repeat split; (eapply pres_rw_cells; [exact HP | eassumption | cbn; intros a Ha; apply HS; lia]).
Qed.

Lemma statics1_of : forall P sp0 tid m m',
  pres P m m' -> (forall a, core1_addr sp0 a -> P a) -> (0x7fff80000000 <= sp0 <= 0x800000000000)%Z ->
  statics sp0 tid m -> ax_cells m' -> statics1 sp0 tid m'.
Proof.
  intros P sp0 tid m m' HP HS Hsp [I T C O F] AX. constructor.
  - intros a Ha. assert (R : (0 <= a < 2 ^ 64)%Z) by (cbn in Ha; lia).
    destruct (HP a R ltac:(apply HS; left; exact Ha)) as [E _]. rewrite E. apply I. cbn in Ha |- *. lia.
  - eapply pres_rw_cells; [exact HP | exact T |]. cbn. intros a Ha. apply HS. right; left. lia.
  - destruct C as [gw C]. exists gw. eapply pres_rw_cells; [exact HP | exact C |]. cbn. intros a Ha. apply HS. right; right; left. lia.
  - eapply pres_rw_cells; [exact HP | exact O |]. unfold OFL. cbn. intros a Ha. apply HS. right; right; right; left. unfold OFL. lia.
  - destruct F as [junk8 F]. exists junk8. eapply pres_rw_cells; [exact HP | exact F |]. cbn. intros a Ha. apply HS. right; right; right; right. lia.
  - exact AX.
Qed.

Lemma statics1_pres : forall P sp0 tid m m',
  pres P m m' -> (forall a, statics1_addr sp0 a -> P a) -> (0x7fff80000000 <= sp0 <= 0x800000000000)%Z ->
  statics1 sp0 tid m -> statics1 sp0 tid m'.
Proof.
  intros P sp0 tid m m' HP HS Hsp [I T C O F X]. constructor.
  - intros a Ha. assert (R : (0 <= a < 2 ^ 64)%Z) by (cbn in Ha; lia).
    destruct (HP a R ltac:(apply HS; left; left; exact Ha)) as [E _]. rewrite E. apply I. exact Ha.
  - eapply pres_rw_cells; [exact HP | exact T |]. cbn. intros a Ha. apply HS. left; right; left. lia.
  - destruct C as [gw C]. exists gw. eapply pres_rw_cells; [exact HP | exact C |]. cbn. intros a Ha. apply HS. left; right; right; left. lia.
  - eapply pres_rw_cells; [exact HP | exact O |]. unfold OFL. cbn. intros a Ha. apply HS. left; right; right; right; left. unfold OFL. lia.
  - destruct F as [junk8 F]. exists junk8. eapply pres_rw_cells; [exact HP | exact F |]. cbn. intros a Ha. apply HS. left; right; right; right; right. lia.
  - eapply ax_cells_pres; [exact HP | | exact X]. intros a Ha. apply HS. right. exact Ha.
Qed.

Lemma statics1_client : forall sp0 LB SP a, (SP <= sp0 - 128)%Z -> statics1_addr sp0 a -> client_addr S0_layout LB SP a.
Proof.
  intros sp0 LB SP a HSP Ha. unfold client_addr, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp].
  unfold statics1_addr, core1_addr, ax_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SO_FILE : Z := 0x33f90.
Definition SO_BUF : Z := 0x64cb8.

(* [comment removed for export] *)
Definition stdout_untouched (m : word -> option byte) : Prop := img_pristine m SO_FILE (SO_FILE + 232).

(* [comment removed for export] *)
Definition stdout_used (m : word -> option byte) (pending : list byte) : Prop :=
  stdout_wmode PF0_S0 m (SO_BUF + Z.of_nat (length pending))
  /\ bytes_at s0segs m SO_BUF pending /\ (Z.of_nat (length pending) <= 1022)%Z.

Definition stdout_addr (a : Z) : Prop := (SO_FILE <= a < SO_FILE + 232)%Z \/ (SO_BUF <= a < SO_BUF + 1024)%Z.

Lemma stdout_untouched_pres : forall P m m',
  pres P m m' -> (forall a, stdout_addr a -> P a) -> stdout_untouched m -> stdout_untouched m'.
Proof.
  intros P m m' HP HS H. unfold stdout_untouched, SO_FILE in *.
  eapply pres_img_pristine; [exact HP | exact H | | lia | lia].
  intros a Ha. apply HS. left. unfold SO_FILE. exact Ha.
Qed.

Lemma cellZ_pres : forall P m m' a n v,
  pres P m m' -> (forall x, a <= x < a + Z.of_nat n -> P x)%Z -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  cellZ PF0_S0 m a n v -> cellZ PF0_S0 m' a n v.
Proof.
  intros P m m' a n v HP HS Ha Hn H. unfold cellZ in *. rewrite <- H.
  change (Z_to_bv 64 a) with (wa a). apply (pres_rdn P); assumption.
Qed.

Lemma stdout_used_pres : forall P m m' pending,
  pres P m m' -> (forall a, stdout_addr a -> P a) -> stdout_used m pending -> stdout_used m' pending.
Proof.
  (intros P m m' pending HP HS; cps_intros (WM & B & L)). unfold stdout_addr, SO_FILE, SO_BUF in *.
  split; [|split; [|exact L]].
  - destruct WM; constructor; cbn [pf_file pf_buf pf_swrite PF0_S0] in *;
      (eapply cellZ_pres; [exact HP | | | | eassumption]).
    all: try lia.
    all: intros x Hx; apply HS; lia.
  - eapply pres_bytes_at; [exact HP | exact B |]. intros x Hx; apply HS. unfold SO_BUF in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma and_255_small : forall v, 0 <= v < 256 -> bv_and (Z_to_bv 64 v) (Z_to_bv 64 255) = Z_to_bv 64 v.
Proof.
  intros v Hv. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
End ACeilS2.


(* [comment removed for export] *)
Ltac img_rdn HP :=
  eapply rdn_pristine_eq;
  [ intros ? ?; apply HP; cbn [in_ivs S_IVS]; lia
  | solve_img
  | vm_compute; reflexivity
  | lia | lia ].
Ltac img_rdn1 HP :=
  eapply rdn_pristine_eq;
  [ intros ? ?; apply HP; cbn [in_ivs S_IVS1]; lia
  | solve_img
  | vm_compute; reflexivity
  | lia | lia ].
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma rw_cells_split : forall m A cs1 cs2,
  rw_cells s0segs m A (cs1 ++ cs2) -> rw_cells s0segs m A cs1 /\ rw_cells s0segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[WF BA] WR].
  apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in BA. apply (proj1 (bytes_at_app _ _ _ _ _)) in BA. destruct BA as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in WR. cps_destruct WR as (A1 & A2 & WW).
  split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply WW. lia.
  - replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply WW. lia.
Qed.

Lemma exit_cps :
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (MD : Model) (sp0 tid lo v : Z) (pending : list byte),
    0x7fff80000000 <= sp0 <= 0x800000000000 ->
    stk s0segs m lo (sp0 - 48) -> lo <= sp0 - 48 - 144 ->
    statics1 sp0 tid m -> rw_cells s0segs m 0x440e4 [C1 (Z_to_bv 8 0)] -> 0 < tid < 2 ^ 22 -> mem_inv s0segs m ->
    m_halted MD = None -> m_vm_lazy MD = [] ->
    0 <= v < 256 ->
    ( (stdout_untouched m /\ pending = [])
      \/ (stdout_used m pending /\ fd_lookup (m_fds MD) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ) ->
    realizes s0segs
      (mkCfg (MS (mkR ra (Z_to_bv 64 (sp0 - 48)) gp (Z_to_bv 64 0x441e0) t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F0 (Z_to_bv 64 0x291c0) FC0 None m (seg_rom s0segs)) MD)
      (t_emit (W 1 pending) (t_exit (exit_code v) (m_fs MD))).
Proof.
  intros until pending. intros Hsp ST LO STAT CB TID MI Hh Hl Hv SO.
  rewrite MS_mkst. replace (exit_code v) with (bv_and (Z_to_bv 64 v) (Z_to_bv 64 255)) by (apply and_255_small; exact Hv).
  apply ref_exit_Z.
  pose proof (s1_img _ _ _ STAT) as HP. destruct (s1_can _ _ _ STAT) as [gw Hgw].
  exists (Z_to_bv 64 (sp0 - 48)), (Z_to_bv 64 0x441e0), tid, (Z_to_bv 64 0), (Z_to_bv 64 0).
  split; [|split; [exact Hh|split; [exact Hl|]]].
  - constructor; try reflexivity; rewrite ?u64_lit by lia; try lia.
    + (* [comment removed for export] *) apply (store_ok_of_stk m lo (sp0 - 48)); [exact ST| lia | lia].
    + (* [comment removed for export] *) replace (279008 - 168)%Z with 0x44138%Z by reflexivity. apply rdn_of_rw_C4. exact (s1_tid _ _ _ STAT).
    + img_rdn1 HP.
    + img_rdn1 HP.
    + img_rdn1 HP.
    + img_rdn1 HP.
    + img_rdn1 HP.
    + img_rdn1 HP.
    + img_rdn1 HP.
    + (* [comment removed for export] *)
      pose proof (s1_ofl _ _ _ STAT) as OF.
      destruct (rw_cells_split m OFL [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 0)] OF) as [_ OF8].
      cbn [cells_size csize Nat.add] in OF8. unfold OFL in OF8. replace (411792 + Z.of_nat 8)%Z with 0x64898%Z in OF8 by reflexivity.
      repeat split; first [img_rdn1 HP | apply rdn_of_rw_C8; exact OF8].
    + (* [comment removed for export] *) repeat split; img_rdn1 HP.
    + img_rdn1 HP.
    + right. destruct (s1_ax _ _ _ STAT) as (A1 & A2 & A3 & A4).
      split; [img_rdn1 HP|]. split; [apply rdn_of_rw_C4; exact A1|]. split; [apply rdn_of_rw_C8; exact A2|].
      split; [img_rdn1 HP|]. split; [apply rdn_of_rw_C8; exact A3|]. split; [apply rdn_of_rw_C8; exact A4|].
      destruct CB as [[_ CBB] _]. cbn [cells_bytes cbytes app] in CBB. exact (rdn_of_bytes_at m 0x440e4 _ CBB).
  - destruct SO as [[SU ->] | [(WM & B & L) FD]].
    + left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0).
      repeat split; (eapply rdn_pristine_eq; [ intros ? ?; apply SU; unfold SO_FILE; lia | solve_img | vm_compute; reflexivity | lia | lia ]).
    + destruct pending as [|p0 pending'].
      * left. split; [reflexivity|]. exists (Z_to_bv 64 SO_BUF), (Z_to_bv 64 0).
        destruct WM; cbn [pf_file pf_buf pf_swrite PF0_S0 length Z.of_nat Z.add] in *.
        repeat split; unfold cellZ, SO_BUF in *; try assumption.
      * right. exists SO_BUF, (SO_BUF + Z.of_nat (length (p0 :: pending'))), (Z_to_bv 64 SO_BUF), (Z_to_bv 64 1024), (Z_to_bv 64 0), gw.
        split; [|exact FD].
        destruct WM; cbn [pf_file pf_buf pf_swrite PF0_S0] in *; unfold cellZ, SO_BUF, BUF_SIZE in *.
        constructor; try assumption.
        -- cbn [length] in *. lia.
        -- lia.
        -- unfold Uaccess.rw_bytes_max. lia.
        -- apply rdn_of_bytes_at. exact B.
        -- split; [img_rdn1 HP|]. apply rdn_of_rw_C8. exact Hgw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ivs_of_regions (rs : list (Z * Z)) : list ivl :=
  match rs with [] => [] | (lo, n) :: rs' => (lo, lo + n)%Z :: ivs_of_regions rs' end.

Lemma outside_regions_lit : forall rs (x : word),
  Forall (fun r => 0 <= fst r < 2 ^ 64) rs ->
  outside (ivs_of_regions rs) (bv_unsigned x) -> OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame.outside x (lit_regions rs).
Proof.
  induction rs as [|[lo n] rs IH]; intros x Hrs Ho; cbn in *; [exact I|].
  apply Forall_cons_iff in Hrs as [H1 H2]. cbn in H1. destruct Ho as [Hn Ho]. split.
  - unfold in_rng. rewrite u64_lit by lia. exact Hn.
  - apply IH; assumption.
Qed.

Lemma munch_of_frame_mod : forall rs m m',
  Forall (fun r => 0 <= fst r < 2 ^ 64) rs -> frame_mod m m' (lit_regions rs) -> munch (ivs_of_regions rs) m m'.
Proof. intros rs m m' Hrs [E G] x Hx. apply E. apply outside_regions_lit; assumption. Qed.

Lemma wmono_of_frame_mod : forall rs m m', frame_mod m m' rs -> wmono s0segs m m'.
Proof. intros rs m m' [_ G]. apply mem_grows_wmono. exact G. Qed.

(* [comment removed for export] *)
Lemma stk_grows : forall m m' lo hi, stk s0segs m lo hi -> mem_grows m m' -> (0x66000 <= lo)%Z -> stk s0segs m' lo hi.
Proof.
  (intros m m' lo hi; cps_intros (H0 & H1 & H); intros G Hlo). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [W _].
  assert (OFF : off_image (bv_unsigned (wa a))) by (unfold off_image; rewrite wa_unsigned by lia; lia).
  rewrite wview_off in W by exact OFF. pose proof (G _ W) as W'.
  unfold mrd. rewrite wview_off by exact OFF. split; [exact W'|].
  destruct (m' (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply W'; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ro_addr_range : forall x : word, ro_addr s0segs x = true -> (0x10000 <= bv_unsigned x < 0x32000)%Z.
Proof.
  intros x H. unfold ro_addr in H. pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x10000).
  { rewrite find_segment_off in H; [discriminate| lia | lia]. }
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x32000); [lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x33000).
  { rewrite find_segment_rw2 in H by lia. cbn in H. discriminate. }
  destruct (Z.lt_ge_cases (bv_unsigned x) 0x66000).
  { rewrite find_segment_rw3 in H by lia. cbn in H. discriminate. }
  rewrite find_segment_off in H; [discriminate | lia | lia].
Qed.

Lemma outside_of_lt : forall W u, Forall (fun iv : ivl => 0x32000 <= fst iv) W -> (u < 0x32000)%Z -> outside W u.
Proof.
  induction W as [|[lo hi] W IH]; intros u HW Hu; cbn; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn in H1. split; [lia|]. apply IH; assumption.
Qed.

Lemma mem_inv_munch : forall W m m',
  munch W m m' -> Forall (fun iv : ivl => 0x32000 <= fst iv) W -> mem_inv s0segs m -> mem_inv s0segs m'.
Proof.
  intros W m m' MU HW MI x b Hx. destruct (ro_addr s0segs x) eqn:E; [|reflexivity]. exfalso.
  pose proof (ro_addr_range x E) as R.
  rewrite (MU x) in Hx by (apply outside_of_lt; [exact HW|lia]).
  rewrite (MI x b Hx) in E. discriminate.
Qed.

(* [comment removed for export] *)
Lemma stk_ok_of_stk : forall m lo (sp : word) K,
  stk s0segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - K)%Z -> SymRun.stk_ok s0segs m sp K.
Proof.
  intros m lo sp K ST HK a n H1 H2.
  rewrite <- (Z_to_bv_bv_unsigned a). apply (store_ok_of_stk m lo (bv_unsigned sp)); [exact ST | lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZL : list byte := [Z_to_bv 8 0x30; Z_to_bv 8 0x0a].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pf0_W (spv : Z) : list ivl := [(spv - 1200, spv); (SO_FILE, SO_FILE + 232); (SO_BUF, SO_BUF + 1024)]%Z.
(* [comment removed for export] *)
Definition pfN_W (spv w : Z) : list ivl := [(spv - 1056, spv); (SO_FILE, SO_FILE + 4); (SO_FILE + 40, SO_FILE + 48); (w, w + 2)]%Z.

Section Printf.
  Hypothesis PF0 : printf0_first_stmt PF0_S0.

  Lemma printf0_cps :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : word -> option byte) (MD : Model) (sp0 tid lo : Z) (K : TSet),
      let spv := bv_unsigned sp in
      spv mod 16 = 0 -> 0x7fff80000000 <= sp0 <= 0x800000000000 -> spv <= sp0 - 128 ->
      stk s0segs m lo spv -> lo <= spv - 1200 -> 0x7fff7f000000 <= lo ->
      mem_inv s0segs m -> statics1 sp0 tid m -> stdout_untouched m ->
      fd_lookup (m_fds MD) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
      m_halted MD = None -> m_vm_lazy MD = [] ->
      K [] ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
          munch (pf0_W spv) m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
          stk s0segs m' lo spv -> statics1 sp0 tid m' -> stdout_used m' [] ->
          realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                      F0 (Z_to_bv 64 0x1392c) FC0 None m' (seg_rom s0segs)) MD) K) ->
      realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F0 (Z_to_bv 64 0x139d8) FC0 None m (seg_rom s0segs)) MD)
               (t_emit (W 1 ZL) K).
  Proof.
    intros until K. intros spv SP16 SP0 SPV ST LO LOLO MI STAT SU FD Hh Hl K0 HK.
    pose proof (s1_img _ _ _ STAT) as HP. destruct (s1_can _ _ _ STAT) as [gw Hgw].
    rewrite MS_mkst.
    eapply (PF0 _ m MD sp (bv_unsigned gw) K); try reflexivity; cbn [pf_ret pf_file pf_buf pf_canary pf_ro_hi pf_segs PF0_S0].
    - exact SP16.
    - unfold PF0_FR. subst spv. lia.
    - subst spv. lia.
    - unfold PF0_FR. apply (store_ok_of_stk m lo spv); [exact ST | lia | subst spv; lia].
    - intros i Hi. destruct (Z.lt_ge_cases i 0x32000).
      + apply (mem_inv_pristine_ro m MI). lia.
      + apply HP. cbn. lia.
    - intros i Hi. apply SU. unfold SO_FILE, FILE_SIZE in *. lia.
    - unfold cellZ. apply rdn_of_rw_C8. rewrite Z_to_bv_bv_unsigned. exact Hgw.
    - apply u64_range.
    - exact FD.
    - exact Hh.
    - exact Hl.
    - exact K0.
    - intros regs' m' KEEP FM WM.
      apply (realizes_getr_ext s0segs (mkR_of regs')); [intros r; apply getr_mkR_of|].
      rewrite (mkR_of_keeps_cs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' KEEP). rewrite <- MS_mkst.
      assert (FM' : frame_mod m m' (lit_regions [(spv - 1200, 1200); (SO_FILE, 232); (SO_BUF, 1024)]%Z)) by exact FM.
      assert (MU : munch (pf0_W spv) m m').
      { replace (pf0_W spv) with (ivs_of_regions [(spv - 1200, 1200); (SO_FILE, 232); (SO_BUF, 1024)]%Z)
          by (cbn; unfold pf0_W; repeat f_equal; lia).
        apply (munch_of_frame_mod [(spv - 1200, 1200); (SO_FILE, 232); (SO_BUF, 1024)]%Z m m'); [|exact FM'].
        repeat constructor; cbn; unfold SO_FILE, SO_BUF; subst spv; lia. }
      pose proof (wmono_of_frame_mod _ _ _ FM') as WMO.
      apply HK.
      + exact MU.
      + exact WMO.
      + eapply mem_inv_munch; [exact MU | | exact MI]. repeat constructor; cbn; unfold SO_FILE, SO_BUF; subst spv; lia.
      + eapply stk_grows; [exact ST | exact (proj2 FM') | lia].
      + eapply statics1_pres; [apply pres_of_munch; [exact MU|exact WMO] | | exact SP0 | exact STAT].
        intros a Ha. unfold statics1_addr, core1_addr, ax_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. cbn. unfold SO_FILE, SO_BUF. subst spv. lia.
      + split; [|split].
        * unfold SO_BUF. rewrite Z.add_0_r. exact WM.
        * apply bytes_at_nil. unfold SO_BUF. lia.
        * cbn. lia.
  Qed.
End Printf.

Lemma printfN_cps :
  forall (sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : word -> option byte) (MD : Model) (sp0 tid lo : Z) (pending : list byte) (K : TSet),
    let spv := bv_unsigned sp in
    spv mod 16 = 0 -> 0x7fff80000000 <= sp0 <= 0x800000000000 -> spv <= sp0 - 128 ->
    stk s0segs m lo spv -> lo <= spv - 1056 -> 0x7fff7f000000 <= lo ->
    mem_inv s0segs m -> statics1 sp0 tid m -> stdout_used m pending -> Z.of_nat (length pending) <= 1020 ->
    m_halted MD = None -> m_vm_lazy MD = [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch (pfN_W spv (SO_BUF + Z.of_nat (length pending))) m m' -> wmono s0segs m m' -> mem_inv s0segs m' ->
        stk s0segs m' lo spv -> statics1 sp0 tid m' -> stdout_used m' (pending ++ ZL) ->
        realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                    F0 (Z_to_bv 64 0x1392c) FC0 None m' (seg_rom s0segs)) MD) K) ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F0 (Z_to_bv 64 0x139d8) FC0 None m (seg_rom s0segs)) MD) K.
Proof.
  intros until K. (intros spv SP16 SP0 SPV ST LO LOLO MI STAT; cps_intros (WMD & B & L); intros LEN Hh Hl HK).
  pose proof (s1_img _ _ _ STAT) as HP. destruct (s1_can _ _ _ STAT) as [gw Hgw].
  set (w := (SO_BUF + Z.of_nat (length pending))%Z) in *.
  set (R := mkR (Z_to_bv 64 0x1392c) sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  assert (PH : pfH m sp w (bv_unsigned gw)).
  { destruct WMD; cbn [pf_file pf_buf pf_swrite PF0_S0] in *; unfold cellZ in *.
    constructor; try assumption.
    - subst spv. lia.
    - subst spv. lia.
    - eapply stk_ok_of_stk; [exact ST | unfold PF_FR; lia].
    - intros i Hi. destruct (Z.lt_ge_cases i 0x32000).
      + apply (mem_inv_pristine_ro m MI). lia.
      + apply HP. cbn. lia.
    - subst w. unfold SO_BUF in *. lia.
    - apply rdn_of_rw_C8. rewrite Z_to_bv_bv_unsigned. exact Hgw.
    - apply u64_range. }
  cps_destruct (printf0_buffered R m (seg_rom s0segs) sp w (bv_unsigned gw) PH eq_refl eq_refl eq_refl) as (regs' & m' & RUN & KEEP & FM & RD1 & RD2 & RD3).
  rewrite MS_mkst.
  eapply (rz_msteps s0segs); [exact Hh | exact Hl | exact RUN |].
  apply (realizes_getr_ext s0segs (mkR_of regs')); [intros r; apply getr_mkR_of|].
  subst R. rewrite (mkR_of_keeps_cs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' KEEP). rewrite <- MS_mkst.
  assert (FM' : frame_mod m m' (lit_regions [(spv - 1056, 1056); (SO_FILE, 4); (SO_FILE + 40, 8); (w, 2)]%Z)) by exact FM.
  assert (Hw : SO_BUF <= w /\ w + 2 <= SO_BUF + 1022) by (subst w; lia).
  assert (MU : munch (pfN_W spv w) m m').
  { replace (pfN_W spv w) with (ivs_of_regions [(spv - 1056, 1056); (SO_FILE, 4); (SO_FILE + 40, 8); (w, 2)]%Z)
      by (cbn; unfold pfN_W; repeat f_equal; lia).
    apply (munch_of_frame_mod [(spv - 1056, 1056); (SO_FILE, 4); (SO_FILE + 40, 8); (w, 2)]%Z m m'); [|exact FM'].
    repeat constructor; cbn; unfold SO_FILE, SO_BUF in *; subst spv; lia. }
  pose proof (wmono_of_frame_mod _ _ _ FM') as WMO.
  pose proof (pres_of_munch _ _ _ MU WMO) as PR.
  apply HK.
  - exact MU.
  - exact WMO.
  - eapply mem_inv_munch; [exact MU | | exact MI]. repeat constructor; cbn; unfold SO_FILE, SO_BUF in *; subst spv; lia.
  - eapply stk_grows; [exact ST | exact (proj2 FM') | lia].
  - eapply statics1_pres; [exact PR | | exact SP0 | exact STAT].
    intros a Ha. unfold statics1_addr, core1_addr, ax_addr, OFL in Ha. cbn [in_ivs S_IVS1] in Ha. cbn. unfold SO_FILE, SO_BUF in *. subst spv. lia.
  - split; [|split].
    + (* [comment removed for export] *)
      rewrite length_app. cbn [length ZL]. replace (SO_BUF + Z.of_nat (length pending + 2))%Z with (w + 2)%Z by lia.
      destruct WMD; cbn [pf_file pf_buf pf_swrite PF0_S0] in *.
      constructor; cbn [pf_file pf_buf pf_swrite PF0_S0]; unfold cellZ; try assumption;
        (eapply cellZ_pres; [exact PR | | lia | lia | eassumption]); cbn; unfold SO_FILE, SO_BUF in *; subst spv; intros; lia.
    + apply (proj2 (bytes_at_app s0segs m' SO_BUF pending ZL)). split.
      * eapply pres_bytes_at; [exact PR | exact B |]. cbn. unfold SO_FILE, SO_BUF in *. subst spv. intros; lia.
      * replace (SO_BUF + Z.of_nat (length pending))%Z with w by reflexivity.
        apply (bytes_at_of_rdn 2). 2-3: unfold SO_BUF in *; lia. exact RD1.
    + rewrite length_app. cbn [length ZL]. lia.
Qed.

End ACeilS3.
