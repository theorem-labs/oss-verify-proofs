(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5PK.
Section WithSegs.
Variable segs : list Segment.
Variable L : heap_layout.
Context {SCFG_P : ScfgP}.
(* [comment removed for export] *)
Abbreviation CEIL := (hl_sptop L - 8388608).
(* [comment removed for export] *)
Hypothesis IMG_HI : hl_img_hi L <= 0x7fff7f800000.
Hypothesis SPTOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis ERRNO : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Hypothesis IMG_LO : 0 <= hl_img_lo L <= hl_img_hi L.
(* [comment removed for export] *)
Hypothesis SEGS_BELOW : forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) (hl_img_hi L)) segs = true.
(* [comment removed for export] *)
Ltac geom := generalize (conj IMG_HI (conj SPTOP ERRNO)); intros _; clear IMG_LO SEGS_BELOW.
Ltac nogeom := clear IMG_HI SPTOP ERRNO IMG_LO SEGS_BELOW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_none (l : list Segment) a n :
  forallb (fun seg => Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) (hl_img_hi L)) l = true ->
  hl_img_hi L <= a -> 0 < n -> find_segment l a n = None.
Proof.
  induction l as [|s l IH]; intros HB Ha Hn. reflexivity.
  cbn [forallb] in HB. apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment]. destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E2. exfalso. lia.
  - apply IH; assumption.
Qed.

Lemma top_none (x : word) : hl_img_hi L <= bv_unsigned x -> seg_rom segs x = None.
Proof.
  intros Hx. unfold seg_rom, memory_read. rewrite (find_segment_none segs). reflexivity. exact SEGS_BELOW. exact Hx. cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma defined_of_rdn M : forall (n : nat) a bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> hl_img_hi L <= a ->
  rdn segs M (Z_to_bv 64 a) n = Some bs -> L5.defined M a (Z.of_nat n).
Proof.
  clear IMG_HI SPTOP ERRNO IMG_LO. induction n as [|n IH]; intros a bs Ha Hn Hi HR i Hii. lia.
  cbn [rdn] in HR.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:EM.
  - destruct (rdn segs M (Z_to_bv 64 a + 1)%bv n) as [rest|] eqn:ER; [|discriminate].
    destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite Z.add_0_r, EM. discriminate.
    rewrite (L5C.add1_lit a) in ER. replace (a + i) with (a + 1 + (i - 1)) by lia.
    apply (IH (a + 1) rest); try lia. exact ER.
  - rewrite (top_none (Z_to_bv 64 a)) in HR. discriminate. rewrite L5.unsigned_lit by lia. lia.
Qed.
Lemma defined_of_u64 M a v : 0 <= a -> a + 8 <= 2 ^ 64 -> hl_img_hi L <= a -> L5.u64_at segs M a v -> L5.defined M a 8.
Proof. clear IMG_HI SPTOP ERRNO IMG_LO. intros Ha H8 Hi Hu. apply (defined_of_rdn M 8 a _ Ha ltac:(cbn; lia) Hi Hu). Qed.
Lemma defined_of_u8 M a v : 0 <= a -> a + 1 <= 2 ^ 64 -> hl_img_hi L <= a -> L5.u8_at segs M a v -> L5.defined M a 1.
Proof. clear IMG_HI SPTOP ERRNO IMG_LO. intros Ha H1 Hi Hu. apply (defined_of_rdn M 1 a _ Ha ltac:(cbn; lia) Hi Hu). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lb_sub (LB LB' : list (Z * Z)) : Prop := forall b, In b LB -> In b LB'.
Lemma lb_sub_refl LB : lb_sub LB LB. Proof. intros b H; exact H. Qed.
Lemma lb_sub_trans A B C : lb_sub A B -> lb_sub B C -> lb_sub A C. Proof. intros H1 H2 b Hb. apply H2, H1, Hb. Qed.
Lemma lb_sub_cons LB A n : lb_sub LB ((A, n) :: LB). Proof. intros b Hb. right. exact Hb. Qed.
Lemma lb_sub_remove LB LB' A : lb_sub LB LB' -> (forall b, In b LB -> fst b <> A) -> lb_sub LB (lb_remove A LB').
Proof. intros S NE b Hb. destruct b as [B m]. apply L5C.in_lb_remove_neq. apply S. exact Hb. apply (NE (B, m)). exact Hb. Qed.

Lemma kept_mono LB LB' sp scr W a : lb_sub LB LB' -> L5C.kept L LB sp scr W a -> L5C.kept L LB' sp scr W a.
Proof.
  nogeom. intros S (Ha & CA & NE & OW). split. exact Ha. split.
  - destruct CA as [IB|[ST|IM]]. left. destruct IB as (b & Hb & Hr). exists b. split. apply S. exact Hb. exact Hr.
    right; left; exact ST. right; right; exact IM.
  - split; assumption.
Qed.

(* [comment removed for export] *)
Definition lb_wf (LB : list (Z * Z)) : Prop :=
  forall b, In b LB -> 4096 <= fst b /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b) /\ fst b + snd b <= CEIL.

Lemma lb_wf_of_heap HI LB cr M VM : heap_iface_ok L SCFG HI -> hi_heap HI LB cr M VM -> lb_wf LB.
Proof.
  nogeom. intros HIok HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition fresh_rng (LB : list (Z * Z)) (A n : Z) : Prop :=
  4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A) /\ A + n <= CEIL /\ blocks_apart A n LB.

Lemma fresh_of_block LB LB' M A n : lb_sub LB LB' -> L5C.fresh_block L LB' M A n -> fresh_rng LB A n.
Proof.
  nogeom. intros S [[B0 [B1 [B2 [B3 B4]]]] [BA _]]. split. exact B0. split. exact B1. split. exact B4.
  intros b Hb. apply BA. apply S. exact Hb.
Qed.

(* [comment removed for export] *)
Inductive wr_ok (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) : L5.range -> Prop :=
| wr_scratch lo n : sp - scr <= lo -> lo + n <= sp -> wr_ok LB sp scr W (lo, n)
| wr_declared lo n lo' n' : In (lo', n') W -> lo' <= lo -> lo + n <= lo' + n' -> wr_ok LB sp scr W (lo, n)
| wr_fresh lo n A m : fresh_rng LB A m -> A <= lo -> lo + n <= A + m -> wr_ok LB sp scr W (lo, n)
| wr_empty lo n : n <= 0 -> wr_ok LB sp scr W (lo, n)
| wr_errno lo n : hl_errno L <= lo -> lo + n <= hl_errno L + 4 -> wr_ok LB sp scr W (lo, n).

Lemma kept_not_in LB sp scr W a lo n :
  lb_wf LB -> CEIL + scr <= sp -> wr_ok LB sp scr W (lo, n) -> L5C.kept L LB sp scr W a -> ~ (lo <= a < lo + n).
Proof.
  geom. intros HLB Hsp W0 K Hin. pose proof K as (Ha & CA & NE & OW).
  inversion W0; subst.
  - destruct CA as [IB|[[S1 S2]|[IM _]]].
    + destruct IB as (b & Hb & Hrb). pose proof (HLB b Hb). lia.
    + apply S2. lia.
    + lia.
  - apply (OW (lo', n')). exact H1. unfold L5.in_rng. cbn. lia.
  - destruct H1 as (F0 & F1 & F2 & F3). destruct CA as [IB|[[S1 S2]|[IM _]]].
    + destruct IB as (b & Hb & Hrb). pose proof (F3 b Hb). pose proof (HLB b Hb). lia.
    + lia.
    + lia.
  - lia.
  - apply NE. unfold in_errno. lia.
Qed.

Lemma kept_outside LB sp scr W F a :
  lb_wf LB -> CEIL + scr <= sp -> Forall (wr_ok LB sp scr W) F -> L5C.kept L LB sp scr W a -> L5.outside F a.
Proof.
  geom. intros HLB Hsp HF K r Hr. destruct r as [lo n]. unfold L5.in_rng; cbn [fst snd].
  eapply kept_not_in; eauto. apply (proj1 (Forall_forall _ _) HF). exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hpres_refl LB sp scr W M : L5.defined M (sp - scr) scr -> L5C.hpres L LB sp scr W M M.
Proof. nogeom. intros D. split. intros; reflexivity. split. exact D. intros a _ _ _ H; exact H. Qed.

(* [comment removed for export] *)
Lemma hpres_step_pure LB sp scr W M0 M1 M2 (F : list L5.range) :
  lb_wf LB -> CEIL + scr <= sp ->
  L5C.hpres L LB sp scr W M0 M1 ->
  (forall x : word, L5.outside F (bv_unsigned x) -> M2 x = M1 x) -> mem_grows M1 M2 ->
  Forall (wr_ok LB sp scr W) F ->
  L5C.hpres L LB sp scr W M0 M2.
Proof.
  geom. intros HLB Hsp (P & D & WD) FR GR WF. split; [|split].
  - intros a K. rewrite FR. apply P. exact K. rewrite L5.unsigned_lit by (destruct K; lia). eapply kept_outside; eauto.
  - eapply L5.defined_grows; eauto.
  - intros a Ha CA NE H0. apply GR. exact (WD a Ha CA NE H0).
Qed.

(* [comment removed for export] *)
Lemma hpres_step_call LB LB' sp scr W sp' scr' W' M0 M1 M2 :
  lb_wf LB -> CEIL + scr <= sp -> sp <= 2 ^ 47 ->
  L5C.hpres L LB sp scr W M0 M1 -> L5C.hpres L LB' sp' scr' W' M1 M2 -> lb_sub LB LB' ->
  sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr' ->
  Forall (wr_ok LB sp scr W) W' ->
  L5C.hpres L LB sp scr W M0 M2.
Proof.
  geom. intros HLB Hsp Hsp47 (P & D & WD) (P' & D' & WD') S H1 H2 H3 WF. pose proof ERRNO as He.
  assert (CL: forall a, client_addr L LB sp scr a -> ~ (sp' - scr' <= a < sp') -> client_addr L LB' sp' scr' a).
  { intros a CA NS. destruct CA as [IB|[[S1 S2]|IM]].
    - left. destruct IB as (b & Hb & Hr). exists b. split. apply S. exact Hb. exact Hr.
    - right; left. split. exact S1. exact NS.
    - right; right. exact IM. }
  split; [|split].
  - intros a K. rewrite P'. apply P. exact K.
    pose proof K as (Ha & CA & NE & OW). split. exact Ha. split. apply CL. exact CA. destruct CA as [IB|[[S1 S2]|[IM _]]].
    + destruct IB as (b & Hb & Hrb). pose proof (HLB b Hb). lia.
    + lia.
    + lia.
    + split. exact NE. eapply kept_outside; eauto.
  - intros i Hi. destruct (Z_lt_le_dec (sp - scr + i) (sp' - scr')) as [Hlt|Hge].
    + apply WD'. lia. right; left. lia. unfold in_errno. lia. apply D. lia.
    + destruct (Z_lt_le_dec (sp - scr + i) sp') as [Hlt'|Hge'].
      * replace (sp - scr + i) with (sp' - scr' + (sp - scr + i - (sp' - scr'))) by lia. apply D'. lia.
      * apply WD'. lia. right; left. lia. unfold in_errno. lia. apply D. lia.
  - intros a Ha CA NE H0. apply WD'. exact Ha. 2: exact NE. 2: exact (WD a Ha CA NE H0).
    apply CL. exact CA. destruct CA as [IB|[[S1 S2]|[IM _]]].
    + destruct IB as (b & Hb & Hrb). pose proof (HLB b Hb). lia.
    + lia.
    + lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma agree_pure M1 M2 (F : list L5.range) a n :
  (forall x : word, L5.outside F (bv_unsigned x) -> M2 x = M1 x) -> 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, a <= i < a + n -> L5.outside F i) -> L5C.agree_on M1 M2 a n.
Proof. nogeom. intros FR Ha Hn HO i Hi. apply FR. rewrite L5.unsigned_lit by lia. apply HO. lia. Qed.

(* [comment removed for export] *)
Lemma agree_call_stack LB' sp' scr' W' M1 M2 a n :
  L5C.hpres L LB' sp' scr' W' M1 M2 -> CEIL + scr' <= sp' -> 0 <= scr' ->
  sp' <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> L5.outside W' i) -> L5C.agree_on M1 M2 a n.
Proof.
  geom. intros HP Hsp Hscr Ha Hn HO i Hi. pose proof ERRNO. apply (proj1 HP). apply L5C.kept_stack. lia. lia. lia. lia. (exact (proj1 SPTOP)). apply HO. lia.
Qed.
(* [comment removed for export] *)
Lemma agree_call_below LB' sp' scr' W' M1 M2 a n :
  L5C.hpres L LB' sp' scr' W' M1 M2 -> 0 <= scr' -> sp' <= 2 ^ 47 ->
  CEIL <= a -> a + n <= sp' - scr' -> (forall i, a <= i < a + n -> L5.outside W' i) -> L5C.agree_on M1 M2 a n.
Proof.
  geom. intros HP Hscr Hsp Ha Hn HO i Hi. pose proof ERRNO. apply (proj1 HP). apply L5C.kept_below. lia. lia. lia. lia. exact (proj1 SPTOP).
  apply HO. lia.
Qed.
(* [comment removed for export] *)
Lemma agree_call_block LB' sp' scr' W' M1 M2 A m a n :
  L5C.hpres L LB' sp' scr' W' M1 M2 -> In (A, m) LB' -> 0 <= A -> (A + m <= hl_img_lo L \/ hl_img_hi L <= A) -> A + m <= CEIL ->
  A <= a -> a + n <= A + m -> (forall i, a <= i < a + n -> L5.outside W' i) -> L5C.agree_on M1 M2 a n.
Proof.
  geom. intros HP Hin HA0 HA HAm Ha Hn HO i Hi. pose proof ERRNO. apply (proj1 HP). eapply L5C.kept_block. exact Hin. lia. lia. lia. lia.
  apply HO. lia.
Qed.
(* [comment removed for export] *)
Lemma agree_call_static LB' sp' scr' W' M1 M2 a n :
  L5C.hpres L LB' sp' scr' W' M1 M2 -> hl_img_lo L <= a -> a + n <= hl_img_hi L ->
  (forall i, a <= i < a + n -> ~ hl_alloc_static L i) -> (a + n <= hl_errno L \/ hl_errno L + 4 <= a) ->
  (forall i, a <= i < a + n -> L5.outside W' i) -> L5C.agree_on M1 M2 a n.
Proof.
  generalize (conj IMG_HI (conj SPTOP ERRNO)); intros _; clear SEGS_BELOW.
  intros HP Hlo Hhi HS He HO i Hi. apply (proj1 HP). apply L5C.kept_static. lia. apply HS; lia. lia. lia. lia.
  apply HO. lia.
Qed.

(* [comment removed for export] *)
Lemma img_clear_agree M1 M2 lo hi : L5C.agree_on M1 M2 lo (hi - lo) -> L5.img_clear M1 lo hi -> L5.img_clear M2 lo hi.
Proof. nogeom. intros AG IC i Hi. rewrite (AG i) by lia. apply IC. exact Hi. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hi_heap_pure HI LB cr M M' VM (F : list L5.range) :
  heap_iface_ok L SCFG HI -> hi_heap HI LB cr M VM ->
  (forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a) -> CEIL <= hl_sptop L ->
  (forall x : word, L5.outside F (bv_unsigned x) -> M' x = M x) -> mem_grows M M' ->
  Forall (fun r : L5.range => (CEIL <= fst r /\ fst r + snd r <= hl_sptop L) \/ (exists b, In b LB /\ fst b <= fst r /\ fst r + snd r <= fst b + snd b) \/ snd r <= 0) F ->
  hi_heap HI LB cr M' VM.
Proof.
  geom. intros HIok HH Hro Hsp FR GR HF.
  eapply (L5C.hi_heap_client L SCFG HI LB cr M M'). exact HIok. exact HH. exact Hro. exact IMG_HI. exact (proj1 SPTOP).
  2: exact GR.
  intros a Ha.
  assert (DEC: L5.outside F a \/ ~ L5.outside F a).
  { clear. induction F as [|r F IH]. left. intros r Hr. destruct Hr.
    destruct (Z_lt_le_dec a (fst r)) as [H1|H1]. 2: destruct (Z_lt_le_dec a (fst r + snd r)) as [H2|H2].
    - destruct IH as [IH|IH]. left. intros r' [<-|Hr']. unfold L5.in_rng. lia. apply IH. exact Hr'. right. intros H. apply IH. intros r' Hr'. apply H. right. exact Hr'.
    - right. intros H. apply (H r). left; reflexivity. unfold L5.in_rng. lia.
    - destruct IH as [IH|IH]. left. intros r' [<-|Hr']. unfold L5.in_rng. lia. apply IH. exact Hr'. right. intros H. apply IH. intros r' Hr'. apply H. right. exact Hr'. }
  destruct DEC as [OUT|IN]. left. apply FR. rewrite L5.unsigned_lit by lia. exact OUT.
  right.
  assert (EX: exists r, In r F /\ L5.in_rng r a).
  { clear -IN. induction F as [|r F IH]. exfalso. apply IN. intros r Hr. destruct Hr.
    destruct (Z_lt_le_dec a (fst r)) as [H1|H1]. 2: destruct (Z_lt_le_dec a (fst r + snd r)) as [H2|H2].
    - destruct IH as (r' & Hr' & Hin). intros H. apply IN. intros r0 [<-|Hr0]. unfold L5.in_rng; lia. apply H. exact Hr0. exists r'. split. right; exact Hr'. exact Hin.
    - exists r. split. left; reflexivity. unfold L5.in_rng. lia.
    - destruct IH as (r' & Hr' & Hin). intros H. apply IN. intros r0 [<-|Hr0]. unfold L5.in_rng; lia. apply H. exact Hr0. exists r'. split. right; exact Hr'. exact Hin. }
  destruct EX as (r & Hr & Hin). pose proof (proj1 (Forall_forall _ _) HF r Hr) as C. unfold L5.in_rng in Hin.
  destruct C as [[C1 C2]|[(b & Hb & B1 & B2)|C3]].
  - left. lia.
  - right. exists b. split. exact Hb. lia.
  - exfalso. lia.
Qed.

End WithSegs.
End L5PK.
