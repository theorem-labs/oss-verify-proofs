(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shspan (A n : Z) : Z := (A + n + 7) / 8 - A / 8.

Definition aregU (RNG : footprint) (m : amem) (A n : Z) : Prop :=
  ablk A (A + n) /\ unpoisoned m A (A + n) /\ rng RNG A n /\ rng RNG (shad A) (shspan A n).
Definition areg (RNG : footprint) (m : amem) (A n : Z) : Prop := 0 < n -> aregU RNG m A n.

(* [comment removed for export] *)
Definition aro (RNG : footprint) (m : amem) (A n : Z) : Prop :=
  unpoisoned m A (A + n) /\ rng RNG A n /\ rng RNG (shad A) (shspan A n).

Definition ahull (RNG : footprint) (m : amem) (A n : Z) : Prop :=
  exists RLO RHI, RLO <= A /\ A + n <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND
    /\ wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Definition art (m : amem) : Prop :=
  rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m.

Definition astk (RNG : footprint) (lo SPV : Z) : Prop :=
  KHIGH <= lo /\ rng RNG lo (SPV - lo) /\ rng_aimg RNG.

(* [comment removed for export] *)
Lemma shspan_sub : forall A n A' n', A <= A' -> 0 <= n' -> A' + n' <= A + n ->
  shad A <= shad A' /\ shad A' + shspan A' n' <= shad A + shspan A n.
Proof. intros A n A' n' H1 H2 H3. unfold shspan. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

Lemma aregU_sub : forall RNG m A n A' n', areg RNG m A n -> 0 < n -> A <= A' -> 0 <= n' -> A' + n' <= A + n -> aregU RNG m A' n'.
Proof.
  intros RNG m A n A' n' AR Hn H1 H2 H3. destruct (AR Hn) as (B & U & R1 & R2).
  destruct (shspan_sub A n A' n' H1 H2 H3) as [S1 S2]. split; [| split; [| split]].
  - eapply ablk_sub; [exact B | lia | lia].
  - eapply unpoisoned_sub; [exact U | lia | lia].
  - eapply rng_sub; [exact R1 | lia | lia].
  - eapply rng_sub; [exact R2 | lia | lia].
Qed.
Lemma aregU_areg : forall RNG m A n, aregU RNG m A n -> areg RNG m A n.
Proof. intros RNG m A n H _. exact H. Qed.

Lemma areg_sub : forall RNG m A n A' n', areg RNG m A n -> A <= A' -> 0 <= n' -> A' + n' <= A + n -> areg RNG m A' n'.
Proof.
  intros RNG m A n A' n' AR H1 H2 H3 Hn'. destruct (AR ltac:(lia)) as (B & U & R1 & R2).
  destruct (shspan_sub A n A' n' H1 H2 H3) as [S4 S5]. split; [| split; [| split]].
  - eapply ablk_sub; [exact B | lia | lia].
  - eapply unpoisoned_sub; [exact U | lia | lia].
  - eapply rng_sub; [exact R1 | lia | lia].
  - eapply rng_sub; [exact R2 | lia | lia].
Qed.

Lemma aro_sub : forall RNG m A n A' n', aro RNG m A n -> A <= A' -> 0 <= n' -> A' + n' <= A + n -> aro RNG m A' n'.
Proof.
  intros RNG m A n A' n' (U & R1 & R2) H1 H2 H3. destruct (shspan_sub A n A' n' H1 H2 H3) as [S1 S2]. split; [| split].
  - eapply unpoisoned_sub; [exact U | lia | lia].
  - eapply rng_sub; [exact R1 | lia | lia].
  - eapply rng_sub; [exact R2 | lia | lia].
Qed.

Lemma aregU_aro : forall RNG m A n, aregU RNG m A n -> aro RNG m A n.
Proof. intros RNG m A n (_ & U & R1 & R2). split; [exact U|]. split; [exact R1 | exact R2]. Qed.
Lemma aregU_app_blk : forall RNG m A n, aregU RNG m A n -> 0 <= n -> app_blk A (A + n).
Proof. intros RNG m A n (B & _) H. apply ablk_app_blk; [exact B | lia]. Qed.

Lemma areg_empty : forall RNG m A, areg RNG m A 0.
Proof. intros RNG m A H. lia. Qed.

(* [comment removed for export] *)
Lemma astk_sub : forall RNG lo SPV SP', astk RNG lo SPV -> lo <= SP' <= SPV -> astk RNG lo SP'.
Proof. intros RNG lo SPV SP' (K & R & I) H. split; [exact K|]. split; [eapply rng_sub; [exact R | lia | lia] | exact I]. Qed.

(* [comment removed for export] *)
Definition azstk (RNG : footprint) (m : amem) (lo hi : Z) : Prop :=
  exists RLO RHI, unpoisoned m lo hi
    /\ (RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
    /\ wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ app_blk lo hi /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma azstk_sub : forall RNG m lo hi lo' hi', azstk RNG m lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> azstk RNG m lo' hi'.
Proof.
  intros RNG m lo hi lo' hi' (RLO & RHI & U & H & W & AB & R) H1 H2 H3. exists RLO, RHI. split; [eapply unpoisoned_sub; [exact U | lia | lia]|].
  split; [lia|]. split; [exact W|]. split; [eapply app_blk_sub; [exact AB | lia | lia | lia] | exact R].
Qed.

Lemma azstk_aro : forall RNG m lo hi X n, azstk RNG m lo hi -> lo <= X -> 0 <= n -> X + n <= hi -> rng RNG X n -> aro RNG m X n.
Proof.
  intros RNG m lo hi X n (RLO & RHI & U & H & W & AB & R) H1 H2 H3 RX. split; [eapply unpoisoned_sub; [exact U | lia | lia]|].
  split; [exact RX|]. eapply rng_sub; [exact R| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
Qed.

Lemma azstk_ahull : forall RNG m lo hi X n, azstk RNG m lo hi -> lo <= X -> 0 <= n -> X + n <= hi -> ahull RNG m X n.
Proof.
  intros RNG m lo hi X n (RLO & RHI & U & H & W & AB & R) H1 H2 H3. exists RLO, RHI. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact W | exact R].
Qed.

Lemma azstk_app : forall RNG m lo hi X n, azstk RNG m lo hi -> lo <= X -> 0 <= n -> X + n <= hi -> app_blk X (X + n).
Proof. intros RNG m lo hi X n (RLO & RHI & U & H & W & AB & R) H1 H2 H3. eapply app_blk_sub; [exact AB | lia | lia | lia]. Qed.

(* [comment removed for export] *)
Definition aappW (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLOW \/ KHIGH <= fst iv) W.

Lemma aappW_shadow_disjoint : forall W a n, aappW W -> 0 <= a -> 0 <= n -> a + n <= shad KEND -> ASHOFF <= a -> disjoint_from W a n.
Proof.
  intros W a n HW H0 H1 H2 H3. induction HW as [|[x y] W Hxy HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hxy. split; [| exact IH].
  rewrite ?shad_div in *. unfold ASHOFF, KLOW, KHIGH, KEND in *. Z.div_mod_to_equations. lia.
Qed.

Lemma azstk_transport : forall RNG m m' W lo hi, azstk RNG m lo hi -> munch W m m' -> wmono bsegs m m' -> aappW W -> lo < hi ->
  azstk RNG m' lo hi.
Proof.
  intros RNG m m' W lo hi (RLO & RHI & U & H & W0 & AB & R) MU WM HW LT. exists RLO, RHI.
  split; [| split; [exact H| split; [eapply wr_at_transport; [exact W0 | exact WM] | split; [exact AB | exact R]]]].
  eapply unpoisoned_munch; [exact U | exact MU |]. apply aappW_shadow_disjoint; [exact HW | | | |].
  - rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - rewrite !shad_div. Z.div_mod_to_equations. lia.
  - destruct AB as [_ AB]. rewrite !shad_div. unfold ASHOFF, KEND, KLOW, KHIGH in *. Z.div_mod_to_equations. lia.
  - rewrite shad_div. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fake_le (c : Z) (k : nat) (LB : list ablock) : Prop :=
  forall l : list Z, List.NoDup l -> (forall F, In F l -> exists n, In (mkABlock (ABFake c) F n) LB) -> (length l <= k)%nat.

Lemma fake_le_none : forall c LB, (forall F n, ~ In (mkABlock (ABFake c) F n) LB) -> fake_le c 0 LB.
Proof.
  intros c LB H [|F l] _ HL; [cbn; lia|]. exfalso. destruct (HL F (or_introl eq_refl)) as [n Hn]. exact (H F n Hn).
Qed.

Lemma fake_le_mono : forall c k k' LB, fake_le c k LB -> (k <= k')%nat -> fake_le c k' LB.
Proof. intros c k k' LB H Hk l ND HL. specialize (H l ND HL). lia. Qed.

(* [comment removed for export] *)
Lemma fake_le_length : forall c LB, fake_le c (length LB) LB.
Proof.
  intros c LB l ND HL. rewrite <- (length_map ab_addr LB). apply NoDup_incl_length; [exact ND|].
  intros F HF. destruct (HL F HF) as [n Hn]. apply in_map_iff. exists (mkABlock (ABFake c) F n). split; [reflexivity | exact Hn].
Qed.

(* [comment removed for export] *)
Lemma fake_le_push_other : forall c k LB b, fake_le c k LB -> (forall F n, b <> mkABlock (ABFake c) F n) -> fake_le c k (b :: LB).
Proof.
  intros c k LB b H Hb l ND HL. apply H; [exact ND|]. intros F HF. destruct (HL F HF) as [n [E|Hn]].
  - exfalso. exact (Hb F n E).
  - exists n. exact Hn.
Qed.

(* [comment removed for export] *)
Definition fake_area (L : alayout) : list (Z * Z) :=
  [(al_fake L, al_fake L + FAKESZ); (shad (al_fake L), shad (al_fake L) + FAKESZ / 8)].

(* [comment removed for export] *)
Lemma azstk_transport_F : forall RNG m m' W L lo hi, azstk RNG m lo hi -> munch (W ++ fake_area L) m m' -> wmono bsegs m m' ->
  aappW W -> ablk (al_fake L) (al_fake L + FAKESZ) -> al_fake L mod 8 = 0 -> al_fake L + FAKESZ <= lo -> lo < hi -> azstk RNG m' lo hi.
Proof.
  intros RNG m m' W L lo hi (RLO & RHI & U & H & W0 & AB & R) MU WM HW AF F8 FL LT. exists RLO, RHI.
  split; [| split; [exact H| split; [eapply wr_at_transport; [exact W0 | exact WM] | split; [exact AB | exact R]]]].
  eapply unpoisoned_munch; [exact U | exact MU |].
  assert (DW : disjoint_from W (shad lo) (shad (hi - 1) + 1 - shad lo)).
  { apply aappW_shadow_disjoint; [exact HW | | | |].
    - rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
    - rewrite !shad_div. Z.div_mod_to_equations. lia.
    - destruct AB as [_ AB]. rewrite !shad_div. unfold ASHOFF, KEND, KLOW, KHIGH in *. Z.div_mod_to_equations. lia.
    - rewrite shad_div. Z.div_mod_to_equations. lia. }
  assert (DF : disjoint_from (fake_area L) (shad lo) (shad (hi - 1) + 1 - shad lo)).
  { pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    unfold fake_area, FAKESZ in *. cbn [disjoint_from]. destruct AB as [_ AB]. unfold ablk, AIMG_HI, KLS in AF.
    rewrite !shad_div. unfold ASHOFF, KEND, KLOW, KHIGH in *.
    split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
  clear - DW DF. induction W as [|[x y] W IH]; cbn [app disjoint_from] in *; [exact DF|].
  destruct DW as [D1 D2]. split; [exact D1 | exact (IH D2)].
Qed.

(* [comment removed for export] *)
Definition ffr_pres (W : list (Z * Z)) (LB : list ablock) (m m' : amem) : Prop :=
  magree bsegs (fun a => (in_fake LB a /\ outside W a) \/ exists a', in_fake LB a' /\ a = shad a') m m'.

Lemma ffr_pres_refl : forall W LB m, ffr_pres W LB m m.
Proof. intros W LB m. apply magree_refl. Qed.
Lemma ffr_pres_trans : forall W LB m1 m2 m3, ffr_pres W LB m1 m2 -> ffr_pres W LB m2 m3 -> ffr_pres W LB m1 m3.
Proof. intros W LB m1 m2 m3. apply magree_trans. Qed.

(* [comment removed for export] *)
Definition ainblk (LB : list ablock) (A n : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= A /\ A + n <= ab_addr b + ab_size b.

(* [comment removed for export] *)
Definition ainimg (LB : list ablock) (A n : Z) : Prop := ainblk LB A n \/ (0 <= A /\ A + n <= AIMG_HI).

Lemma ainimg_sub : forall LB A n A' n', ainimg LB A n -> A <= A' -> A' + n' <= A + n -> ainimg LB A' n'.
Proof.
  intros LB A n A' n' [(b & Hb & H1 & H2)|(H1 & H2)] Ha Hb'; [left; exists b; split; [exact Hb| lia] | right; lia].
Qed.


(* [comment removed for export] *)
Definition hb_heap (LB : list ablock) : Prop := forall b, In b LB -> exists p A n, b = HB p A n.

Lemma hb_heap_nil : hb_heap [].
Proof. intros b []. Qed.
Lemma hb_heap_cons : forall p A n LB, hb_heap LB -> hb_heap (HB p A n :: LB).
Proof. intros p A n LB H b [E|Hb]; [exists p, A, n; symmetry; exact E| exact (H b Hb)]. Qed.

(* [comment removed for export] *)
Lemma nodup_remove_length : forall (l : list Z) x, List.NoDup l -> In x l ->
  length l = S (length (List.remove Z.eq_dec x l)) /\ List.NoDup (List.remove Z.eq_dec x l).
Proof.
  induction l as [|y l IH]; intros x ND HI; [destruct HI|].
  inversion ND as [|y' l' NY NDl]; subst. cbn [List.remove length].
  destruct (Z.eq_dec x y) as [E|NE].
  - subst y. rewrite (List.notin_remove Z.eq_dec l x NY). split; [reflexivity| exact NDl].
  - destruct HI as [E|HI]; [exfalso; exact (NE (eq_sym E))|].
    destruct (IH x NDl HI) as [L ND']. cbn [length]. split; [lia|].
    constructor; [| exact ND']. intros X. apply List.in_remove in X. destruct X as [X _]. exact (NY X).
Qed.

Lemma fake_le_push_any : forall c k LB b, fake_le c k LB -> fake_le c (S k) (b :: LB).
Proof.
  intros c k LB b H l ND HL.
  destruct (List.in_dec Z.eq_dec (ab_addr b) l) as [IN|NI].
  - (* [comment removed for export] *)
    destruct (nodup_remove_length l (ab_addr b) ND IN) as [LEN NDR]. rewrite LEN. apply le_n_S.
    apply H; [exact NDR|].
    intros F HF. apply List.in_remove in HF. destruct HF as [HF NE].
    destruct (HL F HF) as [n [E|Hn]]; [| exists n; exact Hn].
    exfalso. apply NE. rewrite E. reflexivity.
  - apply le_S. apply H; [exact ND|]. intros F HF. destruct (HL F HF) as [n [E|Hn]]; [| exists n; exact Hn].
    exfalso. apply NI. rewrite E. cbn [ab_addr]. exact HF.
Qed.

(* [comment removed for export] *)
Definition ashort (LB : list ablock) (d : Z) : Prop :=
  forall c, 0 <= c <= 2 -> fake_le c (Z.to_nat (4096 - d)) LB.

Lemma ashort_fake_le : forall LB d c, ashort LB d -> 0 <= c <= 2 -> fake_le c (Z.to_nat (4096 - d)) LB.
Proof. intros LB d c H Hc. exact (H c Hc). Qed.

Lemma ashort_mono : forall LB d d', ashort LB d -> d' <= d -> ashort LB d'.
Proof. intros LB d d' H Hd c Hc. eapply fake_le_mono; [exact (H c Hc)| lia]. Qed.

(* [comment removed for export] *)
Lemma ashort_push : forall b LB d, ashort LB (d + 1) -> d < 4096 -> ashort (b :: LB) d.
Proof.
  intros b LB d H Hd c Hc. replace (Z.to_nat (4096 - d)) with (S (Z.to_nat (4096 - (d + 1)))) by lia.
  apply fake_le_push_any. exact (H c Hc).
Qed.

(* [comment removed for export] *)
Lemma ashort_push_heap : forall p A n LB d, ashort LB d -> ashort (HB p A n :: LB) d.
Proof. intros p A n LB d H c Hc. apply fake_le_push_other; [exact (H c Hc)|]. intros F k E. discriminate E. Qed.

Lemma ashort_heap : forall LB d, hb_heap LB -> ashort LB d.
Proof.
  intros LB d HH c Hc. eapply fake_le_mono; [| apply Nat.le_0_l]. apply fake_le_none.
  intros F n Hin. destruct (HH _ Hin) as (p & A & k & E). discriminate E.
Qed.

(* [comment removed for export] *)
Definition fake_heap_law (AI : AMallocIface) : Prop :=
  forall L RNG st LB m, AHEAP AI L RNG st LB m ->
    ablk (al_fake L) (al_fake L + FAKESZ) /\ (forall p A n, In (HB p A n) LB -> A + n <= al_fake L \/ al_fake L + FAKESZ <= A).

(* [comment removed for export] *)
Lemma fake_area_block : forall AI L RNG st LB m p A n, fake_heap_law AI -> AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
  disjoint_from (fake_area L) A n /\ disjoint_from (fake_area L) (shad A) (shspan A n).
Proof.
  intros AI L RNG st LB m p A n FH AH Hin. destruct (FH _ _ _ _ _ AH) as [FB FD]. pose proof (FD p A n Hin) as DJ.
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (N & (BR & _) & _).
  pose proof (ablk_lin _ _ BR) as L1. pose proof (ablk_disj_band _ _ BR) as D1.
  pose proof (ablk_lin _ _ FB) as L2. pose proof (ablk_disj_band _ _ FB) as D2.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (FA : al_fake L mod 8 = 0) by (unfold al_fake; Z.div_mod_to_equations; lia).
  unfold fake_area, shspan. cbn [disjoint_from]. rewrite !shad_div. unfold FAKESZ, ASHOFF, KLS, AIMG_HI in *.
  clear - DJ N L1 D1 L2 D2 ATR FA.
  split; (split; [| split; [| exact I]]); Z.div_mod_to_equations; lia.
Qed.


(* [comment removed for export] *)
Definition ablkLB (LB : list ablock) : Prop := forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).

Lemma ablkLB_nil : ablkLB [].
Proof. intros b []. Qed.
Lemma ablkLB_cons : forall b LB, ablk (ab_addr b) (ab_addr b + ab_size b) -> ablkLB LB -> ablkLB (b :: LB).
Proof. intros b LB H HL b' [<-|Hin]; [exact H| exact (HL b' Hin)]. Qed.
Lemma ablkLB_tail : forall b LB, ablkLB (b :: LB) -> ablkLB LB.
Proof. intros b LB H b' Hin. apply H. right. exact Hin. Qed.
Lemma ablkLB_sub : forall LB LB', ablkLB LB' -> (forall b, In b LB -> In b LB') -> ablkLB LB.
Proof. intros LB LB' H HI b Hin. exact (H b (HI b Hin)). Qed.
(* [comment removed for export] *)
Lemma ablkLB_heap : forall AI L RNG st LB m, AHEAP AI L RNG st LB m -> hb_heap LB -> ablkLB LB.
Proof.
  intros AI L RNG st LB m AH HH b Hin. destruct (HH b Hin) as (p & A & n & ->).
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (_ & (BR & _) & _). cbn [ab_addr ab_size]. exact BR.
Qed.

(* [comment removed for export] *)
Definition afpre (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop)
    (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m : amem) (lo SPV d : Z) : Prop :=
  AHEAP AI L RNG st LB m /\ ashort LB d /\ art m /\ astk RNG lo SPV /\ rng_fs L RNG /\
  ATOP + 4096 <= lo /\ SPV + 16 < al_top L /\ SPV mod 16 = 0
  (* [comment removed for export] *)
  /\ rng RNG lo (al_top L - lo)
  (* [comment removed for export] *)
  /\ ablkLB LB.

End CANSEC1.
