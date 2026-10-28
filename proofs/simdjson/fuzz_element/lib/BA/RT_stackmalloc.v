(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_facts RT_release R_fs_ok R_fs4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section MoreSep.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation WS := [(shad (l_FSB (lay Σ)), shad (l_FSB (lay Σ) + 0xb09000))].
#[local] Notation WK := [(l_ACEIL (lay Σ), USTACK_TOP)].

Lemma fsb_app_mem : l_FSB L + 0xb09000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= l_FSB L.
Proof. pose proof (fsb_grant Σ m HA) as (_ & _ & _ & G4 & _). exact G4. Qed.

Lemma rs_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from WS a n.
Proof.
  intros a n H1 H2 _. pose proof (fsb_grant Σ m HA) as (G1 & _). cbn. split; [|exact I].
  left. unfold shad, SHB, SEGTOP_A in *. pose proof (Z.div_pos (l_FSB L) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma rs_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from WS a n.
Proof.
  intros b gn a n Hin _ _ H1 H2. pose proof (geo_grant Σ m HA b gn Hin) as (G1 & _ & G3 & G4 & _).
  pose proof (fsb_grant Σ m HA) as (F1 & _ & F3 & _). pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _).
  unfold l_ACEIL, STACK_WIN, rtA_sp0, sp_window_hi in *. cbn. split; [|exact I].
  assert (shad (l_FSB L + 0xb09000) <= 2 ^ 44 + SHB) by (unfold shad; assert ((l_FSB L + 0xb09000) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (SHB <= shad (l_FSB L)) by (unfold shad; pose proof (Z.div_pos (l_FSB L) 8 ltac:(lia) ltac:(lia)); lia).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Lemma rs_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
  (hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> disjoint_from WS a n.
Proof.
  intros lo hi a n M1 M2 H0 H47 H1 H2 _ HF. cbn. split; [|exact I]. destruct HF as [HF|HF]; [left | right];
    unfold shad in *; [assert (hi / 8 <= l_FSB L / 8) by (apply Z.div_le_mono; lia) | assert ((l_FSB L + 0xb09000) / 8 <= lo / 8) by (apply Z.div_le_mono; lia)]; lia.
Qed.

Lemma rs_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from WS a n.
Proof.
  intros a n H1 H2 _. pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & G4 & _).
  pose proof (fsb_grant Σ m HA) as (F1 & _ & F3 & _). pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _).
  unfold l_ACEIL, STACK_WIN, rtA_sp0, sp_window_hi in *. cbn. split; [|exact I].
  assert (shad (l_FSB L + 0xb09000) <= 2 ^ 44 + SHB) by (unfold shad; assert ((l_FSB L + 0xb09000) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (SHB <= shad (l_FSB L)) by (unfold shad; pose proof (Z.div_pos (l_FSB L) 8 ltac:(lia) ltac:(lia)); lia).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Lemma rs_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from WS a n.
Proof.
  intros k0 s0 a n Hk H1 H2 _. destruct (map_geo Σ m HA k0 s0 Hk) as (_ & (G1 & _ & G3 & G4 & _) & Hf & _).
  pose proof (fsb_grant Σ m HA) as (F1 & _ & F3 & _). pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _).
  unfold l_ACEIL, STACK_WIN, rtA_sp0, sp_window_hi in *. cbn. split; [|exact I].
  assert (shad (l_FSB L + 0xb09000) <= 2 ^ 44 + SHB) by (unfold shad; assert ((l_FSB L + 0xb09000) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (SHB <= shad (l_FSB L)) by (unfold shad; pose proof (Z.div_pos (l_FSB L) 8 ltac:(lia) ltac:(lia)); lia).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Theorem fshad_avoid : art_avoid_but_fs WS Σ.
Proof. exact (art_avoid_gen Σ m WS HA rs_img rs_grant rs_shad rs_prb rs_secmap). Qed.

Lemma rk_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from WK a n.
Proof.
  intros a n H1 H2 _. pose proof (rta_sp0_range Σ m HA) as Hr. unfold rtA_sp0, l_ACEIL, STACK_WIN, SEGTOP_A in *. cbn. split; [lia | exact I].
Qed.
Lemma rk_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from WK a n.
Proof. intros b gn a n Hin _ _ H1 H2. pose proof (geo_grant Σ m HA b gn Hin) as (_ & _ & G3 & _). cbn. split; [lia | exact I]. Qed.
Lemma rk_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
  (hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> disjoint_from WK a n.
Proof.
  intros lo hi a n _ _ H0 H47 H1 H2 _ _. pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold rtA_sp0, sp_window_lo in *.
  cbn. split; [|exact I]. left. unfold shad, l_ACEIL, STACK_WIN, SHB in *. assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma rk_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from WK a n.
Proof. intros a n H1 H2 _. pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _). cbn. split; [lia | exact I]. Qed.
Lemma rk_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from WK a n.
Proof. intros k0 s0 a n Hk H1 H2 _. destruct (map_geo Σ m HA k0 s0 Hk) as (_ & (_ & _ & G3 & _) & _). cbn. split; [lia | exact I]. Qed.

Theorem stack_avoid : art_avoid_but_fs WK Σ.
Proof. exact (art_avoid_gen Σ m WK HA rk_img rk_grant rk_shad rk_prb rk_secmap). Qed.

End MoreSep.

Lemma dsjl_app : forall W1 W2 l, dsjl W1 l -> dsjl W2 l -> dsjl (W1 ++ W2) l.
Proof.
  intros W1 W2 l H1 H2. apply Forall_forall. intros r Hr. apply dsj_app; [exact (proj1 (Forall_forall _ _) H1 r Hr) | exact (proj1 (Forall_forall _ _) H2 r Hr)].
Qed.

Lemma Forall_dsj_app : forall {X} (f : X -> Z) (g : X -> Z) W1 W2 l, Forall (fun x => disjoint_from W1 (f x) (g x)) l ->
  Forall (fun x => disjoint_from W2 (f x) (g x)) l -> Forall (fun x => disjoint_from (W1 ++ W2) (f x) (g x)) l.
Proof.
  intros X f g W1 W2 l H1 H2. apply Forall_forall. intros r Hr.
  apply dsj_app; [exact (proj1 (Forall_forall _ _) H1 r Hr) | exact (proj1 (Forall_forall _ _) H2 r Hr)].
Qed.

Theorem art_avoid_but_fs_app : forall W1 W2 Σ, art_avoid_but_fs W1 Σ -> art_avoid_but_fs W2 Σ -> art_avoid_but_fs (W1 ++ W2) Σ.
Proof.
  intros W1 W2 Σ (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  split; [unfold consts_avoid in *; exact (Forall_dsj_app fst (fun r => snd r - fst r) _ _ _ A1 B1)|].
  split.
  { intros c Hc. destruct (A2 c Hc) as ((X1 & X2 & X3) & X4). destruct (B2 c Hc) as ((Y1 & Y2 & Y3) & Y4).
    split; [split; [apply dsj_app; assumption | split; apply dsj_app; assumption] | unfold pclass_avoid in *; apply dsj_app; assumption]. }
  split.
  { intros c i st Hc Hn. pose proof (A3 c i st Hc Hn) as X. pose proof (B3 c i st Hc Hn) as Y. unfold pchunk_avoid in *.
    destruct st as [|n|n|].
    - apply dsj_app; assumption.
    - destruct X as (X1 & X2 & X3 & X4). destruct Y as (Y1 & Y2 & Y3 & Y4).
      split; [apply dsj_app; assumption|]. split; [intros H; apply dsj_app; [exact (X2 H) | exact (Y2 H)]|]. split; apply dsj_app; assumption.
    - destruct X as (X1 & X2 & X3). destruct Y as (Y1 & Y2 & Y3).
      split; [apply dsj_app; assumption|]. split; [intros H; apply dsj_app; [exact (X2 H) | exact (Y2 H)] | apply dsj_app; assumption].
    - apply dsj_app; assumption. }
  split.
  { intros k s Hk. destruct (A4 k s Hk) as (X1 & X2 & X3 & X4 & X5 & X6). destruct (B4 k s Hk) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
    repeat split; apply dsj_app; assumption. }
  split; [destruct A5 as [X1 X2]; destruct B5 as [Y1 Y2]; split; [apply dsjl_app; assumption | apply dsj_app; assumption]|].
  split.
  { destruct A6 as (X1 & X2 & X3). destruct B6 as (Y1 & Y2 & Y3). split; [apply dsj_app; assumption|]. split; [apply dsjl_app; assumption|].
    exact (Forall_dsj_app fst (fun _ => 8192) _ _ _ X3 Y3). }
  split; [destruct A7 as (X1 & X2 & X3); destruct B7 as (Y1 & Y2 & Y3); split; [apply dsjl_app; assumption | split; apply dsj_app; assumption]|].
  split; [apply dsjl_app; assumption|].
  destruct A9 as [X1 X2]. destruct B9 as [Y1 Y2]. split; [apply dsj_app; assumption|].
  exact (Forall_dsj_app (fun r => shad (fst r)) (fun r => shad (snd r - 1) + 1 - shad (fst r)) _ _ _ X2 Y2).
Qed.

Definition fs_push (Σ : rtsA) (k : nat) (g : fsst) (f : Z) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (match k with 5%nat => g | _ => fs0 Σ end) (match k with 0%nat => g | _ => fsc0 Σ end)
    (match k with 5%nat | 0%nat | 1%nat => fs4 Σ | _ => g end) (match k with 1%nat => g | _ => fs1 Σ end) (ia_init Σ) (credit Σ - 1) (live Σ) ((f, k) :: frames Σ) (ann Σ).

Lemma fs_of_push : forall Σ k g f k', (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat -> (k' = 5 \/ k' = 0 \/ k' = 4 \/ k' = 1)%nat ->
  fs_of (fs_push Σ k g f) k' = if Nat.eqb k k' then g else fs_of Σ k'.
Proof. intros Σ k g f k' Hk Hk'. destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; destruct Hk' as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity. Qed.

Lemma nbusy_upd0to1 : forall (fl : list Z) i, (i < length fl)%nat -> nth i fl 1 = 0 -> nbusy (upd fl i 1%Z) = S (nbusy fl).
Proof.
  induction fl as [|z fl IH]; intros [|i] Hi Hn; cbn [length] in Hi; try lia; cbn [upd nbusy nth] in *.
  - subst z. cbn. reflexivity.
  - rewrite (IH i ltac:(lia) Hn). destruct (Z.eqb z 0); lia.
Qed.

Lemma filter_len_le : forall {X} (p : X -> bool) (l : list X), (length (List.filter p l) <= length l)%nat.
Proof. intros X p l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter length]. destruct (p x); cbn [length]; lia. Qed.

Ltac cls_norm := rewrite ?NF_5, ?NF_0, ?NF_4, ?NF_1, ?fsz_5, ?fsz_0, ?fsz_4, ?fsz_1 in *;
  try change (2 ^ 17) with 131072 in *; try change (2 ^ 20) with 1048576 in *;
  try change (2048 / 8) with 256 in *; try change (64 / 8) with 8 in *; try change (1024 / 8) with 128 in *;
  try change (128 / 8) with 16 in *; try change (1 * 131072) with 131072 in *; try change (1 * 1048576) with 1048576 in *.

Lemma frame_cls_range : forall FSB c p, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> 0 <= p < NF c ->
  FSB + 0x9000 + c * 2 ^ 20 <= frame_addr FSB c p /\ frame_addr FSB c p + fsz c <= FSB + 0x9000 + c * 2 ^ 20 + 2 ^ 20.
Proof. intros FSB c p Hc Hp. unfold frame_addr. destruct Hc as [ -> | [ -> | [ -> | -> ] ] ]; cls_norm; lia. Qed.

Lemma frames_apart_all : forall FSB c c' p q, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> (c' = 5 \/ c' = 0 \/ c' = 4 \/ c' = 1) ->
  0 <= p < NF c -> 0 <= q < NF c' -> (c <> c' \/ p <> q) ->
  frame_addr FSB c p + fsz c <= frame_addr FSB c' q \/ frame_addr FSB c' q + fsz c' <= frame_addr FSB c p.
Proof.
  intros FSB c c' p q Hc Hc' Hp Hq Hne. unfold frame_addr.
  destruct Hc as [ -> | [ -> | [ -> | -> ] ] ]; destruct Hc' as [ -> | [ -> | [ -> | -> ] ] ]; cls_norm; lia.
Qed.

Lemma shad_fsb_end : forall FSB, shad (FSB + 0xb09000) = shad FSB + 0x161200.
Proof. intros FSB. unfold shad. replace (FSB + 0xb09000) with (FSB + 0x161200 * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma frame_shad_in : forall FSB c p, FSB mod 4096 = 0 -> (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> 0 <= p < NF c ->
  shad FSB + 0x1200 + c * 2 ^ 17 <= shad (frame_addr FSB c p)
  /\ shad (frame_addr FSB c p) + fsz c / 8 <= shad FSB + 0x1200 + c * 2 ^ 17 + 2 ^ 17.
Proof.
  intros FSB c p HF Hc Hp. rewrite shad_frame by lia. unfold shad.
  destruct Hc as [ -> | [ -> | [ -> | -> ] ] ]; cls_norm; lia.
Qed.

Lemma frame_shad_in2 : forall FSB c p, FSB mod 4096 = 0 -> (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> 0 <= p < NF c ->
  shad FSB <= shad (frame_addr FSB c p) /\ shad (frame_addr FSB c p) + fsz c / 8 <= shad (FSB + 0xb09000).
Proof.
  intros FSB c p HF Hc Hp. pose proof (frame_shad_in FSB c p HF Hc Hp) as (S1 & S2). rewrite shad_fsb_end.
  destruct Hc as [ -> | [ -> | [ -> | -> ] ] ]; cls_norm; lia.
Qed.

Lemma frame_shads_apart_all : forall FSB c c' p q, FSB mod 4096 = 0 -> (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> (c' = 5 \/ c' = 0 \/ c' = 4 \/ c' = 1) ->
  0 <= p < NF c -> 0 <= q < NF c' -> (c <> c' \/ p <> q) ->
  shad (frame_addr FSB c p) + fsz c / 8 <= shad (frame_addr FSB c' q) \/ shad (frame_addr FSB c' q) + fsz c' / 8 <= shad (frame_addr FSB c p).
Proof.
  intros FSB c c' p q HF Hc Hc' Hp Hq Hne. rewrite !shad_frame by lia.
  destruct Hc as [ -> | [ -> | [ -> | -> ] ] ]; destruct Hc' as [ -> | [ -> | [ -> | -> ] ] ]; cls_norm; lia.
Qed.

Definition fs_room (k : nat) (fr : list (Z * nat)) : Prop :=
  Z.of_nat (length (List.filter (fun fk : Z * nat => Nat.eqb (snd fk) k) fr)) < fs_cap (Z.of_nat k) /\ Z.of_nat (length fr) < 4096.
Lemma cap_std : forall k (fr : list (Z * nat)), (k = 5 \/ k = 0 \/ k = 4)%nat -> (length fr < FRAMES_MAX)%nat -> fs_room k fr.
Proof.
  intros k fr Hk H. unfold FRAMES_MAX in H. unfold fs_room.
  pose proof (filter_len_le (fun fk : Z * nat => Nat.eqb (snd fk) k) fr) as LE. pose proof (fs_cap_ge (Z.of_nat k)). lia.
Qed.
Lemma cap_1 : forall (fr : list (Z * nat)), (length fr < 4096)%nat -> fs_room 1 fr.
Proof.
  intros fr H. unfold fs_room. change (fs_cap (Z.of_nat 1)) with 4096.
  pose proof (filter_len_le (fun fk : Z * nat => Nat.eqb (snd fk) 1%nat) fr) as LE. lia.
Qed.
Lemma cap_0w : forall (fr : list (Z * nat)),
  Z.of_nat (length (List.filter (fun fk : Z * nat => Nat.eqb (snd fk) 0%nat) fr)) < 2040 -> Z.of_nat (length fr) < 4096 -> fs_room 0 fr.
Proof. intros fr H1 H2. unfold fs_room. change (fs_cap (Z.of_nat 0)) with 2040. split; assumption. Qed.

Section Push.
Variables (Σ : rtsA) (m m' : mem) (k : nat) (j : Z) (usp lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat.
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation g := (fs_of Σ k).
#[local] Notation K := (Z.of_nat k).
#[local] Notation pos := ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)).
#[local] Notation f := (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))).
#[local] Notation g' := (mkFs (fss_hint (fs_of Σ k) + j + 1) (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)).
Hypothesis Hj : 0 <= j < NF K.
Hypothesis Hfree : nth (Z.to_nat pos) (fss_flags g) 1 = 0.
Hypothesis Hcr : 1 <= credit Σ.
Hypothesis Hlen : fs_room k (frames Σ).
Hypothesis Hlo : l_ACEIL L <= lo.
Hypothesis Husp : lo + 208 <= usp.
Hypothesis Husp2 : usp <= USTACK_TOP.
Hypothesis MU : munch (sm_W K FSB pos usp) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis P_hint : fs_hint FSB K m' (fss_hint g + j + 1).
Hypothesis P_const : fs_const FSB m'.
Hypothesis P_flags : fs_flags FSB K m' (upd (fss_flags g) (Z.to_nat pos) 1).
Hypothesis P_wr : wr_at asegs m' f (fsz K).
Hypothesis P_last : rw_cells asegs m' (f + fsz K - 8) [C8 (Z_to_bv 64 (fl_base FSB K + pos))].
Hypothesis P_sh : wr_at asegs m' (shad f) (fsz K / 8).
Hypothesis P_free : fs_free_frames FSB K m' (upd (fss_flags g) (Z.to_nat pos) 1).
Hypothesis P_gwf : gw = false.

Lemma push_cls : K = 5 \/ K = 0 \/ K = 4 \/ K = 1.
Proof using Hk. clear - Hk. destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; [left | right; left | right; right; left | right; right; right]; reflexivity. Qed.

Lemma push_pos : 0 <= pos < NF K.
Proof using Hk. clear - Hk. apply Z.mod_pos_bound. pose proof push_cls as Hc. unfold NF. destruct Hc as [E|[E|[E|E]]]; rewrite E; reflexivity. Qed.

Lemma push_flags_ok : flags_ok K (fss_flags g).
Proof.
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (F0 & F2 & F4 & Fc1 & _).
  destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 F4) | exact (proj1 Fc1)].
Qed.

Lemma push_wf : rt_wf (fs_push Σ k g' f).
Proof.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  pose proof W6 as (FW0 & FW2 & FW4 & FW1 & FWr & FND & FLN & FCNT & FHINT).
  pose proof push_cls as Hc. pose proof push_pos as Hp. pose proof push_flags_ok as (Hfl & Hfl01).
  assert (Hpl : (Z.to_nat pos < length (fss_flags g))%nat) by (apply Nat2Z.inj_lt; rewrite Hfl, Z2Nat.id by lia; lia).

  assert (Hnew : ~ In (f, k) (frames Σ)).
  { intros Hin. destruct (proj1 (Forall_forall _ _) FWr _ Hin) as (_ & p' & Hp' & Hf' & Hb'). cbn [fst snd] in *.
    apply (frame_addr_inj _ _ _ _ Hc) in Hf'. rewrite <- Hf' in Hb'. rewrite (nth_indep_Z _ _ 0 1 Hpl) in Hb'. congruence. }
  assert (Wg' : fs_cls_wf K g').
  { assert (Wg : fs_cls_wf K g) by (destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; assumption).
    destruct Wg as (_ & H1 & H2). split; [split|split]; cbn [fss_flags fss_hint].
    - rewrite upd_length. exact Hfl.
    - apply Forall_upd; [exact Hfl01 | right; reflexivity].
    - pose proof (FHINT k Hk) as X. destruct W7 as (B1 & _). assert (NF K <= 16384) by (unfold NF; destruct Hc as [E|[E|[E|E]]]; rewrite E; cbn; lia).
      unfold CREDIT0 in *. lia.
    - rewrite (nbusy_upd0to1 _ _ Hpl Hfree). pose proof (FCNT k Hk) as C. pose proof (proj1 Hlen) as HC.
      lia. }
  assert (NF8 : NF K <= 16384) by (unfold NF; destruct Hc as [E|[E|[E|E]]]; rewrite E; cbn; lia).
  unfold rt_wf. split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
  split; [|split; [|split; [exact W8|split; [change (dep_pot (d_n (dep Σ)) (Z.of_nat (length (live Σ))) (credit Σ - 1)); apply (dep_pot_mono _ _ _ _ W9); lia|split; [exact W10 | exact W11]]]]].
  -
    assert (CLS : forall k', (k' = 5 \/ k' = 0 \/ k' = 4 \/ k' = 1)%nat -> fs_cls_wf (Z.of_nat k') (fs_of (fs_push Σ k g' f) k')).
    { intros k' Hk'. rewrite (fs_of_push Σ k g' f k' Hk Hk'). destruct (Nat.eqb_spec k k') as [<-|Hne]; [exact Wg'|].
      destruct Hk' as [ -> | [ -> | [ -> | -> ] ] ]; assumption. }
    split; [exact (CLS 5%nat ltac:(lia))|]. split; [exact (CLS 0%nat ltac:(lia))|]. split; [exact (CLS 4%nat ltac:(lia))|]. split; [exact (CLS 1%nat ltac:(lia))|].
    split.
    { apply Forall_cons.
      - cbn [fst snd]. split; [exact Hk|]. exists pos. split; [exact Hp|]. split; [reflexivity|].
        rewrite (fs_of_push Σ k g' f k Hk Hk), Nat.eqb_refl. cbn [fss_flags]. apply nth_upd_same. exact Hpl.
      - apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & p2 & Hp2 & Hf2 & Hb2).
        cbn [fst snd] in *. split; [exact Hk2|]. exists p2. split; [exact Hp2|]. split; [exact Hf2|].
        rewrite (fs_of_push Σ k g' f k2 Hk Hk2). destruct (Nat.eqb_spec k k2) as [<-|Hne]; [|exact Hb2].
        cbn [fss_flags]. rewrite nth_upd_other; [exact Hb2|]. intros E.
        assert (p2 = pos) by (apply Z2Nat.inj; lia). subst p2. rewrite (nth_indep_Z _ _ 0 1 Hpl) in Hb2. congruence. }
    split; [apply NoDup_ListNoDup; constructor; [exact Hnew | apply NoDup_ListNoDup; exact FND]|].
    split; [cbn [frames fs_push length]; pose proof (proj2 Hlen); lia|].
    split.
    + intros k' Hk'. rewrite (fs_of_push Σ k g' f k' Hk Hk'). cbn [frames fs_push]. rewrite filter_cons_class. pose proof (FCNT k' Hk') as C.
      destruct (Nat.eqb_spec k k') as [<-|Hne]; cbn [fss_flags length].
      * rewrite (nbusy_upd0to1 _ _ Hpl Hfree). lia.
      * exact C.
    + intros k' Hk'. rewrite (fs_of_push Σ k g' f k' Hk Hk'). cbn [credit fs_push]. pose proof (FHINT k' Hk') as X.
      destruct (Nat.eqb_spec k k') as [<-|Hne]; cbn [fss_hint]; lia.
  -
    unfold budget_wf. cbn [credit aw fs_push]. destruct W7 as (B1 & B2 & B3 & B4 & B5). split; [lia|]. split; [exact B2|]. split; [lia|].
    split; [exact B4|]. unfold secsum in *. cbn [sec fs_push]. lia.
Qed.

Lemma push_bounds : 0 < FSB /\ FSB mod 4096 = 0 /\ SEGTOP_A <= FSB /\ FSB + 0xb09000 <= l_ACEIL L
  /\ SHB <= shad FSB /\ shad (FSB + 0xb09000) <= 2 ^ 44 + SHB /\ (FSB + 0xb09000 <= shad FSB \/ shad (FSB + 0xb09000) <= FSB)
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L + STACK_WIN <= USTACK_TOP.
Proof using HA.
  clear - HA.
  pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof (rta_sp0_range Σ m HA) as Hr. pose proof (rta_sp0_win Σ m HA) as Hw.
  assert (S0 : SHB <= shad FSB) by (unfold shad; pose proof (Z.div_pos FSB 8 ltac:(lia) ltac:(lia)); lia).
  assert (S1 : shad (FSB + 0xb09000) <= 2 ^ 44 + SHB).
  { unfold shad. assert ((FSB + 0xb09000) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia). lia. }
  split; [exact G1|]. split; [exact G2|]. split; [destruct G5 as [G5|G5]; [lia | exact G5]|]. split; [exact G3|].
  split; [exact S0|]. split; [exact S1|].
  split; [destruct G4 as [G4|G4]; [left | right]; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  unfold l_ACEIL, rtA_sp0, SHB, USTACK_TOP, STACK_WIN in *. lia.
Qed.

Lemma push_pieces :
  FSB + 8 * K + 8 <= FSB + 0x1000 /\ FSB + 0x1000 <= fl_base FSB K + pos /\ fl_base FSB K + pos + 1 <= FSB + 0x9000
  /\ FSB + 0x9000 <= f /\ f + fsz K <= FSB + 0xb09000
  /\ shad FSB <= shad f /\ shad f + fsz K / 8 <= shad (FSB + 0xb09000)
  /\ l_ACEIL L <= usp - 208.
Proof.
  pose proof push_cls as Hc. pose proof push_pos as Hp. pose proof push_bounds as (B1 & B2 & _).
  pose proof (frame_addr_range FSB K pos Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2. pose proof (flags_range _ Hc) as (F1 & F2).
  pose proof (frame_shad_in FSB K pos B2 Hc Hp) as (S1 & S2). rewrite shad_fsb_end.
  unfold fl_base. destruct Hc as [E|[E|[E|E]]]; rewrite E in *; cbn in *; lia.
Qed.

Lemma dw_gen : forall a n, (a + n <= FSB \/ FSB + 0xb09000 <= a) -> (a + n <= shad FSB \/ shad (FSB + 0xb09000) <= a) ->
  (a + n <= l_ACEIL L \/ usp <= a) -> disjoint_from (sm_W K FSB pos usp) a n.
Proof.
  intros a n H1 H2 H3. pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_cls as Hc.
  unfold sm_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dw_hint : forall c, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> c <> K -> disjoint_from (sm_W K FSB pos usp) (FSB + 8 * c) 8.
Proof.
  intros c Hc' Hne. pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_cls as Hc.
  pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  unfold sm_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dw_flags : forall c, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> c <> K -> disjoint_from (sm_W K FSB pos usp) (fl_base FSB c) (NF c).
Proof.
  intros c Hc' Hne. pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_cls as Hc. pose proof push_pos as Hp.
  pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (flags_range _ Hc') as (F1 & F2). pose proof (flags_apart _ _ Hc Hc' (not_eq_sym Hne)) as FA.
  unfold sm_W. cbn [disjoint_from]. unfold fl_base in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dw_oflags : forall c, In c OCLS -> disjoint_from (sm_W K FSB pos usp) (fl_base FSB c) (NF c).
Proof.
  intros c Hc'. pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_cls as Hc. pose proof push_pos as Hp.
  pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (oflags_range _ Hc') as (F1 & F2 & F3). pose proof (oflags_apart_flags FSB c K Hc' Hc) as FA. pose proof (flags_range _ Hc) as (G1 & G2).
  unfold sm_W. cbn [disjoint_from]. unfold fl_base in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.
Lemma push_ofl : fs_oflags_zero FSB m'.
Proof.
  pose proof (ART_fs Σ m HA) as ((_ & O) & _).
  exact (fs_oflags_zero_transport _ FSB m m' O MU WM dw_oflags).
Qed.
Lemma dw_frame : forall c q, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1) -> 0 <= q < NF c -> (c <> K \/ q <> pos) ->
  disjoint_from (sm_W K FSB pos usp) (frame_addr FSB c q) (fsz c)
  /\ disjoint_from (sm_W K FSB pos usp) (shad (frame_addr FSB c q)) (fsz c / 8).
Proof.
  intros c q Hc' Hq Hne. pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_cls as Hc. pose proof push_pos as Hp.
  pose proof push_bounds as (_ & B2 & _ & B4 & _ & B6 & B7 & B8 & _).
  pose proof (frame_addr_range FSB c q Hc' Hq) as (R1 & R2). unfold kFakeStackSize in R2.
  pose proof (frame_shad_in2 FSB c q B2 Hc' Hq) as (S1 & S2).
  pose proof (frames_apart_all FSB c K q pos Hc' Hc Hq Hp Hne) as FA.
  pose proof (frame_shads_apart_all FSB c K q pos B2 Hc' Hc Hq Hp Hne) as SA.
  assert (Z8 : 0 <= fsz c / 8) by (apply Z.div_pos; [unfold fsz; pose proof (Z.pow_nonneg 2 c ltac:(destruct Hc' as [E|[E|[E|E]]]; lia)); lia | lia]).
  assert (Z8' : 0 <= fsz K / 8) by (apply Z.div_pos; [unfold fsz; pose proof (Z.pow_nonneg 2 K ltac:(lia)); lia | lia]).
  assert (Z0 : 0 <= fsz c) by (unfold fsz; pose proof (Z.pow_nonneg 2 c ltac:(destruct Hc' as [E|[E|[E|E]]]; lia)); lia).
  unfold sm_W. cbn [disjoint_from].
  set (a := frame_addr FSB c q) in *. set (sa := shad a) in *. set (fc := fsz c) in *. set (fk := fsz K) in *.
  split.
  - split; [clear - R1 P1; lia|]. split; [clear - R1 P3; lia|]. split; [clear - FA; lia|].
    split; [clear - B7 R1 R2 P6 P7 Z8'; lia|]. split; [clear - R2 B4 P8; lia | exact I].
  - split; [clear - B7 S1 S2 P1 Z8; lia|]. split; [clear - B7 S1 S2 P2 P3 Z8; lia|]. split; [clear - B7 S1 S2 P4 P5 Z8; lia|].
    split; [clear - SA; lia|]. split; [clear - S2 B6 B8 P8; lia | exact I].
Qed.

Lemma push_munch : munch ([(FSB, FSB + 0xb09000)] ++ [(shad FSB, shad (FSB + 0xb09000))] ++ [(l_ACEIL L, USTACK_TOP)]) m m'.
Proof.
  pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_cls as Hc.
  apply (munch_weaken (sm_W K FSB pos usp)); [|exact MU].
  intros x Hx. cbn in Hx. destruct Hx as (X1 & X2 & X3 & _). unfold sm_W. cbn [outside].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dw_grant : forall i b gn a n, (i <> 5)%nat -> nth_error (startup_grants L) i = Some (b, gn) -> b <= a -> a + n <= b + gn ->
  disjoint_from (sm_W K FSB pos usp) a n.
Proof.
  intros i b gn a n Hi Hn H1 H2. pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  assert (Hin : In (b, gn) (startup_grants L)) by (eapply nth_error_In; exact Hn).
  pose proof (geo_grant Σ m HA b gn Hin) as (G1 & G2 & G3 & G4 & G5).
  assert (AP : apart b gn FSB 0xb09000).
  { destruct (Nat.lt_ge_cases i 5) as [Hl|Hl].
    - exact (geo_apart Σ m HA i 5 _ _ Hl Hn eq_refl).
    - pose proof (geo_apart Σ m HA 5 i _ _ ltac:(lia) eq_refl Hn) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold apart in AP. apply dw_gen; [lia | unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | lia].
Qed.

Lemma push_fs_rep : fs_rep (fs_push Σ k g' f) m'.
Proof.
  pose proof push_ofl as POFL.
  pose proof push_cls as Hc. pose proof push_pos as Hp. pose proof push_flags_ok as (Hfl & _).
  pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _).
  pose proof (ART_fs Σ m HA) as FS.
  destruct FS as (F1 & _ & _ & _ & _ & FT & (dtvbeg & Hdb & TG) & (tb & te & TT) & FB).

  assert (CLSo : forall c, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1)%nat -> c <> k -> fs_cls_rep FSB (Z.of_nat c) (fs_of Σ c) m').
  { intros c Hcc Hne. pose proof (fs_rep_cls Σ m c (ART_fs Σ m HA) Hcc) as X.
    assert (Hc2 : Z.of_nat c = 5 \/ Z.of_nat c = 0 \/ Z.of_nat c = 4 \/ Z.of_nat c = 1) by (destruct Hcc as [ -> | [ -> | [ -> | -> ] ] ]; cbn; lia).
    assert (HcK : Z.of_nat c <> K) by lia.
    assert (Lc : Z.of_nat (length (fss_flags (fs_of Σ c))) = NF (Z.of_nat c)).
    { destruct HFw as (F0 & F2 & F4 & Fc1 & _).
      destruct Hcc as [ -> | [ -> | [ -> | -> ] ] ]; [exact (proj1 (proj1 F0)) | exact (proj1 (proj1 F2)) | exact (proj1 (proj1 F4)) | exact (proj1 (proj1 Fc1))]. }
    apply (fs_cls_rep_transport _ _ _ _ m m' X MU WM). split; [|split].
    - exact (dw_hint _ Hc2 HcK).
    - rewrite Lc. exact (dw_flags _ Hc2 HcK).
    - intros q Hq _. exact (dw_frame _ q Hc2 Hq (or_introl HcK)). }

  assert (CLSk : fs_cls_rep FSB K g' m') by (split; [exact P_hint | split; [exact P_flags | exact P_free]]).
  assert (DIMG : forall a n, a + n <= SEGTOP_A -> disjoint_from (sm_W K FSB pos usp) a n).
  { intros a n H. apply dw_gen; [lia | unfold SHB, SEGTOP_A in *; lia | lia]. }
  assert (T' : rw_cells asegs m' tpA [C8 (Z_to_bv 64 FSB)]).
  { apply (rw_cells_transport asegs _ m m' _ _ FT MU WM). apply DIMG. unfold tpA, SEGTOP_A. cbn. lia. }
  assert (TG' : tga_cells (l_DTV L) dtvbeg m').
  { unfold tga_cells, dtls_cells in *. destruct TG as (G1' & G2' & G3' & G4' & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)).
    repeat (split; [eapply (rw_cells_transport asegs _ m m'); [eassumption | exact MU | exact WM | apply DIMG;
                      unfold g_real_tls_get_addr, g_dtv_ptr, g_dtv1, g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity,
                        g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; cbn; lia]|]).
    apply (rw_cells_transport asegs _ m m' _ _ D8 MU WM). cbn [cells_size csize Nat.add].
    apply (dw_grant 4%nat (l_DTV L) 4096); [lia | reflexivity | lia | lia]. }
  assert (TT' : ttls_cells (l_T L) m' tb te).
  { unfold ttls_cells in *. apply (rw_cells_transport asegs _ m m' _ _ TT MU WM). cbn [cells_size csize Nat.add].
    apply (dw_grant 2%nat (l_T L) 4096); [lia | reflexivity | lia | lia]. }

  assert (FB' : fs_busy L ((f, k) :: frames Σ) m').
  { apply Forall_cons.
    - exists pos. cbn [fst snd]. rewrite fs_size_fsz. split; [reflexivity|]. split; [exact P_wr|]. split; [exact P_sh | exact P_last].
    - apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FB (f2, k2) Hin) as (q & Hq & Wq1 & Wq2 & Cq).
      destruct (busy_slot Σ m HA f2 k2 Hin) as (Hk2 & q' & Hq' & Hf2 & Hb2). cbn [fst snd] in *.
      exists q. split; [exact Hq|]. split; [exact (wr_at_wmono m m' _ _ Wq1 WM)|]. split; [exact (wr_at_wmono m m' _ _ Wq2 WM)|].
      apply (rw_cells_transport asegs _ m m' _ _ Cq MU WM). cbn [cells_size csize Nat.add].
      assert (Hc2 : Z.of_nat k2 = 5 \/ Z.of_nat k2 = 0 \/ Z.of_nat k2 = 4 \/ Z.of_nat k2 = 1) by (destruct Hk2 as [ -> | [ -> | [ -> | -> ] ] ]; cbn; lia).
      assert (Hne : Z.of_nat k2 <> K \/ q' <> pos).
      { destruct (Nat.eq_dec k2 k) as [->|Hne]; [right | left; lia]. intros ->.
        assert (Hpl : (Z.to_nat pos < length (fss_flags g))%nat) by (apply Nat2Z.inj_lt; rewrite Hfl, Z2Nat.id by lia; lia).
        rewrite (nth_indep_Z _ _ 0 1 Hpl) in Hb2. congruence. }
      destruct (dw_frame _ q' Hc2 Hq' Hne) as (D1 & _). rewrite <- Hf2 in D1. rewrite fs_size_fsz.
      assert (8 <= fsz (Z.of_nat k2)) by (unfold fsz; destruct Hc2 as [E|[E|[E|E]]]; rewrite E; cbn; lia).
      apply (dsj_sub _ f2 (fsz (Z.of_nat k2))); [exact D1 | lia | lia]. }
  unfold fs_rep. cbn [lay fs_push frames].
  destruct Hk as [E|[E|[E|E]]]; subst k; cbn [fs0 fsc0 fs4 fs1 fs_push];
    (split; [exact (fs_gstate_of_const _ _ _ _ ltac:(intros X; rewrite P_gwf in X; discriminate X) P_const POFL)|]); (split; [first [exact CLSk | exact (CLSo 5%nat ltac:(lia) ltac:(lia))]|]);
    (split; [first [exact CLSk | exact (CLSo 0%nat ltac:(lia) ltac:(lia))]|]);
    (split; [first [exact CLSk | exact (CLSo 4%nat ltac:(lia) ltac:(lia))]|]);
    (split; [first [exact CLSk | exact (CLSo 1%nat ltac:(lia) ltac:(lia))]|]);
    (split; [exact T'|]); (split; [exists dtvbeg; split; [exact Hdb | exact TG']|]); (split; [exists tb, te; exact TT' | exact FB']).
Qed.

Theorem push_art : ART_A (fs_push Σ k g' f) m'.
Proof.
  pose proof (ART_transport_but_fs _ Σ m m' HA push_munch WM
     (art_avoid_but_fs_app _ _ Σ (fsb_avoid Σ m HA) (art_avoid_but_fs_app _ _ Σ (fshad_avoid Σ m HA) (stack_avoid Σ m HA)))) as BF.
  exact (ART_of_but_fs _ m' push_wf BF push_fs_rep).
Qed.

Lemma push_pres : rt_pres (live Σ) (frames Σ) usp m m'.
Proof.
  intros a Ha. apply MU. set (x := bv_unsigned a) in *.
  pose proof push_pieces as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof push_pos as Hp.
  pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). pose proof push_flags_ok as (Hfl & _).
  pose proof (art_avoid_client Σ m usp HA ltac:(unfold l_ACEIL in Hlo; unfold rtA_sp0; lia)) as (_ & _ & _ & _ & _ & _ & _ & AF & _).
  destruct AF as (_ & A0 & A2 & A4 & A1 & _).
  assert (AK : fs_cls_avoid (W_client Σ usp) FSB K g) by (destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; assumption).
  destruct AK as (AK1 & AK2 & AK3). destruct (AK3 pos Hp Hfree) as (AK4 & AK5). rewrite Hfl in AK2.
  assert (STK : disjoint_from (W_client Σ usp) (usp - 208) 208).
  { apply avoid_client_intro; [lia | apply dsj_CS_out; right; unfold l_ACEIL, STACK_WIN, SEGTOP_A in *; lia | | |].
    - apply Forall_forall. intros [p n] Hin. destruct (rta_live_range Σ m p n HA Hin) as (_ & X & _). cbn [fst snd].
      unfold l_ACEIL, rtA_sp0 in *. lia.
    - apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ m HA f2 k2 Hin) as (_ & X & _). cbn [fst snd].
      unfold l_ACEIL, rtA_sp0 in *. lia.
    - apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ m HA f2 k2 Hin) as (X0 & X & _). cbn [fst snd].
      assert (shad (f2 + fs_size k2) <= 2 ^ 44 + SHB).
      { unfold shad. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
      right. unfold l_ACEIL, rtA_sp0 in *. lia. }
  pose proof (W_client_cover Σ usp x Ha) as NO.
  unfold sm_W. cbn [outside].
  split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK1); lia|].
  split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK2); unfold fl_base in *; lia|].
  split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK4); lia|].
  split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK5); lia|].
  split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ STK); lia | exact I].
Qed.

Lemma push_f : 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP.
Proof using HA Hk.
  clear - HA Hk.
  pose proof push_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). pose proof push_cls as Hc. pose proof push_pos as Hp.
  pose proof (frame_addr_range FSB K pos Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2. rewrite fs_size_fsz.
  split; [lia|]. split; [|unfold STACK_WIN, USTACK_TOP in *; lia].
  apply Z.mod_divide; [lia|]. unfold frame_addr. apply Z.divide_add_r; [apply Z.divide_add_r; [apply Z.divide_add_r|]|].
  - apply Z.mod_divide in B2; [|lia]. apply (Z.divide_trans 64 4096); [exists 64; reflexivity | exact B2].
  - exists 576. reflexivity.
  - exists (K * 2 ^ 14). change (2 ^ 20) with (2 ^ 14 * 64). ring.
  - apply Z.divide_mul_r. unfold fsz. exists (2 ^ K). ring.
Qed.

Theorem push_post : ART_A (fs_push Σ k g' f) m' /\ rt_pres (live Σ) (frames Σ) usp m m'
  /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8).
Proof.
  pose proof push_cls as Hc. rewrite fs_size_fsz.
  assert (Z8 : 8 <= fsz K) by (unfold fsz; destruct Hc as [E|[E|[E|E]]]; rewrite E; cbn; lia).
  split; [exact push_art|]. split; [exact push_pres|]. split; [|exact P_sh].
  destruct P_wr as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
Qed.

End Push.

Lemma rw_cells_app_r : forall (m : mem) a cs1 cs2, rw_cells asegs m a (cs1 ++ cs2) -> rw_cells asegs m (a + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m a cs1 cs2 [[Hw Hb] W]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb2].
  apply cells_wf_app in Hw as [Hw1 Hw2]. rewrite cells_bytes_length in Hb2 by exact Hw1.
  split; [split; [exact Hw2 | exact Hb2]|].
  rewrite cells_size_app, Nat2Z.inj_add in W. destruct W as (W0 & W1 & W2).
  split; [lia|]. split; [lia|]. intros i Hi. replace (a + Z.of_nat (cells_size cs1) + i) with (a + (Z.of_nat (cells_size cs1) + i)) by lia.
  apply W2. lia.
Qed.

Lemma rw_cells_wrat : forall (m : mem) A cs n, rw_cells asegs m A cs -> n <= Z.of_nat (cells_size cs) -> wr_at asegs m A n.
Proof. intros m A cs n [_ (H0 & H1 & H)] Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma rw_cells_last : forall (m : mem) a n1 j1 (x : word) n2 j2 (y : word) sz, Z.of_nat n1 + 8 + Z.of_nat n2 + 8 = sz ->
  rw_cells asegs m a [CB n1 j1; C8 x; CB n2 j2; C8 y] -> rw_cells asegs m (a + sz - 8) [C8 y].
Proof.
  intros m a n1 j1 x n2 j2 y sz Hsz H. pose proof (rw_cells_app_r m a [CB n1 j1; C8 x; CB n2 j2] [C8 y] H) as X.
  cbn [cells_size csize] in X. replace (a + sz - 8) with (a + Z.of_nat (n1 + (8 + (n2 + 0)))) by lia. exact X.
Qed.

Lemma sm_pre : forall Σ m k lo, ART_A Σ m -> (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat -> rtA_sp0 Σ - STACK_WIN <= lo ->
  fs_gstate (frames Σ) (gcredit Σ) (l_FSB (lay Σ)) m /\ fs_hint (l_FSB (lay Σ)) (Z.of_nat k) m (fss_hint (fs_of Σ k))
  /\ fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m (fss_flags (fs_of Σ k)) /\ flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))
  /\ Z.of_nat (nbusy (fss_flags (fs_of Σ k))) <= fs_cap (Z.of_nat k) /\ 0 <= fss_hint (fs_of Σ k) < 2 ^ 61
  /\ fs_free_frames (l_FSB (lay Σ)) (Z.of_nat k) m (fss_flags (fs_of Σ k)) /\ rw_cells asegs m tpA [C8 (Z_to_bv 64 (l_FSB (lay Σ)))]
  /\ (exists dtvbeg, 0 < dtvbeg < 2 ^ 64 /\ tga_cells (l_DTV (lay Σ)) dtvbeg m) /\ thread_cells (l_TCX (lay Σ)) (l_T (lay Σ)) m
  /\ (exists tb te, ttls_cells (l_T (lay Σ)) m tb te) /\ m2s_cells m /\ FSB_ok2 (l_FSB (lay Σ)) /\ 0x10007fff8000 <= lo
  /\ l_FSB (lay Σ) + kFakeStackSize <= lo
  /\ 0 < l_DTV (lay Σ) /\ l_DTV (lay Σ) + 4096 <= lo /\ 0 < l_TCX (lay Σ) /\ l_TCX (lay Σ) + 0xa0 <= lo
  /\ 0 < l_T (lay Σ) /\ l_T (lay Σ) + 4096 <= lo.
Proof.
  intros Σ m k lo HA Hk Hlo.
  pose proof (ART_fs Σ m HA) as FS. destruct FS as (F1 & _ & _ & _ & _ & FT & TG & TT & _).
  pose proof (fs_rep_cls Σ m k (ART_fs Σ m HA) Hk) as (CH & CF & CFr).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (F0 & F2 & F4 & Fc1 & _).
  assert (Wk : fs_cls_wf (Z.of_nat k) (fs_of Σ k)) by (destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; assumption).
  destruct Wk as (OK & HH & NB).
  pose proof (ART_consts Σ m HA) as (_ & _ & TC & M2S & _).
  pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & G5).
  pose proof (rta_sp0_win Σ m HA) as Hw. pose proof (rta_sp0_range Σ m HA) as Hr.
  pose proof (geo_grant Σ m HA (l_DTV (lay Σ)) 4096 ltac:(unfold startup_grants; do 4 right; left; reflexivity)) as (D1 & _ & D3 & _).
  pose proof (geo_grant Σ m HA (l_TCX (lay Σ)) 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (X1 & _ & X3 & _).
  pose proof (geo_grant Σ m HA (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (T1 & _ & T3 & _).
  unfold l_ACEIL, rtA_sp0 in *.
  split; [exact F1|]. split; [exact CH|]. split; [exact CF|]. split; [exact OK|]. split; [exact NB|]. split; [exact HH|].
  split; [exact CFr|]. split; [exact FT|]. split; [exact TG|]. split; [exact TC|]. split; [exact TT|]. split; [exact M2S|].
  split.
  { unfold FSB_ok2, kFakeStackSize, kHighShadowEnd. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A, STACK_WIN, USTACK_TOP in *.
    split; [lia|]. split; [lia|]. split; [lia | exact G2]. }
  unfold kFakeStackSize, STACK_WIN in *. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

Lemma sm_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

End GWIN.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.

Definition smgc_case (k : nat) : Prop :=
  forall (Σ : rts RTA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 4 \/ k = 5)%nat -> tp = Z_to_bv 64 0x6a7e68 ->
  (length (rt_frames RTA Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RTA Σ ->
  ART RTA Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo ->
  fs_constg (l_FSB (lay Σ)) true m -> rt_frames RTA Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RTA Σ ->
  cps asegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RTA) (f : Z),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RTA Σ' = (f, k) :: rt_frames RTA Σ /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).
Definition smgc_stmt : Prop := forall k, smgc_case k.

Lemma sm_finish : forall (Σ : rtsA) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (k : nat) (j lo : Z) (fc : bv 32)
    (Pm : machine_state -> Prop) c1,
  ART_A Σ m -> (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat -> 0 <= j < NF (Z.of_nat k) ->
  nth (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fss_flags (fs_of Σ k)) 1 = 0 ->
  1 <= credit Σ -> fs_room k (frames Σ) ->
  rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
  (forall ms, Pm ms -> exists m',
     ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       (Z_to_bv 64 (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))) m' ms
     /\ munch (sm_W (Z.of_nat k) (l_FSB (lay Σ)) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) (bv_unsigned sp)) m m'
     /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     /\ fs_hint (l_FSB (lay Σ)) (Z.of_nat k) m' (fss_hint (fs_of Σ k) + j + 1) /\ fs_const (l_FSB (lay Σ)) m'
     /\ fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m'
          (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)
     /\ wr_at asegs m' (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) (fsz (Z.of_nat k))
     /\ rw_cells asegs m' (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) + fsz (Z.of_nat k) - 8)
          [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + (fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)))]
     /\ wr_at asegs m' (shad (frame_addr (l_FSB (lay Σ)) (Z.of_nat k) ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))))
          (fsz (Z.of_nat k) / 8)
     /\ fs_free_frames (l_FSB (lay Σ)) (Z.of_nat k) m'
          (upd (fss_flags (fs_of Σ k)) (Z.to_nat ((fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k))) 1)) ->
  exists (Σ' : rts RTA) (f : Z),
       ASTA RTA Σ' PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c1
       /\ rt_frames RTA Σ' = (f, k) :: rt_frames RTA Σ /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
       /\ rt_credit RTA Σ' = rt_credit RTA Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP.
Proof.
  intros Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m k j lo fc Pm c1 HA Hk Hj Hfree Hcr Hlen LOW LOR SPT HAST HPm.
  set (FSB := l_FSB (lay Σ)) in *. set (pos := (fss_hint (fs_of Σ k) + j) mod NF (Z.of_nat k)) in *.
  set (f := frame_addr FSB (Z.of_nat k) pos) in *.
  set (g' := mkFs (fss_hint (fs_of Σ k) + j + 1) (upd (fss_flags (fs_of Σ k)) (Z.to_nat pos) 1)).
  set (usp := bv_unsigned sp) in *.
  assert (Hlo : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; unfold rtA_sp0 in LOW; lia).
  assert (Husp : lo + 208 <= usp) by (unfold RT_STACK in LOR; lia).
  assert (Husp2 : usp <= USTACK_TOP) by lia.
  exists (fs_push Σ k g' f), f.
  pose proof (push_f Σ m k j HA Hk) as (F1 & F2 & F3).
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity | exact (conj F1 (conj F2 F3))]]]]].
  unfold ASTA. change (rt_allow RTA (fs_push Σ k g' f)) with (rtA_allow Σ).
  eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
  intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & P1 & P2 & P3 & P4 & P5 & P6 & P7).
  destruct (push_post Σ m m' k j usp lo HA Hk Hj Hfree Hcr Hlen Hlo Husp Husp2 MU WM P1 P2 P3 P4 P5 P6 P7 eq_refl) as (ART' & PRES & WR1 & WR2).
  exists m'. split; [exact RS|]. split; [split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]]|].
  split; [exact (rt_pres_vis _ _ _ _ _ _ PRES)|]. split; [exact WR1 | exact WR2].
Qed.

Section GC.
Hypothesis SMGC : smgc_stmt.
Theorem rta_stack_malloc_4 : stack_malloc_contract RTA 4.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST Hk -> Hlen Hcr ART0 MI0 CALL TOPC.
  intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  destruct (sm_pre Σ m 4%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
    & M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
  destruct FC as ((gflag & FC & GNIL & GCR) & OFL).
  destruct gflag.
  {
    exact (SMGC 4%nat Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             FDO MST Hk eq_refl Hlen Hcr ART0 MI0 CALL FC (GNIL eq_refl eq_refl) (TOPC (GNIL eq_refl eq_refl)) T cf Hc Hkont). }
  apply fs_constg_false in FC.
  assert (W1 : evt asegs (sm4_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) (fss_hint (fs_of Σ 4))
                            (fss_flags (fs_of Σ 4)) lo m)
                 (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc (e_stack_malloc 4) m)).
  { unfold entry_st.
    exact (stack_malloc_4_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      (l_FSB (lay Σ)) (fss_hint (fs_of Σ 4)) (fss_flags (fs_of Σ 4)) (l_DTV (lay Σ)) dtvbeg (l_TCX (lay Σ)) (l_T (lay Σ)) lo tb te
      FC FH FL OK ltac:(change (fs_cap (Z.of_nat 4)) with 16 in NB; lia) HH FF TLS TGA TC TT M2S FSOK HLO FSL HD HDL Hdb HX HXL HT HTL ST
      ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hkont. unfold sm4_post in Hc1.
  apply AST_exI in Hc1 as (jn & Hc2).
  assert (PURE : (jn < 1024)%nat /\ nth (Z.to_nat ((fss_hint (fs_of Σ 4) + Z.of_nat jn) mod 1024)) (fss_flags (fs_of Σ 4)) 1 = 0).
  { destruct Hc2 as (_ & HP & _).
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & Hfree & _).
    split; assumption. }
  destruct PURE as (Hj & Hfree).
  apply (sm_finish Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m 4%nat (Z.of_nat jn) lo fc _ c1 ART0 ltac:(lia)
           ltac:(change (NF (Z.of_nat 4)) with 1024; lia) Hfree Hcr (cap_std 4%nat _ ltac:(lia) Hlen) LOW LOR SPT Hc2).
  intros ms HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & junk1 & junk2 & -> & MU & WM & MI
    & ST' & _ & _ & PH & PC & PF & FR & SH & PFr).
  exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact PH|]. split; [exact PC|]. split; [exact PF|].
  split; [exact (rw_cells_wrat m' _ _ _ FR (Z.le_refl _))|].
  split; [exact (rw_cells_last m' _ 24 junk1 sp 984 junk2 _ (fsz (Z.of_nat 4)) eq_refl FR)|].
  split; [exact (rw_cells_wrat m' _ _ _ SH (Z.le_refl _)) | exact PFr].
Qed.
End GC.

