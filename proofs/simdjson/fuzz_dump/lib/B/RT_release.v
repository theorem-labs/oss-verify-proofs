(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_thread RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit RT_facts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Section FsbSep.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation WF := [(l_FSB (lay Σ), l_FSB (lay Σ) + 0xb09000)].

Lemma fsb_grant : grant_ok L (l_FSB L) 0xb09000.
Proof. exact (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)). Qed.

Lemma rf_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from WF a n.
Proof. intros a n H1 H2 _. pose proof fsb_grant as (G1 & _ & _ & _ & G5). cbn. split; [|exact I]. unfold SEGTOP_A in *. lia. Qed.

Lemma rf_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from WF a n.
Proof. intros b gn a n _ _ HF H1 H2. cbn. split; [|exact I]. unfold apart in HF. lia. Qed.

Lemma rf_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) -> disjoint_from WF a n.
Proof.
  intros lo hi a n _ _ H0 H47 H1 H2 _. pose proof fsb_grant as (_ & _ & _ & G4 & _). cbn. split; [|exact I].
  assert (Hs : shad hi <= 2 ^ 44 + SHB) by (unfold shad; assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (Hs0 : SHB <= shad lo) by (unfold shad; pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)); lia).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Lemma rf_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from WF a n.
Proof.
  intros a n H1 H2 _. pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha.
  cbn. split; [|exact I]. unfold apart in Ha. lia.
Qed.

Lemma rf_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from WF a n.
Proof.
  intros k0 s0 a n Hk H1 H2 _. destruct (map_geo Σ m HA k0 s0 Hk) as (_ & _ & Hf & _). cbn. split; [|exact I]. unfold apart in Hf. lia.
Qed.

Theorem fsb_avoid : art_avoid_but_fs WF Σ.
Proof. exact (art_avoid_gen Σ m WF HA rf_img rf_grant (fun lo hi a n H1 H2 H3 H4 H5 H6 H7 _ => rf_shad lo hi a n H1 H2 H3 H4 H5 H6 H7) rf_prb rf_secmap). Qed.

End FsbSep.

Definition ART_but_fs (Σ : rtsA) (m : mem) : Prop :=
  consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m /\ chunk_rep Σ m /\ sec_rep Σ m /\ quar_rep Σ m
  /\ dep_rep (lay Σ) (dep Σ) m /\ ia_rep Σ m /\ shadow_rep (lay Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

Lemma ART_transport_but_fs : forall W Σ (m m' : mem), ART_A Σ m -> munch W m m' -> wmono bsegs m m' -> art_avoid_but_fs W Σ ->
  ART_but_fs Σ m'.
Proof.
  intros W Σ m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A9 & A10).
  pose proof (ART_wf Σ m H) as Hwf.
  split; [exact (consts_rep_transport W _ m m' (ART_consts Σ m H) MU WM A1)|].
  split; [intros c Hc; exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m H c Hc) MU WM (proj1 (A2 c Hc)))|].
  split; [intros c Hc; exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m H c Hc) MU WM (proj2 (A2 c Hc)))|].
  split; [destruct (ART_chunk Σ m H) as [P S]; split;
          [intros c i st Hc Hn; exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (A3 c i st Hc Hn))
          | intros k s Hk; exact (schunk_transport W k s m m' (S k s Hk) MU WM (A4 k s Hk))]|].
  split; [exact (sec_rep_transport W Σ m m' (ART_sec Σ m H) MU WM A5)|].
  split; [exact (quar_rep_transport W Σ m m' (ART_quar Σ m H) MU WM A6)|].
  split; [destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _); exact (dep_rep_transport W _ _ m m' (ART_dep Σ m H) Hdok MU WM A7)|].
  split; [exact (ia_rep_transport W Σ m m' (ART_ia Σ m H) MU WM A9)|].
  split; [exact (shadow_rep_transport W _ m m' (ART_shadow Σ m H) MU WM A10)|].
  exact (vis_rep_wmono _ m m' (ART_vis Σ m H) WM).
Qed.

Lemma ART_of_but_fs : forall Σ m, rt_wf Σ -> ART_but_fs Σ m -> fs_rep Σ m -> ART_A Σ m.
Proof.
  intros Σ m Hw (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C9 & C10 & C11) C8. exact (ART_intro Σ m Hw C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11).
Qed.

Definition fs_set (Σ : rtsA) (k : nat) (f : fsst) (fr : list (Z * nat)) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (match k with 5%nat => f | _ => fs0 Σ end) (match k with 0%nat => f | _ => fsc0 Σ end)
    (match k with 5%nat | 0%nat | 1%nat | 3%nat | 2%nat => fs4 Σ | _ => f end) (match k with 1%nat => f | _ => fs1 Σ end) (match k with 3%nat => f | _ => fs3 Σ end) (match k with 2%nat => f | _ => fs2 Σ end) (ia_init Σ) (credit Σ) (live Σ) fr (ann Σ).

Definition fs_release (Σ : rtsA) (k : nat) (p : Z) (fr : list (Z * nat)) : rtsA :=
  fs_set Σ k (mkFs (fss_hint (fs_of Σ k)) (upd (fss_flags (fs_of Σ k)) (Z.to_nat p) 0)) fr.

Lemma fs_of_set : forall Σ k f fr k', (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat -> (k' = 5 \/ k' = 0 \/ k' = 4 \/ k' = 1 \/ k' = 3 \/ k' = 2)%nat ->
  fs_of (fs_set Σ k f fr) k' = if Nat.eqb k k' then f else fs_of Σ k'.
Proof. intros Σ k f fr k' Hk Hk'. destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; destruct Hk' as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; reflexivity. Qed.

Lemma nbusy_upd0 : forall (fl : list Z) i, (nbusy (upd fl i 0%Z) <= nbusy fl)%nat.
Proof.
  induction fl as [|z fl IH]; intros [|i]; cbn [upd nbusy]; [lia | lia | |].
  - destruct (Z.eqb z 0); cbn; lia.
  - specialize (IH i). destruct (Z.eqb z 0); lia.
Qed.

Lemma nth_upd_other : forall (l : list Z) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof.
  intros l i j x d Hij. destruct (Nat.lt_ge_cases j (length l)) as [Hl|Hl].
  - assert (E : nth_error (upd l i x) j = nth_error l j) by (apply nth_error_upd_other; exact Hij).
    rewrite (nth_error_nth' l d Hl) in E. rewrite (nth_error_nth' (upd l i x) d) in E by (rewrite upd_length; lia).
    injection E as E. exact E.
  - rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.

Lemma nth_upd_same : forall (l : list Z) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof.
  intros l i x d Hi. pose proof (nth_error_upd_same l i x Hi) as E. rewrite (nth_error_nth' _ d) in E by (rewrite upd_length; lia).
  injection E as E. exact E.
Qed.

Lemma filter_cons_class : forall (f : Z) (k : nat) (fr : list (Z * nat)) k',
  List.filter (fun fk => Nat.eqb (snd fk) k') ((f, k) :: fr) = if Nat.eqb k k' then (f, k) :: List.filter (fun fk => Nat.eqb (snd fk) k') fr
                                                                   else List.filter (fun fk => Nat.eqb (snd fk) k') fr.
Proof. reflexivity. Qed.

Lemma nbusy_upd1to0 : forall (fl : list Z) i, (i < length fl)%nat -> nth i fl 0 = 1 -> (nbusy (upd fl i 0%Z) + 1 = nbusy fl)%nat.
Proof.
  induction fl as [|z fl IH]; intros [|i] Hi Hn; cbn [length] in Hi; try lia; cbn [upd nbusy nth] in *.
  - subst z. cbn. lia.
  - rewrite <- (IH i ltac:(lia) Hn). destruct (Z.eqb z 0); lia.
Qed.

Lemma Forall_upd : forall (P : Z -> Prop) l i x, Forall P l -> P x -> Forall P (upd l i x).
Proof.
  intros P l. induction l as [|y l IH]; intros [|i] x H Hx; cbn [upd]; [constructor | constructor | |].
  - apply Forall_cons_iff in H as [_ H]. constructor; assumption.
  - apply Forall_cons_iff in H as [H1 H]. constructor; [exact H1 | exact (IH i x H Hx)].
Qed.

Lemma fs_rep_cls : forall Σ (m : mem) k, fs_rep Σ m -> (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat -> fs_cls_rep (l_FSB (lay Σ)) (Z.of_nat k) (fs_of Σ k) m.
Proof. intros Σ m k (_ & F0 & F2 & F4 & Fc1 & Fc3 & Fc2 & _) Hk. destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; assumption. Qed.

Lemma flags_range : forall c, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1 \/ c = 3 \/ c = 2) -> 0x1000 <= 0x1000 + flags_off c /\ 0x1000 + flags_off c + NF c <= 0x9000.
Proof. intros c Hc. unfold flags_off, NF. destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia. Qed.

Lemma flags_apart : forall c c', (c = 5 \/ c = 0 \/ c = 4 \/ c = 1 \/ c = 3 \/ c = 2) -> (c' = 5 \/ c' = 0 \/ c' = 4 \/ c' = 1 \/ c' = 3 \/ c' = 2) -> c <> c' ->
  flags_off c + NF c <= flags_off c' \/ flags_off c' + NF c' <= flags_off c.
Proof. intros c c' Hc Hc' Hne. unfold flags_off, NF. destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; destruct Hc' as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn in *; lia. Qed.

Lemma frame_addr_inj : forall FSB c p p', (c = 5 \/ c = 0 \/ c = 4 \/ c = 1 \/ c = 3 \/ c = 2) -> frame_addr FSB c p = frame_addr FSB c p' -> p = p'.
Proof. intros FSB c p p' Hc E. unfold frame_addr, fsz in E. destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn in E; lia. Qed.

Lemma u8arr_byte : forall (m : mem) A bs j b, u8arr bsegs m A bs -> nth_error bs j = Some b -> rw_cells bsegs m (A + Z.of_nat j) [C1 b].
Proof.
  intros m A bs j b [Hb Hw] Hn. pose proof (proj1 (nth_error_Some bs j) ltac:(rewrite Hn; discriminate)) as Hj.
  split; [split; [repeat split | cbn; exact (bytes_at_nth1 bsegs m A bs j b Hb Hn)]|].
  cbn [cells_size csize Nat.add]. destruct Hw as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat j + i) with (A + (Z.of_nat j + i)) by lia. apply W. lia.
Qed.

Lemma u8arr_set_byte : forall (m m' : mem) A bs j b, u8arr bsegs m A bs -> (j < length bs)%nat ->
  munch [(A + Z.of_nat j, A + Z.of_nat j + 1)] m m' -> wmono bsegs m m' -> rw_cells bsegs m' (A + Z.of_nat j) [C1 b] ->
  u8arr bsegs m' A (upd bs j b).
Proof.
  intros m m' A bs j b [(B0 & B1 & B) Hw] Hj MU WM [[_ Hc] _]. split.
  - split; [exact B0|]. split; [rewrite upd_length; exact B1|]. intros i Hi. rewrite upd_length in Hi.
    destruct (Nat.eq_dec i j) as [->|Hne].
    + rewrite nth_error_upd_same by exact Hj. destruct Hc as (_ & _ & Hc). specialize (Hc 0%nat ltac:(cbn; lia)). cbn in Hc.
      rewrite Z.add_0_r in Hc. exact Hc.
    + rewrite nth_error_upd_other by lia. rewrite <- (B i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
      cbn. split; [|exact I]. rewrite wa_unsigned by lia. lia.
  - rewrite upd_length. exact (wr_at_wmono m m' _ _ Hw WM).
Qed.

Lemma map_upd : forall {X Y} (f : X -> Y) l i x, map f (upd l i x) = upd (map f l) i (f x).
Proof. intros X Y f l. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity | reflexivity | reflexivity | rewrite IH; reflexivity]. Qed.

Section Release.
Variables (Σ : rtsA) (m : mem) (f : Z) (k : nat) (fr : list (Z * nat)).
Hypothesis HA : ART_A Σ m.
Hypothesis HF : frames Σ = (f, k) :: fr.
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).

Lemma rel_slot : (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat /\ exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr FSB (Z.of_nat k) p
  /\ nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1.
Proof. apply (busy_slot Σ m HA). rewrite HF. left. reflexivity. Qed.

Lemma rel_flags_ok : forall k', (k' = 5 \/ k' = 0 \/ k' = 4 \/ k' = 1 \/ k' = 3 \/ k' = 2)%nat -> flags_ok (Z.of_nat k') (fss_flags (fs_of Σ k')).
Proof.
  intros k' Hk'. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (F0 & F2 & F4 & Fc1 & Fc3 & Fc2 & _).
  destruct Hk' as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 F4) | exact (proj1 Fc1) | exact (proj1 Fc3) | exact (proj1 Fc2)].
Qed.

Theorem rta_frame_release : exists (Σ' : rtsA) (fl : Z), rw_cells bsegs m fl [C1 (Z_to_bv 8 1)]
  /\ ~ aclient (live Σ) (frames Σ) USTACK_TOP fl /\ 0 < fl /\ fl + 1 <= rtA_sp0 Σ - STACK_WIN
  /\ ro_cells bsegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
  /\ forall m', munch [(fl, fl + 1)] m m' -> wmono bsegs m m' -> rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)] ->
       ART_A Σ' m' /\ frames Σ' = fr /\ rtA_live Σ' = rtA_live Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ
       /\ rtA_allow Σ' = rtA_allow Σ /\ (forall mo, ARTM_A Σ mo -> ARTM_A Σ' mo).
Proof.
  destruct rel_slot as (Hk & p & Hp & Hf & Hb).
  assert (Hc : Z.of_nat k = 5 \/ Z.of_nat k = 0 \/ Z.of_nat k = 4 \/ Z.of_nat k = 1 \/ Z.of_nat k = 3 \/ Z.of_nat k = 2) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
  pose proof (rel_flags_ok k Hk) as (Hlen & Hfl01).
  pose proof (ART_fs Σ m HA) as FS. pose proof (fs_rep_cls Σ m k FS Hk) as (CH & CF & CFr).
  pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & G5).
  pose proof (flags_range _ Hc) as (FR1 & FR2).
  set (fl := fl_base FSB (Z.of_nat k) + p).
  assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ k)))%nat) by (apply Nat2Z.inj_lt; rewrite Hlen, Z2Nat.id by lia; lia).
  assert (Hfl : FSB + 0x1000 <= fl /\ fl + 1 <= FSB + 0x9000) by (unfold fl, fl_base; lia).
  assert (Hnth : nth_error (map b8 (fss_flags (fs_of Σ k))) (Z.to_nat p) = Some (Z_to_bv 8 1)).
  { rewrite nth_error_map, (nth_error_nth' _ 0 Hpl), Hb. reflexivity. }
  exists (fs_release Σ k p fr), fl.
  assert (Hbyte : rw_cells bsegs m fl [C1 (Z_to_bv 8 1)]).
  { unfold fs_flags in CF. pose proof (u8arr_byte m _ _ _ _ CF Hnth) as X. rewrite Z2Nat.id in X by lia. exact X. }
  split; [exact Hbyte|].
  split.
  {
    intros Hcl. pose proof (rta_sp0_range Σ m HA) as Hr.
    pose proof (art_avoid_client Σ m USTACK_TOP HA ltac:(unfold rtA_sp0, STACK_WIN, USTACK_TOP in *; lia)) as (_ & _ & _ & _ & _ & _ & _ & AF & _).
    destruct AF as (_ & A0 & A2 & A4 & A1 & A3 & A2b & _).
    assert (AK : fs_cls_avoid (W_client Σ USTACK_TOP) FSB (Z.of_nat k) (fs_of Σ k)) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; assumption).
    destruct AK as (_ & AK & _). rewrite Hlen in AK.
    apply (W_client_cover Σ USTACK_TOP fl Hcl). apply (disjoint_outside _ _ _ _ AK). unfold fl. lia. }
  split; [lia|]. split; [unfold l_ACEIL in G3; unfold rtA_sp0; lia|].
  split.
  {
    destruct FS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB. apply Forall_cons_iff in FB as [FB0 _].
    destruct FB0 as (p' & Hf' & _ & _ & Cw). cbn [fst snd] in *. rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ Hc) in Hf'. subst p'.
    exact (proj1 Cw). }
  intros m' MU WM Hz.

  assert (MUF : munch [(FSB, FSB + 0xb09000)] m m').
  { apply (munch_weaken [(fl, fl + 1)]); [|exact MU]. intros x Hx. cbn in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  pose proof (ART_transport_but_fs _ Σ m m' HA MUF WM (fsb_avoid Σ m HA)) as BF.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10).
  pose proof W6 as (FW0 & FW2 & FW4 & FW1 & FW3 & FW2b & FWr & FND & FLN & FCNT & FHINT).
  apply NoDup_ListNoDup in FND. rewrite HF in FND, FWr, FLN. apply NoDup_cons_iff in FND as [FNI FND]. apply Forall_cons_iff in FWr as [_ FWr].

  set (g := fs_of Σ k). set (g' := mkFs (fss_hint g) (upd (fss_flags g) (Z.to_nat p) 0)).
  assert (Wg' : fs_cls_wf (Z.of_nat k) g').
  { assert (Wg : fs_cls_wf (Z.of_nat k) g) by (unfold g; destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; assumption).
    destruct Wg as ((L1 & L2) & H1 & H2). split; [split|split]; cbn [fss_flags fss_hint g'].
    - rewrite upd_length. exact L1.
    - apply Forall_upd; [exact L2 | left; reflexivity].
    - exact H1.
    - pose proof (nbusy_upd0 (fss_flags g) (Z.to_nat p)). lia. }
  assert (Hfr : forall f2 k2, In (f2, k2) fr -> (f2, k2) <> (f, k)) by (intros f2 k2 Hin E; rewrite E in Hin; exact (FNI Hin)).
  assert (Wfr : Forall (fun fk => (snd fk = 5%nat \/ snd fk = 0%nat \/ snd fk = 4%nat \/ snd fk = 1%nat \/ snd fk = 3%nat \/ snd fk = 2%nat)
                      /\ exists q, 0 <= q < NF (Z.of_nat (snd fk)) /\ fst fk = frame_addr FSB (Z.of_nat (snd fk)) q
                                  /\ nth (Z.to_nat q) (fss_flags (fs_of (fs_release Σ k p fr) (snd fk))) 0 = 1) fr).
  { apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & p2 & Hp2 & Hf2 & Hb2).
    cbn [fst snd] in *. split; [exact Hk2|]. exists p2. split; [exact Hp2|]. split; [exact Hf2|].
    unfold fs_release. rewrite (fs_of_set Σ k _ fr k2 Hk Hk2). destruct (Nat.eqb_spec k k2) as [<-|Hne]; [|exact Hb2].
    cbn [fss_flags]. rewrite nth_upd_other; [exact Hb2|]. intros E. apply (Hfr f2 k Hin).
    assert (p2 = p) by (apply Z2Nat.inj; [lia | lia | symmetry; exact E]). subst p2. rewrite Hf2, Hf. reflexivity. }
  assert (Hwf' : rt_wf (fs_release Σ k p fr)).
  { split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
    split; [|split; [exact W7|split; [exact W8|split; [exact W9 | exact W10]]]].
    assert (CNT' : forall k', (k' = 5 \/ k' = 0 \/ k' = 4 \/ k' = 1 \/ k' = 3 \/ k' = 2)%nat ->
              Z.of_nat (nbusy (fss_flags (fs_of (fs_release Σ k p fr) k'))) = Z.of_nat (length (List.filter (fun fk => Nat.eqb (snd fk) k') fr))).
    { intros k' Hk'. unfold fs_release. rewrite (fs_of_set Σ k _ fr k' Hk Hk'). pose proof (FCNT k' Hk') as Ck. rewrite HF in Ck.
      rewrite (filter_cons_class f k fr k') in Ck. destruct (Nat.eqb_spec k k') as [<-|Hne]; cbn [fss_flags].
      - cbn [length] in Ck. pose proof (nbusy_upd1to0 (fss_flags (fs_of Σ k)) (Z.to_nat p) Hpl Hb) as X. lia.
      - exact Ck. }
    assert (HNT' : forall k', (k' = 5 \/ k' = 0 \/ k' = 4 \/ k' = 1 \/ k' = 3 \/ k' = 2)%nat -> fss_hint (fs_of (fs_release Σ k p fr) k') <= 2 ^ 14 * (CREDIT0 - credit (fs_release Σ k p fr))).
    { intros k' Hk'. unfold fs_release. rewrite (fs_of_set Σ k _ fr k' Hk Hk'). cbn [credit fs_set]. pose proof (FHINT k' Hk') as Hh.
      destruct (Nat.eqb_spec k k') as [<-|Hne]; [cbn [fss_hint]; exact Hh | exact Hh]. }
    split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Wfr|split; [apply NoDup_ListNoDup; exact FND | split; [cbn [length] in FLN; cbn [frames fs_release fs_set]; lia|split; [exact CNT' | exact HNT']]]]]]]]]].
    all: unfold fs_release, fs_set; destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn [fs0 fsc0 fs4 fs1 fs3 fs2]; first [exact Wg' | assumption]. }
  destruct FS as (F1 & _ & _ & _ & _ & _ & _ & FT & (dtvbeg & Hdb & TG) & (tb & te & TT) & FB). unfold fs_busy in FB. rewrite HF in FB.
  apply Forall_cons_iff in FB as [FB0 FBr].
  destruct FB0 as (p0 & Hf0 & FWr0 & FWs0 & _). cbn [fst snd] in *. rewrite Hf in Hf0. apply (frame_addr_inj _ _ _ _ Hc) in Hf0. subst p0.
  pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold sp_window_hi, l_ACEIL, STACK_WIN in *. unfold rtA_sp0 in *.

  assert (DSH : forall fa n, 0 <= fa -> fa + n <= FSB + 0xb09000 -> 0 <= n -> disjoint_from [(fl, fl + 1)] (shad fa) (n / 8)).
  { intros fa n H1 H2 H3. cbn. split; [|exact I].
    assert (Hs0 : SHB <= shad fa) by (unfold shad; pose proof (Z.div_pos fa 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hs1 : shad fa + n / 8 <= 2 ^ 44 + SHB).
    { unfold shad.
      assert (fa / 8 * 8 + n / 8 * 8 <= fa + n) by (pose proof (Z.mul_div_le fa 8 ltac:(lia)); pose proof (Z.mul_div_le n 8 ltac:(lia)); lia).
      assert (fa / 8 + n / 8 <= 2 ^ 44) by (assert ((fa / 8 + n / 8) * 8 <= 2 ^ 47) by lia; lia). lia. }
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia. }
  assert (DFR : forall fa n, FSB + 0x9000 <= fa -> disjoint_from [(fl, fl + 1)] fa n) by (intros fa n H; cbn; split; [lia | exact I]).
  assert (DIMG : forall a n, a + n <= SEGTOP_A -> disjoint_from [(fl, fl + 1)] a n) by (intros a n H; cbn; split; [unfold SEGTOP_A in *; lia | exact I]).
  assert (DGR : forall i b gn a n, (0 < i)%nat -> (i <> 5)%nat -> nth_error (startup_grants L) i = Some (b, gn) -> b <= a -> a + n <= b + gn ->
             disjoint_from [(fl, fl + 1)] a n).
  { intros i b gn a n Hi Hi5 Hn H1 H2. cbn. split; [|exact I].
    destruct (Nat.lt_ge_cases i 5) as [Hl|Hl].
    - pose proof (geo_apart Σ m HA i 5 _ _ Hl Hn eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart in Ha. lia.
    - pose proof (geo_apart Σ m HA 5 i _ _ ltac:(lia) eq_refl Hn) as Ha. cbn [fst snd] in Ha. unfold apart in Ha. lia. }

  assert (CLSo : forall c, (c = 5 \/ c = 0 \/ c = 4 \/ c = 1 \/ c = 3 \/ c = 2)%nat -> c <> k -> fs_cls_rep FSB (Z.of_nat c) (fs_of Σ c) m').
  { intros c Hcc Hne. pose proof (fs_rep_cls Σ m c (ART_fs Σ m HA) Hcc) as X. pose proof (rel_flags_ok c Hcc) as (Lc & _).
    assert (Hc2 : Z.of_nat c = 5 \/ Z.of_nat c = 0 \/ Z.of_nat c = 4 \/ Z.of_nat c = 1 \/ Z.of_nat c = 3 \/ Z.of_nat c = 2) by (destruct Hcc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
    apply (fs_cls_rep_transport [(fl, fl + 1)] _ _ _ m m' X MU WM). split; [|split].
    - cbn. split; [|exact I]. destruct Hc2 as [E|[E|[E|[E|[E|E]]]]]; rewrite E; lia.
    - rewrite Lc. pose proof (flags_range _ Hc2) as (R1 & R2). cbn. split; [|exact I]. unfold fl, fl_base.
      assert (Z.of_nat c <> Z.of_nat k) by lia. destruct (flags_apart _ _ Hc2 Hc H); lia.
    - intros q Hq _. pose proof (frame_addr_range FSB _ q Hc2 Hq) as (R1 & R2). unfold kFakeStackSize in R2.
      split; [apply DFR; exact R1 | apply DSH; [lia | lia | unfold fsz; pose proof (Z.pow_nonneg 2 (Z.of_nat c) ltac:(lia)); lia]]. }

  assert (CLSk : fs_cls_rep FSB (Z.of_nat k) g' m').
  { split; [|split].
    - unfold fs_hint in *. apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ CH MU WM). cbn. split; [|exact I].
      destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E in *; lia.
    - unfold fs_flags in *. cbn [fss_flags g']. rewrite map_upd. change (b8 0) with (Z_to_bv 8 0).
      apply (u8arr_set_byte m m' _ _ _ _ CF); [rewrite length_map; exact Hpl | rewrite Z2Nat.id by lia; exact MU | exact WM
                                              | rewrite Z2Nat.id by lia; exact Hz].
    - intros q Hq Hq0. cbn [fss_flags g'] in Hq0. destruct (Z.eq_dec q p) as [->|Hne].
      + rewrite <- Hf. assert (Hsz : fsz (Z.of_nat k) = fs_size k) by (symmetry; apply fs_size_fsz).
        assert (Hpos : 0 < fs_size k) by (rewrite <- Hsz; unfold fsz; destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E; cbn; lia).
        split.
        * pose proof (wr_at_stk m' _ _ (wr_at_wmono m m' _ _ FWr0 WM) ltac:(lia)) as St.
          destruct (stk_bytes bsegs m' _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs. rewrite Hsz.
          split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; replace (f + fs_size k - f) with (fs_size k) in Hl by lia; exact Hbs]|].
          cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono m m' _ _ FWr0 WM).
        * assert (Hs8 : 0 <= fs_size k / 8) by (apply Z.div_pos; lia).
          pose proof (wr_at_stk m' _ _ (wr_at_wmono m m' _ _ FWs0 WM) Hs8) as St.
          destruct (stk_bytes bsegs m' _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs. rewrite Hsz.
          split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; replace (shad f + fs_size k / 8 - shad f) with (fs_size k / 8) in Hl by lia; exact Hbs]|].
          cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono m m' _ _ FWs0 WM).
      + rewrite nth_upd_other in Hq0 by (intros E; apply Hne; apply Z2Nat.inj; [lia | lia | symmetry; exact E]).
        destruct (CFr q Hq Hq0) as [(j1 & J1) (j2 & J2)]. pose proof (frame_addr_range FSB _ q Hc Hq) as (R1 & R2). unfold kFakeStackSize in R2.
        split; [exists j1; apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ J1 MU WM) | exists j2; apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ J2 MU WM)];
          cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (unfold fsz; destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E; cbn; lia);
          [apply DFR; exact R1 | apply DSH; [lia | lia | unfold fsz; destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E; cbn; lia]]. }

  assert (FS' : fs_rep (fs_release Σ k p fr) m').
  { assert (F1' : fs_gstate fr (gcredit Σ) FSB m').
    { apply (fs_gstate_tail (f, k) fr). rewrite <- HF. apply (fs_gstate_transport [(fl, fl + 1)] _ _ _ m m' F1 MU WM). split; [destruct Hfl; cbn; split; [lia | exact I]|].
      intros c' Hc'. destruct (oflags_apart_flags FSB c' (Z.of_nat k) Hc' Hc) as [X|X]; (subst fl; cbn; split; [lia | exact I]). }
    assert (T' : rw_cells bsegs m' tpA [C8 (Z_to_bv 64 FSB)]) by (apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ FT MU WM); apply DIMG; unfold tpA, SEGTOP_A; cbn; lia).
    assert (TG' : tga_cells (l_DTV L) dtvbeg m').
    { unfold tga_cells, dtls_cells in *. destruct TG as (G1' & G2' & G3' & G4' & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)).
      repeat (split; [eapply (rw_cells_transport bsegs [(fl, fl + 1)] m m'); [eassumption | exact MU | exact WM | apply DIMG;
                      unfold g_real_tls_get_addr, g_dtv_ptr, g_dtv1, g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity,
                        g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; cbn; lia]|]).
      apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ D8 MU WM). cbn [cells_size csize Nat.add].
      apply (DGR 4%nat (l_DTV L) 4096); [lia | lia | reflexivity | lia | pose proof (geo_grant Σ m HA (l_DTV L) 4096 ltac:(unfold startup_grants; do 4 right; left; reflexivity)) as (D0 & _); lia]. }
    assert (TT' : ttls_cells (l_T L) m' tb te).
    { unfold ttls_cells in *. apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ TT MU WM). cbn [cells_size csize Nat.add].
      apply (DGR 2%nat (l_T L) 4096); [lia | lia | reflexivity | pose proof (geo_grant Σ m HA (l_T L) 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (D0 & _); lia | lia]. }
    assert (FB' : fs_busy L fr m').
    { unfold fs_busy. apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FBr (f2, k2) Hin) as (q & Hq & Wq1 & Wq2 & Cq).
      destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & q' & Hq' & Hf2 & _). cbn [fst snd] in *.
      assert (Hc2 : Z.of_nat k2 = 5 \/ Z.of_nat k2 = 0 \/ Z.of_nat k2 = 4 \/ Z.of_nat k2 = 1 \/ Z.of_nat k2 = 3 \/ Z.of_nat k2 = 2) by (destruct Hk2 as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
      pose proof (frame_addr_range FSB _ q' Hc2 Hq') as (R1 & R2). rewrite <- Hf2 in R1.
      exists q. split; [exact Hq|]. split; [exact (wr_at_wmono m m' _ _ Wq1 WM)|]. split; [exact (wr_at_wmono m m' _ _ Wq2 WM)|].
      apply (rw_cells_transport bsegs [(fl, fl + 1)] m m' _ _ Cq MU WM). apply DFR. rewrite fs_size_fsz.
      assert (8 <= fsz (Z.of_nat k2)) by (unfold fsz; destruct Hc2 as [E|[E|[E|[E|[E|E]]]]]; rewrite E; cbn; lia). lia. }
    unfold fs_rep. cbn [lay fs_release fs_set frames].
    destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn [fs0 fsc0 fs4 fs1 fs3 fs2];
      (split; [exact F1'|]); (split; [first [exact CLSk | exact (CLSo 5%nat ltac:(lia) ltac:(lia))]|]);
      (split; [first [exact CLSk | exact (CLSo 0%nat ltac:(lia) ltac:(lia))]|]); (split; [first [exact CLSk | exact (CLSo 4%nat ltac:(lia) ltac:(lia))]|]);
      (split; [first [exact CLSk | exact (CLSo 1%nat ltac:(lia) ltac:(lia))]|]);
      (split; [first [exact CLSk | exact (CLSo 3%nat ltac:(lia) ltac:(lia))]|]);
      (split; [first [exact CLSk | exact (CLSo 2%nat ltac:(lia) ltac:(lia))]|]);
      (split; [exact T'|]); (split; [exists dtvbeg; split; [exact Hdb | exact TG']|]); (split; [exists tb, te; exact TT' | exact FB']). }
  split; [exact (ART_of_but_fs _ m' Hwf' BF FS')|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros mo Hmo. exact Hmo.
Qed.

End Release.

Theorem rta_frame_release_vis : forall Σ (m : mem) f k fr, ART_A Σ m -> frames Σ = (f, k) :: fr ->
  exists (Σ' : rtsA) (fl : Z), rw_cells bsegs m fl [C1 (Z_to_bv 8 1)]
  /\ ~ aclient (rtA_live Σ) (frames Σ) USTACK_TOP fl /\ 0 < fl /\ fl + 1 <= rtA_sp0 Σ - STACK_WIN
  /\ ro_cells bsegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
  /\ forall m', munch [(fl, fl + 1)] m m' -> wmono bsegs m m' -> rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)] ->
       ART_A Σ' m' /\ frames Σ' = fr /\ rtA_live Σ' = rtA_live Σ /\ rtA_sp0 Σ' = rtA_sp0 Σ /\ credit Σ' = credit Σ
       /\ rtA_allow Σ' = rtA_allow Σ /\ (forall mo, ARTM_A Σ mo -> ARTM_A Σ' mo).
Proof.
  intros Σ m f k fr HA HF. destruct (rta_frame_release Σ m f k fr HA HF) as (Σ' & fl & A1 & A2 & A3).
  exists Σ', fl. split; [exact A1|]. split; [|exact A3]. intros X. apply A2. unfold rtA_live in X. exact (aclient_vis _ _ _ _ _ X).
Qed.

End GWIN.
