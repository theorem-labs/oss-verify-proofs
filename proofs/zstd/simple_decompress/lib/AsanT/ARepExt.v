(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes AModelFacts ASecFacts ARep ALayout AHeapP ARepKit ARepFrame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition aext (L : alayout) (iv : Z * Z) : Prop :=
  fst iv < snd iv ->
     (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
  \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
  \/ ATOP <= fst iv
  \/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47)).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nonempty (iv : Z * Z) : bool := fst iv <? snd iv.

Lemma sub_fp_filter_nonempty : forall W, sub_fp W (List.filter nonempty W).
Proof.
  unfold sub_fp. induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
  unfold nonempty in Hx. cbn [fst snd] in Hx. destruct (Z.ltb_spec lo hi).
  - cbn in Hx. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact Hx].
Qed.
Lemma munch_filter_nonempty : forall W m m', munch W m m' -> munch (List.filter nonempty W) m m'.
Proof. intros W m m' MU. eapply munch_weaken; [apply sub_fp_filter_nonempty | exact MU]. Qed.

Lemma filter_cons_eq : forall {A} (f : A -> bool) x l, List.filter f (x :: l) = if f x then x :: List.filter f l else List.filter f l.
Proof. reflexivity. Qed.

Lemma disjoint_from_Forall : forall W A k,
  Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W -> disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros A k HF; cbn; [exact I|].
  inversion HF as [| x l H1 H2]; subst. cbn [fst snd] in H1. split; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma ext_clear : forall L W A k,
  Forall (aext L) W -> 0 <= k ->
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= A) ->
  A + k <= ATOP ->
  (A + k <= shad ATOP \/ shad (2^47) <= A) ->
  disjoint_from (List.filter nonempty W) A k.
Proof.
  intros L W A k EXT Hk D1 D2 D3 D4. apply disjoint_from_Forall.
  induction W as [|[lo hi] W IH]; [constructor|].
  inversion EXT as [| x l E1 E2]; subst.
  rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
  destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
  constructor; [| apply IH; exact E2]. cbn [fst snd].
  unfold aext in E1. cbn [fst snd] in E1. specialize (E1 LT).
  clear IH E2 EXT. lia.
Qed.

(* [comment removed for export] *)
Section Ext.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

Theorem AREP_frame_ext : forall L st X m m' W,
  alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
             (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
          \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
          \/ ATOP <= fst iv
          \/ (shad ATOP <= fst iv /\ snd iv <= shad (2^47))) W ->      (* [comment removed for export] *)
  AREP H L st X m'.
Proof.
  intros L st X m m' W ALO AR MU0 WM EXT.
  change (Forall (aext L) W) in EXT.
  pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
  (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(lia)) as FKI. unfold aobj in FK. destruct FK as (FK3 & FK1 & FK2 & FKS & _).
  unfold sclr, KLS in FKS. unfold AIMG_HI in FKI. pose proof atop_range as ATR.
  pose proof (fun A k => ext_clear L W A k EXT) as KX. cbn beta in KX. fold W' in KX.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_res_hi L ALO) as ORH.
  unfold aobj, sclr, KLS in OT, OC, ORS, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_fake_res L ALO) as D_f_res.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_c_f, D_f_res, D_n_f, D_s_f.
  (* [comment removed for export] *)
  assert (SHF : 2147450880 + 805376 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= shad ATOP
                /\ shad ATOP + 1048576 <= shad (2^47) /\ shad (2^47) = 17594333495296).
  { rewrite !shad_div, shlen_div. change (2^47) with 140737488355328. unfold ASHOFF in *. clear -FKI FK2 ATR. Z.div_mod_to_equations. lia. }
  destruct SHF as (SF1 & SF2 & SF3 & SF4).
  assert (SF0 : shlen 11571200 = 1446400) by (rewrite shlen_div; reflexivity).
  assert (SAT : 0x10006fef8000 <= shad ATOP <= 0x10007fef8000) by (rewrite shad_div; unfold ASHOFF; clear -ATR; Z.div_mod_to_equations; lia).
  assert (SHR : shad (al_res L) + shlen 137439023104 <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad (al_res L)).
  { destruct D_f_res as [D|D]; [right | left]; apply shad_sep; [exact D | clear -FK3 | exact D | clear -ORS]; Z.div_mod_to_equations; lia. }
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= shad ATOP).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS ORH. Z.div_mod_to_equations. lia. }
  destruct SHRES as (SR1 & SR2 & SR3).
  (* [comment removed for export] *)
  assert (FKB : al_fake L + 11571200 <= 2147450880 \/ 17594333495296 <= al_fake L) by (clear -FKS; lia).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0 <= A -> 0 <= k -> A + k <= AIMG_HI -> disjoint_from W' A k).
  { intros A k H1 H2 H3. unfold AIMG_HI in H3. apply KX; [exact H2| clear -H3 FKI; lia| clear -H3 SF1; lia| clear -H3 ATR; lia| clear -H3 SF0 SF1 SF2; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply KX; [exact H2| | clear -H1 H2 H3 SHR SR2; lia| clear -H3 SR3 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| clear -H3 SR3; lia].
    clear -H1 H3 SR1 SR3 FKB ATR. rewrite (shad_div ATOP) in *. unfold ASHOFF in *. lia. }
  (* [comment removed for export] *)
  assert (Kobj : forall A k, 0 <= k -> A + k <= ATOP -> (A + k <= 2147450880 \/ 17594333495296 <= A) ->
                 (A + k <= al_fake L \/ al_fake L + 11571200 <= A) -> disjoint_from W' A k).
  { intros A k H2 H3 HB H4. apply KX; [exact H2| exact H4| clear -HB SF0 SF1 SF2 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia| exact H3| clear -HB H3 SF3 SF4 ATR; rewrite (shad_div ATOP) in *; unfold ASHOFF in *; lia]. }
  clear KX.
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 ORS; lia | clear -H1 ORH; lia | clear -H1 H3 D_f_res; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OT; lia | clear -H1 H3 OT; lia | clear -H1 H3 D_t_f; lia]. }
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OC; lia | clear -H1 H3 OC; lia | clear -H1 H3 D_c_f; lia]. }
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W' m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  split.
  { eapply (hq_frame _ HL L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE]. unfold nonempty in NE. cbn [fst snd] in NE. apply Z.ltb_lt in NE.
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E NE). change (2^47)%Z with 140737488355328%Z in E.
      unfold AINSTANCE in *. change (shad 140737488355328) with 17594333495296%Z in E.
      split; [clear -E OT D_t_f SF0 SF1 SF2 SAT; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      split; [clear -E FKI SF1 SAT ATR; lia|].
      intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |];
        clear -E B1 B2 ORS ORH D_f_res SF0 SF2 SAT; lia.
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
      atop_facts. clear -E Ha FK1 FK2.
      destruct E as [[E1 E2]|[[E1 E2]|[E1|[E1 E2]]]].
      + do 10 right. left. lia.
      + do 2 right. left. rewrite shlen_div in E2. lia.
      + do 4 right. left. lia.
      + do 3 right. left. rewrite (shad_div 140737488355328) in E2. change (140737488355328 / 8)%Z with 17592186044416%Z in E2. unfold ASHOFF in E2. lia.
    - apply sec_same_refl. }
  split.
  { eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
    apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
    unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
    pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold aext in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)). change (2^47)%Z with 140737488355328%Z in E.
    change (shad 140737488355328) with 17594333495296%Z in E.
    clear -E Ha FKI SF0 SF1 SF2 SAT ON OS D_n_f D_s_f ATR. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
  intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Ext.

(* [comment removed for export] *)
Lemma AHEAP_P_hb_fake : forall H L RNG st LB m p A n,
  AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> A + n <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7). destruct G7 as (_ & _ & _ & _ & _ & _ & CF & _).
       pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold SEC_UOFF. clear -G3 G4 G5 CF SF. lia. }
  destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. destruct M as (N0 & FIT & _).
  destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
  pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. unfold adisj in D.
  pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
  subst A n. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP D N0 FIT RG RZ. lia.
Qed.

Lemma AREP_relro : forall H L st X m, AREP H L st X m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L st X m AR. destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _). exact HRO. Qed.

Lemma AHEAP_P_relro : forall H L RNG st LB m, AHEAP_P H L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros H L RNG st LB m (_ & _ & [X [AR _]] & _). exact (AREP_relro H L st X m AR). Qed.

(* [comment removed for export] *)
Lemma AHEAP_P_hb_range : forall H L RNG st LB m p A n,
  AHEAP_P H L RNG st LB m -> In (HB p A n) LB -> ablock_range A n.
Proof.
  intros H L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  destruct AR as (WF & _). pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  2: { cbn [sec_wf1] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
       pose proof (sec_facts n ltac:(lia) G6) as SF. subst A. unfold ablock_range, SEC_UOFF in *. clear -G1 G2 G3 G4 G5 SF.
       split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
  destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. destruct M as (N0 & FIT & _).
  destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
  pose proof (slot_aligned L (xb_class b) (xb_slot b) SAL CLB) as AL.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_res_hi L ALO) as ORH.
  pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rz_size_eq (xb_n b)) as RZE.
  assert (RZ16 : rz_size (xb_n b) mod 16 = 0).
  { rewrite RZE. assert (0 <= rz_log (xb_n b)) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
    replace (2 ^ rz_log (xb_n b)) with (2 ^ (rz_log (xb_n b) - 0)) by (f_equal; lia).
    rewrite Z.mul_comm. apply Z_mod_mult. }
  subst A n. unfold ablock_range, xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
  split; [right; split; [clear -P5 RSP ORS ORH CLB RZ; lia| clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia]|]. split; [clear -N0; lia|].
  split; [clear -P4 Q1 Q2 CLB RSP ORS FIT RG; lia|].
  clear -AL RZ16. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.
