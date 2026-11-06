(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux MRepAux MTree Mall5lv Mallrkx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall1es Mallx0z Mall17y Mall79j.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_read_wr8 st p v rid o :
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) rid) o =
  if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
  intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
  - destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
  - rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop :=
  (exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b - IB <= o < snd b + 12)
  \/ (exists b g i, hosts st b g /\ fst b = rid /\ 0 <= i <= m_last_idx (get_meta_rec st g) /\ o = sstart_of (get_meta_rec st g) i - IB)
  \/ (exists blk, In blk LB /\ fst (blk_slot blk) = rid
        /\ snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk)) - IB <= o < snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk))).

Section KSH.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : forall rid o, PROT st LB rid o -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.

Lemma hosts_sh b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
Lemma is_gm_sh q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
Lemma conc_sh q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

Lemma hdr_known_sh p b1 i1 rid :
  fst p = rid -> (forall k, 1 <= k <= 3 -> PROT st LB rid (snd p - k)) ->
  hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof.
  (intros <- HP; (first [ intro dR_23; dex3 dR_23 as v3 lo hi; dand5 dR_23 as H3 I3 H2 H1 E | intro dR_23; dand8 dR_23 as v3 lo hi H3 I3 H2 H1 E | intros (v3 & lo & hi & H3 & I3 & H2 & H1 & E) ])). exists v3, lo, hi.
  rewrite !SHP by (apply HP; lia). auto 10.
Qed.

Lemma KINV_shadow c : KINV st LB c -> KINV st' LB c.
Proof.
  intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
  assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
  { intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
    - unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
    - intros ML. (first [ pose proof ((go_nest _ _ _ GO ML)) as dR_1; dex3 dR_1 as g1 i1 b1; dand8 dR_1 as SL HB1 FB EQB I1 NF1 LT HK | pose proof ((go_nest _ _ _ GO ML)) as dR_1; dand11 dR_1 as g1 i1 b1 SL HB1 FB EQB I1 NF1 LT HK | destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK) ]).
      exists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
      split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
      eapply hdr_known_sh; [reflexivity| | exact HK].
      intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
  constructor.
  - apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
  - intros b g HB. apply GMO. apply hosts_sh. exact HB.
  - intros b gh Hb. rewrite EG in Hb. (first [ pose proof ((ki_grps _ _ _ K b gh Hb)) as dR_2; dex1 dR_2 as g; destruct dR_2 as [Hg Hai] | pose proof ((ki_grps _ _ _ K b gh Hb)) as dR_2; dand3 dR_2 as g Hg Hai | destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai) ]). exists g. rewrite EM. auto.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
  - intros s g i Hs. rewrite ESL in Hs. rewrite EM. (first [ pose proof ((CS s g i Hs)) as dR_3; dand3 dR_3 as GM E I | destruct (CS s g i Hs) as (GM & E & I) ]). split; [apply is_gm_sh; exact GM| auto].
  - intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
    left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
  - intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
    right; left. exists b, g, i. auto.
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
    assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
    constructor; [| rewrite EG; exact NG| exact SZ].
    exists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
    exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
    + rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
    + eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
      cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
  - exact (ki_nodup _ _ _ K).
  - pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
  - intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
  - intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - exact TK'.
Qed.
End KSH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).

Lemma hdr_st_tables st pf :
  s_regions (hdr_st st pf) = s_regions st /\ s_areas (hdr_st st pf) = s_areas st /\ s_groups (hdr_st st pf) = s_groups st
  /\ s_slots (hdr_st st pf) = s_slots st /\ s_reserved (hdr_st st pf) = s_reserved st /\ s_ctx (hdr_st st pf) = s_ctx st
  /\ s_tick (hdr_st st pf) = s_tick st /\ (forall q, get_meta_rec (hdr_st st pf) q = get_meta_rec st q)
  /\ s_metas (hdr_st st pf) = s_metas st /\ s_next_rid (hdr_st st pf) = s_next_rid st.
Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Lemma ticks_ok_hdr_st st pf : ticks_ok st -> ticks_ok (hdr_st st pf).
Proof. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
  cell_read (get_shadow (hdr_st st pf) rid) o =
    if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
    then Known (if o =? snd pf - 3 then 255 else 0)
    else cell_read (get_shadow st rid) o.
Proof.
  intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
  cbn [aadd fst snd].
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
  destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
  destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_cell_read_other st pf rid o : ticks_ok st ->
  (rid <> fst pf \/ o < snd pf - 3 \/ snd pf <= o) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = cell_read (get_shadow st rid) o.
Proof.
  intros TK H. rewrite hdr_st_cell_read by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_known_back st pf rid o v : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = Known v -> exists w, cell_read (get_shadow st rid) o = Known w.
Proof.
  intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
  destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
  destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
  destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
  cbn [orb] in H. exists v; exact H.
Qed.

(* [comment removed for export] *)
Lemma free_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> free_fp (hdr_st st pf) lo sp' a -> free_fp st lo sp a.
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. (first [ dex3 H as rid r v; dand4 H as H1 H2 H3 H4 | dand7 H as rid r v H1 H2 H3 H4 | destruct H as (rid & r & v & H1 & H2 & H3 & H4) ]). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

Lemma ZINV_hdr_st st pf Zs : ZINV st Zs -> ZINV (hdr_st st pf) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma KINV_hdr_st st LB LB' c (pf : aptr) (blk : block) r :
  CINV st LB -> In blk LB -> KINV st LB' c ->
  (forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk) ->
  fst pf = fst (blk_slot blk) -> (s_regions st) !! (fst pf) = Some r -> r_base r + snd pf = blk_addr blk -> snd pf mod 16 = 0 ->
  KINV (hdr_st st pf) LB' c.
Proof.
  intros C Hin K HLB Hfst Hr Hpo PM.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
  destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
  rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  (first [ pose proof ((hdr_st_tables st pf)) as dR_5; dand9 dR_5 as ER EA EG ESL ERS EC ET EM _ | destruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _) ]).
  apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
  intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
  destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
  pose proof (ki_gmetas _ _ _ K) as CG.
  destruct HP as [HP|[HP|HP]].
  - (first [ dex2 HP as b gh; dand3 HP as Hb Fb Ho | dand5 HP as b gh Hb Fb Ho | destruct HP as (b & gh & Hb & Fb & Ho) ]).
    specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
    rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
  - (first [ dex3 HP as b g i; dand4 HP as HB Fb Hi -> | dand7 HP as b g i HB Fb Hi -> | destruct HP as (b & g & i & HB & Fb & Hi & ->) ]).
    pose proof (CG b g HB) as GO. (first [ pose proof ((go_region _ _ _ GO)) as dR_8; dex1 dR_8 as rb; dand5 dR_8 as Hrb _ B0 B16 _ | pose proof ((go_region _ _ _ GO)) as dR_8; dand6 dR_8 as rb Hrb _ B0 B16 _ | destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _) ]). pose proof (go_stride _ _ _ GO) as [S16 SM].
    pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
    assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
    { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
    set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
    unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
  - (first [ dex1 HP as blk'; dand3 HP as Hin' Fb' Ho | dand4 HP as blk' Hin' Fb' Ho | destruct HP as (blk' & Hin' & Fb' & Ho) ]). destruct (HLB blk' Hin') as [HinL NEs].
    specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
    pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
    destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
    rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
    unfold IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite <- list_elem_of_In, list_elem_of_filter.
  pose proof (list_elem_of_In l x) as E. tauto.
Qed.

Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
  List.NoDup l -> List.NoDup (filter P l).
Proof.
  induction l as [|x l IH]; intros ND; [constructor|].
  rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

Lemma map_filter_slot (f : aptr -> bool) (LB : list block) :
  map blk_slot (filter (fun b => f (blk_slot b)) LB) = filter f (map blk_slot LB).
Proof.
  induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma KINV_filter_slot st LB c (f : aptr -> bool) : KINV st LB c -> KINV st (filter (fun b => f (blk_slot b)) LB) c.
Proof.
  intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
  - apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) BL blk Hin).
  - rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

End CEIL.

Lemma LPRE_intro st LB c g p i (blk : block) :
  ci_slots st -> hosts st p g -> (s_slots st) !! (blk_slot blk) = Some (g, i) ->
  ~ slot_free (get_meta_rec st g) i -> (s_groups st) !! (blk_slot blk) = None -> c <= m_sizeclass (get_meta_rec st g) ->
  LPRE st (filter (fun b => negb (aptr_eqb (blk_slot b) (blk_slot blk))) LB) c g p i.
Proof.
  intros CS HB SL NF NG HC. (first [ pose proof ((CS _ _ _ SL)) as dR_10; dand3 dR_10 as GM E I | destruct (CS _ _ _ SL) as (GM & E & I) ]).
  constructor; auto.
  - rewrite <- E. exact NG.
  - apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
    rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma conc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma pw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite conc_drop by exact H. reflexivity. Qed.
Lemma get_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

Lemma meta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). (first [ pose proof ((PM q)) as dR_11; dand3 dR_11 as P1 P2 P3 | destruct (PM q) as (P1 & P2 & P3) ]).
  unfold meta_cells. rewrite !pw_drop by assumption. reflexivity.
Qed.

Lemma ctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !pw_drop by assumption. reflexivity.
Qed.
Lemma actives_drop : actives st' = actives st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply pw_drop. apply PA.
Qed.
Lemma ctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (conc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma mrep_drop_region m : mrep st m -> mrep st' m.
Proof.
  intros MR. (first [ pose proof (MR) as dR_12; dand6 dR_12 as WF CX GL AR GR SH | pose proof MR as (WF & CX & GL & AR & GR & SH) ]). (first [ pose proof (WF) as dR_13; dand5 dR_13 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. (first [ pose proof ((WA a ar Ha)) as dR_14; dex1 dR_14 as r; destruct dR_14 as [Hr REST] | pose proof ((WA a ar Ha)) as dR_14; dand3 dR_14 as r Hr REST | destruct (WA a ar Ha) as (r & Hr & REST) ]). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. (first [ pose proof ((WG b gh Hb)) as dR_15; dex1 dR_15 as r; destruct dR_15 as [Hr REST] | pose proof ((WG b gh Hb)) as dR_15; dand3 dR_15 as r Hr REST | destruct (WG b gh Hb) as (r & Hr & REST) ]). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold mrep_ctx. rewrite ctx_head_cells_drop, actives_drop, ctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. (first [ pose proof ((AR a ar Ha)) as dR_16; dand3 dR_16 as A1 A2 A3 | destruct (AR a ar Ha) as (A1 & A2 & A3) ]).
    unfold area_rep. rewrite (conc_drop a) by exact Pa. rewrite pw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rec_drop, meta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. (first [ pose proof ((GR b gh Hb)) as dR_17; dex1 dR_17 as w8; destruct dR_17 as [R Hw] | pose proof ((GR b gh Hb)) as dR_17; dand3 dR_17 as w8 R Hw | destruct (GR b gh Hb) as (w8 & R & Hw) ]). exists w8.
    rewrite (conc_drop b) by exact Pb. rewrite pw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold shadow_rep. rewrite get_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ci_mptrs_frame st st2 : ci_mptrs st -> amc (ctx st2) = amc (ctx st) -> s_areas st2 = s_areas st -> s_regions st2 = s_regions st ->
  ci_mptrs st2.
Proof.
  ((first [ intro dR_24; dand5 dR_24 as M1 M2 M3 M4 M5 | intros (M1 & M2 & M3 & M4 & M5) ]); intros EC EA ER).
  assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
  unfold amc in EC. inversion EC.
  unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.

Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma ptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> mrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof.
  (intros K ZI MR Hr Kr NOG; (first [ intro dR_25; dand5 dR_25 as M1 M2 M3 M4 M5 | intros (M1 & M2 & M3 & M4 & M5) ])).
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_18; dand5 dR_18 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { (intros q; (first [ intro dR_26; dex3 dR_26 as a ar k; dand3 dR_26 as Ha Hk -> | intro dR_26; dand6 dR_26 as a ar k Ha Hk -> | intros (a & ar & k & Ha & Hk & ->) ]); intros E). cbn in E. (first [ pose proof ((WA a ar Ha)) as dR_19; dex1 dR_19 as ra; dand6 dR_19 as Hra _ _ _ NK _ | pose proof ((WA a ar Ha)) as dR_19; dand7 dR_19 as ra Hra _ _ _ NK _ | destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _) ]).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. ((first [ intro dR_27; dex1 dR_27 as r'; destruct dR_27 as [Hr' NK] | intro dR_27; dand3 dR_27 as r' Hr' NK | intros (r' & Hr' & NK) ]); intros E). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. (first [ pose proof ((ki_bk _ _ _ K brid boff HB)) as dR_20; dex1 dR_20 as r'; destruct dR_20 as [Hr' K'] | pose proof ((ki_bk _ _ _ K brid boff HB)) as dR_20; dand3 dR_20 as r' Hr' K' | destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K') ]). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. (first [ pose proof ((WA a ar Ha)) as dR_21; dex1 dR_21 as ra; dand6 dR_21 as Hra _ _ _ NK _ | pose proof ((WA a ar Ha)) as dR_21; dand7 dR_21 as ra Hra _ _ _ NK _ | destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _) ]). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    (first [ pose proof ((ki_grps _ _ _ K b gh Hb)) as dR_22; dex1 dR_22 as g; destruct dR_22 as [Hg _] | pose proof ((ki_grps _ _ _ K b gh Hb)) as dR_22; dand3 dR_22 as g Hg _ | destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _) ]). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End CEIL2.
