(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Read MI_WFree
  MI_Pres2 MI_Pres4 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim MI_Contracts.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocRep_u MallocTree_u MallocBlocks_u MallocFacts_B_u MallocFacts_inv_u MallocFacts_inv2_u.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Section CF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Lemma hostsB b g : MallocFacts_B_u.hosts st b g <-> hosts st b g.
Proof. reflexivity. Qed.
Lemma is_gmB g : is_gm st g <-> live_group st g.
Proof. reflexivity. Qed.

Lemma listed_meta_slot m h : In m (LS h) -> meta_slot st m.
Proof.
  intros H. pose proof (listed_present _ _ _ _ _ INV m h H) as P. destruct (s_metas st !! m) as [mr|] eqn:E; [| congruence].
  destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & ->). exists a, ar, k. auto.
Qed.

Lemma in_list_of_next m : m_next (MR st m) <> None -> exists h, In m (LS h).
Proof. intros H. exact (proj2 (proj1 (il_link _ _ IL m)) H). Qed.

(* [comment removed for export] *)
Lemma sep_ghdr' m bm i m2 b2 : hosts st bm m -> 0 <= i <= m_last_idx (MR st m) ->
  s_groups st !! (fst bm, sstart (MR st m) i) = None ->
  hosts st b2 m2 -> fst b2 = fst bm ->
  snd b2 + 16 <= sstart (MR st m) i \/ sstart (MR st m) (i + 1) <= snd b2.
Proof.
  intros Hm Hi NH H2 Hf. pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (sst_lt _ _ _ IG _ _ i (i + 1) Hm ltac:(lia)) as L1. unfold UNIT in S0.
  destruct (aptr_eq_dec m2 m) as [->|NEm].
  - left. pose proof (hosts_inj _ _ _ IM _ _ _ Hm H2); subst b2. pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). lia.
  - pose proof (sstart0 _ _ _ IM _ _ H2) as S2. unfold UNIT in S2. pose proof (gend_ge _ _ _ IM IG _ _ H2) as G2.
    destruct (dichotomy _ _ _ _ IM IG IS _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
    + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ _ _ IM IG IS _ _ _ Hm NH _ _ Ha)|].
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha H2) as (A1 & A2 & A3).
      destruct (Z.lt_ge_cases j i).
      * left. pose proof (sstart_mono _ _ _ IG _ _ (j + 1) i Hm ltac:(lia)). lia.
      * right. pose proof (sstart_mono _ _ _ IG _ _ (i + 1) j Hm ltac:(lia)). lia.
    + left. destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
      pose proof (hosts_inj _ _ _ IM _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ IM _ _ _ H2 H2'); subst b2'.
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha Hm) as (A1 & A2 & A3).
      pose proof (sstart_mono _ _ _ IG _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). lia.
    + destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
      pose proof (hosts_inj _ _ _ IM _ _ _ Hm Hm'); subst bm'.
      destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
      pose proof (hosts_inj _ _ _ IM _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ IM _ _ _ Hp Hp'); subst bp'.
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
      destruct (anc_box _ _ _ _ IM IG IS _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite (gend_eq st) in A2.
      pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)).
      destruct (Z.lt_ge_cases j1 j2).
      * right. pose proof (sstart_mono _ _ _ IG _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
      * left. pose proof (sstart_mono _ _ _ IG _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma c_links : ci_links_t st.
Proof.
  pose proof (old_lists _ _ _ _ _ INV) as LO.
  constructor.
  - intros m nx Hn. fold (MR st m) in Hn. fold (MR st nx). destruct (in_list_of_next m ltac:(rewrite Hn; discriminate)) as [h Hh].
    destruct (lists_next_in st LS LO h m Hh) as (y & Hy & Ey & Py). rewrite Hn in Ey. inversion Ey; subst y.
    split; [exact Py| exact (listed_meta_slot _ _ Hy)].
  - intros m pv Hp. fold (MR st m) in Hp. fold (MR st pv).
    destruct (m_next (MR st m)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL m) Ex) as P; rewrite Hp in P; discriminate].
    destruct (in_list_of_next m ltac:(rewrite Ex; discriminate)) as [h Hh].
    destruct (lists_prev_in st LS LO h m Hh) as (y & Hy & Ey & Ny). rewrite Hp in Ey. inversion Ey; subst y.
    split; [exact Ny| exact (listed_meta_slot _ _ Hy)].
  - intros m. fold (MR st m). split; [exact (proj2 (il_link _ _ IL m))|]. intros Hp.
    destruct (m_next (MR st m)) as [x|] eqn:Ex; [| reflexivity]. exfalso.
    destruct (in_list_of_next m ltac:(rewrite Ex; discriminate)) as [h Hh].
    destruct (lists_prev_in st LS LO h m Hh) as (y & _ & Ey & _). rewrite Hp in Ey. discriminate.
  - intros m Hn. fold (MR st m) in Hn. destruct (in_list_of_next m Hn) as [h Hh]. exact (listed_meta_slot _ _ Hh).
Qed.

Lemma c_heads : ci_heads_t st.
Proof.
  constructor.
  - intros h Hh. fold (MR st h). pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
    split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|]. pose proof (il_free _ _ IL h Hin) as E. rewrite E. reflexivity.
  - intros sc a Ha. fold (MR st a). pose proof (head_listed _ _ _ _ _ INV (LActive sc) a Ha) as Hin.
    destruct (il_active _ _ IL sc a Hin) as (Hsc & Hl & Esc). split; [exact Hsc|]. split; [exact (listed_next _ _ _ _ _ INV a _ Hin)|]. split; [exact Hl| exact Esc].
Qed.

Lemma c_homog : ci_homog st.
Proof.
  intros m nx Hn. fold (MR st m) in Hn. fold (MR st m) (MR st nx).
  destruct (in_list_of_next m ltac:(rewrite Hn; discriminate)) as [h Hh].
  pose proof (next_listed _ _ _ _ _ INV h m nx Hh Hn) as Hnx.
  destruct h as [sc|].
  - destruct (il_active _ _ IL sc m Hh) as (_ & Lm & Em). destruct (il_active _ _ IL sc nx Hnx) as (_ & Ln & En).
    split; [split; auto|]. intros _. rewrite Em, En. reflexivity.
  - pose proof (free_not_live _ _ _ _ _ INV m Hh) as Nm. pose proof (free_not_live _ _ _ _ _ INV nx Hnx) as Nn.
    split; [split; intros H'; exfalso; [exact (Nm H')| exact (Nn H')]|]. intros H'. exfalso. exact (Nm H').
Qed.

Lemma q_div b0 stride i off : stride mod 16 = 0 -> (b0 + 16 + stride * i + 16 * off - b0 - 16) / 16 * 16 = stride * i + 16 * off.
Proof.
  intros Hs. pose proof (Z.div_mod stride 16 ltac:(lia)) as E. rewrite Hs, Z.add_0_r in E.
  set (k := stride / 16) in *. clearbody k. subst stride.
  replace (b0 + 16 + 16 * k * i + 16 * off - b0 - 16) with ((k * i + off) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

Lemma mod16_addr a b st_ i off : a mod 4096 = 0 -> b mod 16 = 0 -> st_ mod 16 = 0 -> (a + (b + 16 + st_ * i) + 16 * off) mod 16 = 0.
Proof.
  intros Ha Hb Hs.
  pose proof (Z.div_mod a 4096 ltac:(lia)) as Ea. rewrite Ha, Z.add_0_r in Ea. set (a' := a / 4096) in *. clearbody a'.
  pose proof (Z.div_mod b 16 ltac:(lia)) as Eb. rewrite Hb, Z.add_0_r in Eb. set (b' := b / 16) in *. clearbody b'.
  pose proof (Z.div_mod st_ 16 ltac:(lia)) as Es. rewrite Hs, Z.add_0_r in Es. set (s' := st_ / 16) in *. clearbody s'.
  subst a b st_. replace (4096 * a' + (16 * b' + 16 + 16 * s' * i) + 16 * off) with ((256 * a' + b' + 1 + s' * i + off) * 16) by lia.
  apply Z_mod_mult.
Qed.

Lemma c_gmeta : ci_gmeta st.
Proof.
  intros b g Hm. destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai & Hb & GO).
  pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI. pose proof (g_li _ _ _ _ _ _ GO) as LI.
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
  destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r & Hr & Kr & A0 & GE).
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SM].
  constructor; try (fold (MR st g)).
  - pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! g) as [mr|] eqn:Em; [| congruence].
    destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk). exists a, ar, ka. auto.
  - split; [exact M1|]. apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia.
  - split; [exact M2|]. apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia.
  - exact LI.
  - exact (g_freeable _ _ _ _ _ _ GO).
  - destruct (g_sc _ _ _ _ _ _ GO) as [[S1 S2]|(S1 & S2 & S3 & _)]; [left; lia| right; lia].
  - split; [exact ML|]. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & _ & _ & CEIL & _). pose_ceil.
    destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
    destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r' & Hr' & _ & E4 & _). rewrite Hr in Hr'. inversion Hr'; subst r'. lia.
  - intros i Hi. split; intros Ht; [pose proof (M3 i Hi Ht); lia| exact (M4 i Hi Ht)].
  - exact (hosts_mem _ _ _ IM _ _ Hm).
  - exists r. pose proof (g_align _ _ _ _ _ _ GO) as [_ A16]. split; [exact Hr|]. split; [exact Kr|]. split; [exact A0|]. split; [exact A16|].
    split; [unfold MallocFacts_B_u.sstart_of; change (sstart (MR st g) (m_last_idx (MR st g) + 1) <= round_up_pg (r_len r)); rewrite <- (gend_eq st); exact GE|].
    intros NZ. destruct (g_top _ _ _ _ _ _ GO NZ) as (S0 & r' & Hr' & _ & E4 & _). rewrite Hr in Hr'. inversion Hr'; subst r'. auto.
  - split; [exact SG| exact SM].
  - intros MZ. destruct (g_nest _ _ _ _ _ _ GO MZ) as (p & i & Hsl & Hfst & Hend & Hsc & Hstr).
    destruct (is_valid _ _ _ IS _ _ _ Hsl) as ([bp Hp] & Hi & Es).
    exists p, i, bp. split; [exact Hsl|]. split; [exact Hp|].
    rewrite (hosts_gbase _ _ _ IM _ _ Hp) in Hfst. split; [exact Hfst|]. split; [exact Es|]. split; [exact Hi|].
    pose proof Hp as [aip Hp']. pose proof (is_part _ _ _ IS bp p aip i Hp' Hi) as P. rewrite <- Es in P.
    unfold one5, tbit in P. destruct P as (_ & _ & _ & nAD & _ & _ & nBD & _).
    assert (D : s_groups st !! b <> None) by (rewrite Hb; discriminate).
    split. { intros [F|A]; [apply nBD| apply nAD]; split; auto. }
    fold (MR st p). split; [lia|].
    destruct (ish_nest _ _ ISH b g p i Hm MZ Hsl) as ((v3 & K3 & L3 & R3) & K2 & K1 & Q). rewrite (hosts_gbase _ _ _ IM _ _ Hp) in K2, K1, Q.
    exists v3, (byte_of ((snd b - snd bp - UNIT) / UNIT) 0), (byte_of ((snd b - snd bp - UNIT) / UNIT) 1).
    split; [exact K3|]. split; [exact L3|]. split; [exact K2|]. split; [exact K1|].
    rewrite u16_bytes by exact Q. rewrite (slot_start'_eq _ _ _ IM _ _ i Hp) in Es. rewrite Es. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hp).
    pose proof (stride_ge _ _ _ IG _ _ Hp) as [_ SMp]. unfold UNIT in *. pose proof (q_div (snd bp) (get_stride (MR st p)) i 0 SMp). lia.
Qed.

Lemma c_groups : ci_groups st.
Proof. intros b gh Hb. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Eg & _ & AI). exists m. auto. Qed.

Lemma c_group_inj : ci_group_inj st.
Proof. intros b1 b2 g H1 H2. exact (hosts_inj _ _ _ IM _ _ _ H1 H2). Qed.

Lemma c_slots : ci_slots st.
Proof. intros s g i Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as (A & B & C). split; [exact A|]. split; [exact C| exact B]. Qed.

Lemma c_slots_total : ci_slots_total st.
Proof. intros b g i Hb Hi. exact (is_total _ _ _ IS _ _ _ Hb Hi). Qed.

Lemma c_ghdr_unk : ci_ghdr_unk st.
Proof. intros b gh o Hb Ho. destruct (hdr_hosts _ _ _ _ _ INV _ _ Hb) as [m Hm]. exact (ish_ghdr _ _ ISH b m o Hm Ho). Qed.

Lemma c_hdr0 : ci_hdr0 st.
Proof. intros g b i Hm Hi. fold (MR st g) in *. exact (ish_hdr0 _ _ ISH b g i Hm ltac:(unfold cnt_of; lia)). Qed.

Lemma c_ctx : ci_ctx st.
Proof.
  pose proof (ia_ctx _ IA) as (C1 & C2 & C3 & C4). pose proof (ia_secret _ IA) as [S1 S2].
  split; [exact C2|]. split.
  { intros i. unfold bounces, ctx. destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 i v E)). }
  split. { intros i. unfold unmap_seq, ctx. destruct (c_unmap_seq (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C4 i v E)). }
  split. { intros sc. pose proof (f_usage _ _ _ _ _ INV ZB sc) as U. rewrite usage_strip in U. lia. }
  unfold ctx. destruct S2 as [(_ & E & _)|[_ E]]; rewrite E; lia.
Qed.

Lemma c_brk : ci_brk st.
Proof.
  intros rid off Hb. pose proof (ir_brk _ _ _ IR) as BR. unfold ctx in Hb. rewrite Hb in BR. destruct BR as (_ & r & Hr & Kr & _). exists r. auto.
Qed.

Lemma c_mem_hosts : ci_mem_hosts st.
Proof. intros q b H. exact (mem_hosts _ _ _ _ _ INV ZB _ _ H). Qed.

Lemma metakind_ng r : is_metakind r -> r_kind r <> RKGroup.
Proof. intros [K|K]; rewrite K; discriminate. Qed.

Lemma area_ng a : s_areas st !! a <> None -> ng_ptr st (Some a).
Proof.
  intros Ha. destruct (s_areas st !! a) as [ar|] eqn:E; [| congruence].
  destruct (ia_areas _ IA _ _ E) as ((r & Hr & MK & _) & _). exists r. split; [exact Hr| exact (metakind_ng _ MK)].
Qed.

Lemma c_mptrs : ci_mptrs st.
Proof.
  unfold ci_mptrs, ctx.
  split. { destruct (c_avail_meta (s_ctx st)) as [q|] eqn:E; [| exact I]. destruct (ia_availptr _ IA q E) as (r & Hr & MK). exists r. split; [exact Hr| exact (metakind_ng _ MK)]. }
  split. { destruct (c_meta_area_head (s_ctx st)) as [q|] eqn:E; [| exact I]. exact (area_ng _ (ia_head _ IA q E)). }
  split. { destruct (c_meta_area_tail (s_ctx st)) as [q|] eqn:E; [| exact I]. exact (area_ng _ (ia_tail _ IA q E)). }
  split. { destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:E; [| exact I].
           destruct (ir_cursor _ _ _ IR) as (_ & _ & CU). destruct (CU rid off E) as (r & Hr & MK & _). exists r. split; [exact Hr| exact (metakind_ng _ MK)]. }
  intros a ar Ha. destruct (a_next ar) as [a'|] eqn:E; [| exact I]. destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT). exact (area_ng _ (NXT a' E)).
Qed.

(* [comment removed for export] *)
Variable LB : list block.
Hypothesis CR : CORR st LB BL.

Lemma LB_blk_ok : Forall (blk_ok st) LB.
Proof.
  apply List.Forall_forall. intros blk Hblk.
  destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  destruct (is_blocks _ _ _ IS _ Hk) as (m' & i' & Hs & Hoff & _). cbn [bslot boff fst snd] in Hs, Hoff.
  pose proof (is_total _ _ _ IS _ _ _ Hm Hi) as Hs'. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm), <- Ec, Hs in Hs'. inversion Hs'; subst m' i'.
  constructor.
  - exists m, i, bm. rewrite C1. split; [exact Hs|]. split; [exact Hm|]. split; [rewrite Ec; reflexivity|]. split; [exact Hi|]. fold (MR st m).
    pose proof Hm as [ai Hb]. pose proof (is_part _ _ _ IS bm m ai i Hb Hi) as P. rewrite (slot_start'_eq _ _ _ IM _ _ i Hm), <- Ec in P.
    unfold one5, tbit in P. destruct P as (_ & _ & nAC & _ & _ & nBC & _).
    assert (C : In c (map bslot BL)) by (apply (in_map bslot _ _ Hk)).
    split. { intros [F|A]; [apply nBC| apply nAC]; split; auto. }
    exists off. split; [exact Ho|]. split; [rewrite Ea, Ec; unfold conc, get_region; cbn [fst snd]; rewrite Hr; lia|]. split; [rewrite C2; exact Fit|].
    pose proof (ish_blk _ _ ISH ((c, off), n) m i Hk Hs) as (K4 & K3 & K2 & K1 & Q & _). cbn [bslot boff bsize fst snd] in K4, K3, K2, K1, Q.
    unfold known, SHd in K4, K3, K2, K1. rewrite (hosts_gbase _ _ _ IM _ _ Hm) in K2, K1, Q.
    split; [unfold IB; replace (snd c + UNIT * off - 4) with (snd c + UNIT * off - 4) by lia; exact K4|].
    eexists _, _, _. unfold aadd; cbn [fst snd]. split; [exact K3|].
    split; [apply land31_idx; [destruct (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai' & _ & GO'); pose proof (g_li _ _ _ _ _ _ GO'); lia| lia]|].
    split; [exact K2|]. split; [exact K1|].
    rewrite u16_bytes by exact Q. rewrite Ec. cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm).
    pose proof (stride_ge _ _ _ IG _ _ Hm) as [_ SMm]. unfold UNIT in *. pose proof (q_div (snd bm) (get_stride (MR st m)) i off SMm). lia.
  - rewrite C1. exact NH.
  - rewrite C2. exact Hn.
Qed.

Lemma LB_blk_clear : Forall (blk_clear st LB) LB.
Proof.
  apply List.Forall_forall. intros blk Hblk.
  destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk) as (c & off & n & m & bm & i & r & Hk & C1 & C2 & Hm & Hi & Ec & NH & Hr & Kr & Ea & Ho & Hn & Fit).
  pose proof (sstart_succ st m i) as SS. pose proof (sstart0 _ _ _ IM _ _ Hm) as S0. pose proof (sstart_mono _ _ _ IG _ _ 0 i Hm ltac:(lia)) as SM0.
  pose proof (stride_ge _ _ _ IG _ _ Hm) as [SG SMm].
  destruct (group_in_region _ _ _ _ _ INV _ _ Hm) as (r' & Hr' & _ & A0 & GE). rewrite Hr in Hr'. inversion Hr'; subst r'.
  pose proof (hosts_GO _ _ _ _ _ INV _ _ Hm) as (ai & Hb & GO). pose proof (g_align _ _ _ _ _ _ GO) as [_ A16].
  constructor.
  - exists r. rewrite C1, Ec. cbn [fst]. split; [exact Hr|]. split; [exact Kr|].
    split; [unfold UNIT in *; lia|].
    split. { rewrite C2. rewrite (gend_eq st) in GE. pose proof (sstart_mono _ _ _ IG _ _ (i + 1) (m_last_idx (MR st m) + 1) Hm ltac:(lia)). unfold UNIT, IB in *. lia. }
    split. { rewrite Ea. destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & PG & _). unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hm). unfold UNIT, PGSZ in *.
             exact (mod16_addr _ _ _ _ _ PG A16 SMm). }
    intros a Ha. pose proof (f_blk_unknown _ _ _ _ _ INV _ CR blk r Hblk ltac:(rewrite C1, Ec; exact Hr) a Ha) as U. rewrite C1, Ec in U. exact U.
  - intros b gh Hgh Hf. rewrite C1, Ec in Hf. cbn [fst] in Hf. destruct (hdr_hosts _ _ _ _ _ INV _ _ Hgh) as [m2 Hm2].
    unfold conc, get_region. rewrite Hf, Hr. rewrite Ea, C2.
    destruct (sep_ghdr' m bm i m2 b Hm Hi ltac:(rewrite Ec in NH; exact NH) Hm2 Hf) as [A|A]; unfold UNIT, IB in *; lia.
  - intros blk' Hblk' NE Hf.
    destruct (LB_geo _ _ _ _ _ INV _ CR _ Hblk') as (c2 & o2 & n2 & m2 & bm2 & i2 & r2 & K2 & D1 & D2 & Hm2 & Hi2 & Ec2 & N2 & R2 & _ & A2 & O2 & P2 & F2).
    rewrite C1, D1, Ec, Ec2 in Hf. cbn [fst] in Hf. rewrite Hf, Hr in R2. inversion R2; subst r2.
    rewrite A2, Ea, D2, C2. pose proof (sstart_succ st m2 i2).
    assert (NE' : m2 <> m \/ i2 <> i). { destruct (aptr_eq_dec m2 m) as [->|]; [right| now left]. intros ->. apply NE. rewrite C1, D1, Ec, Ec2, Hf. reflexivity. }
    rewrite Ec in NH. rewrite Ec2 in N2.
    destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 bm2 i2 Hm2 Hf Hi2 NE' N2) as [A|A]; unfold UNIT, IB in *; lia.
Qed.
End CF.
End CEIL_WRAP_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac inst f INV CR :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV eq_refl) | exact (f _ _ _ _ _ INV eq_refl eq_refl)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV eq_refl _ CR) | exact (f _ _ _ _ _ INV eq_refl eq_refl _ CR) ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


Theorem areach_cinv_proof : forall {resv} st LB, AREACH_from resv st LB -> CINV st LB.
Proof.
  intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  constructor.
  - inst c_links INV CR.
  - inst c_heads INV CR.
  - inst c_homog INV CR.
  - inst c_gmeta INV CR.
  - inst c_groups INV CR.
  - inst c_group_inj INV CR.
  - inst c_slots INV CR.
  - inst c_slots_total INV CR.
  - inst c_ghdr_unk INV CR.
  - inst c_hdr0 INV CR.
  - inst LB_blk_ok INV CR.
  - inst LB_nodup INV CR.
  - inst c_ctx INV CR.
  - inst c_brk INV CR.
  - inst f_ticks INV CR.
  - inst c_mem_hosts INV CR.
  - inst c_mptrs INV CR.
  - inst LB_blk_clear INV CR.
Qed.
End CEIL_WRAP_2.

