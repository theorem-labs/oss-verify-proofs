(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4
  AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHit AsanRepCa AsanRepX.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_iface AF_place AF_fakestack_rep AF_kit AF_kit2 AF_kit3 AF_unwind AF_primary1b A_policy5 A_slack5 A_budget5 A_bundle A_benv5 A_init5 A_instD5 A_balloc5 A_bpolicy5 A_rtok5
  AF_alloc_iface AF_ca_iface AF_tkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sA_self : forall s, sA (aps_alloc s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma aps_alloc_sA : forall a s, aps_alloc (sA a s) = a.
Proof. intros a s. destruct s. reflexivity. Qed.

(* [comment removed for export] *)
Definition cp_st (E : aenv) (c : Z) (a : astate) : astate :=
  let l := get_cache a c in let x := List.last l 0 in let i := Z.of_nat (Nat.pred (length l)) in
  upd_cache_allocated (fun al => al + class_size c)
    (upd_cache_stale (fun st => <[c := <[i := x]> (match st !! c with Some m0 => m0 | None => ∅ end)]> st)
       (set_cache c (removelast l) a)).

Lemma cache_pop_hit_eval : forall E c a, get_cache a c <> [] ->
  cache_pop E c a = SRet (cp_st E c a, ONorm (Some (chunk_of_compact (ae_space_beg E) c (List.last (get_cache a c) 0)))).
Proof.
  intros E c a NE. unfold cache_pop. unfold abind at 1. cbn [aget sbind snd fst].
  destruct (get_cache a c) as [|y l0] eqn:EL; [congruence|].
  unfold abind at 1. cbn [aret sbind snd fst negb]. unfold abind at 1. cbn [aget sbind snd fst]. rewrite EL.
  unfold abind at 1. cbn [aupd sbind snd fst aret]. unfold AsanOps.aret, cp_st. rewrite EL. reflexivity.
Qed.

Lemma get_cache_nprimc : forall b c a c', get_cache (upd_nprimc b c a) c' = get_cache a c'.
Proof. intros b c a c'. destruct a; reflexivity. Qed.

Lemma pop_st_cp : forall E n a, pop_st n a = cp_st E (hc n) (upd_nprimc true (hc n) a).
Proof. intros E n a. unfold pop_st, cp_st. rewrite get_cache_nprimc. destruct a; reflexivity. Qed.

Lemma ca_op_hit_eval : forall E n a, from_primary n = true -> get_cache a (malloc_class n) <> [] ->
  ca_op E n a = SRet (pop_st n a, ONorm (Some (hab E n a))).
Proof.
  intros E n a PR NE. unfold ca_op. rewrite PR. unfold abind at 1. cbn [aupd sbind snd fst].
  change (malloc_class n) with (hc n) in *.
  rewrite (cache_pop_hit_eval E (hc n) (upd_nprimc true (hc n) a)) by (rewrite get_cache_nprimc; exact NE).
  rewrite <- (pop_st_cp E). unfold hab, hx. rewrite get_cache_nprimc. reflexivity.
Qed.

Corollary arun_ca_op_hit : forall E n a fuel orc, from_primary n = true -> get_cache a (malloc_class n) <> [] ->
  arun fuel (ca_op E n a) orc = Some (pop_st n a, ONorm (Some (hab E n a)), [], orc).
Proof. intros E n a fuel orc PR NE. rewrite (ca_op_hit_eval E n a PR NE). destruct fuel; reflexivity. Qed.

(* [comment removed for export] *)
Lemma pop_st_spec : forall E n a, from_primary n = true -> get_cache a (malloc_class n) <> [] ->
  1 <= hc n <= kLargestClassID -> AWf E [] [] a -> room a (hc n) ->
  AWf E [] [] (pop_st n a) /\ pframe (upd_nprimc true (hc n) a) (pop_st n a)
  /\ as_cache_inited (pop_st n a) = true /\ avail E [] (pop_st n a) (hc n) (hab E n a)
  /\ exists x, hab E n a = chunk_of_compact (ae_space_beg E) (hc n) x /\ (16 * x) mod class_size (hc n) = 0.
Proof.
  intros E n a PR NE HC WF ROOM.
  set (a0 := upd_nprimc true (hc n) a).
  assert (WF0 : AWf E [] [] a0) by (eapply AWf_same_core; [| exact WF]; subst a0; destruct a; repeat split; reflexivity).
  assert (ROOM0 : room a0 (hc n)) by (subst a0; unfold room, get_region in *; destruct a; exact ROOM).
  pose proof (cache_pop_spec E [] [] a0 (hc n) HC WF0 ROOM0 a0 eq_refl) as X.
  rewrite (cache_pop_hit_eval E (hc n) a0) in X by (subst a0; rewrite get_cache_nprimc; exact NE).
  cbn [sall leaf_ok] in X. rewrite <- (pop_st_cp E) in X.
  replace (chunk_of_compact (ae_space_beg E) (hc n) (List.last (get_cache a0 (hc n)) 0)) with (hab E n a) in X
    by (subst a0; unfold hab, hx; rewrite get_cache_nprimc; reflexivity).
  destruct X as (W1 & PF & _ & _ & CI & AV & EX). split; [exact W1|]. split; [exact PF|]. split; [exact CI|]. split; [exact AV| exact EX].
Qed.

(* [comment removed for export] *)
Lemma Sh_cache_block : forall E (P : list Z) (D : list batch) s c x a,
  AWf E P D s -> 1 <= c <= kLargestClassID -> In x (get_cache s c) ->
  chunk_of_compact (ae_space_beg E) c x <= a < chunk_of_compact (ae_space_beg E) c x + class_size c ->
  Sh E s a = Some kAsanHeapLeftRedzoneMagic.
Proof.
  intros E P D s c x a WF Hc Hx Ha. unfold Sh.
  pose proof WF as (WE & WR & (_ & _ & WC3) & _). destruct (WC3 c Hc) as (_ & _ & Cx). destruct (Cx x Hx) as (CV & _ & _).
  destruct CV as (k & K0 & KE & KB). destruct (proj2 WR c Hc) as (R1 & _). cbv zeta in R1. unfold region_of in KB, R1.
  pose proof (class_size_mod c Hc) as [_ CS].
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply orb_true_iff. left. apply (existsb_In _ _ c); [apply In_ziota; unfold kLargestClassID in Hc; lia|].
    apply andb_true_iff. unfold region_of. rewrite KE in Ha. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Ha K0 KB R1 CS; nia. }
  rewrite RM. cbn [orb]. destruct (find_chunk s a) as [cm|] eqn:FC; [| reflexivity].
  exfalso. destruct (find_chunk_some s a cm FC) as (cb & Hcb & R).
  pose proof (cache_block_clear E P D s c x cb cm WF Hc Hx Hcb) as CL. rewrite blk_hi_span in CL. unfold blk_lo in CL.
  clear -Ha R CL. lia.
Qed.

(* [comment removed for export] *)
Lemma room_of_binv : forall a c, binv a -> 1 <= c <= kLargestClassID -> 0 <= as_nprim_ever a <= 12000 -> room a c.
Proof.
  intros a c HB Hc NP. unfold room. pose proof (binv_mapped_user a c HB Hc) as [X [Y1 Y2]].
  pose proof (class_size_mod c Hc) as [_ CS]. unfold b24, kNB, kBatchClass, kUserMapSize, kFreeArrayOffset in *.
  destruct (c =? 24); clear -X Y1 Y2 NP CS; nia.
Qed.

(* [comment removed for export] *)
Lemma blocks_sep_of : forall E a mo, env0_ok5 E -> AWf E [] [] a -> AKern E a mo -> blocks_sep E a.
Proof.
  intros E a mo ENV WF K. pose proof alloc_ceiling_range as CR.
  pose proof ENV as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & _).
  destruct WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  assert (SECR : forall sc r, In sc (as_sec a) -> In r (ae_reserved E) -> sc_map_beg sc + sc_map_size sc <= fst r \/ fst r + snd r <= sc_map_beg sc).
  { intros sc r Hsc Hr. destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). exact (RSV _ Hr). }
  pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & S3 & S4 & S5).
  unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in N3, N4.
  intros b len [[Hb ->]|[Hb ->]].
  - destruct Hb as [<-|Hb].
    + split; [unfold app_mem; rewrite kHighMemBeg_val, kLowAppEnd_val; unfold kDepotNodeBlockBytes in *; clear -N3 CR; lia|].
      split; [unfold kDepotNodeBlockBytes in *; clear -N3; lia|]. split; [exact N7|]. split; [| split; [exact N8| exact N5]].
      intros sc Hsc. destruct (SECR sc _ Hsc N1); cbn [fst snd] in *; [right| left]; lia.
    + destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & WEfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEimg & _).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; [left| right]; lia|].
      unfold img_sep. destruct (B5 _ WEimg) as [X|X]; [left; exact X| right]. destruct (ae_img E); cbn [fst snd] in *; lia.
  - destruct Hb as [<-|Hb].
    + split; [unfold app_mem; rewrite kHighMemBeg_val, kLowAppEnd_val; unfold kStoreBlockBytes in *; clear -N4 CR; lia|].
      split; [unfold kStoreBlockBytes in *; clear -N4; lia|]. unfold kStoreBlockBytes. split; [exact S1|]. split; [exact S2|]. split; [exact N9| exact N6].
    + destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & WEfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WEimg & _).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; [left| right]; lia|].
      unfold img_sep. destruct (B5 _ WEimg) as [X|X]; [left; exact X| right]. destruct (ae_img E); cbn [fst snd] in *; lia.
Qed.


(* [comment removed for export] *)
Lemma pop_keep : forall E n a,
     (csmall a -> csmall (pop_st n a)) /\ (sstats_ok a -> sstats_ok (pop_st n a)) /\ (res_ok a -> res_ok (pop_st n a)) /\ (AQbound a -> AQbound (pop_st n a)) /\ (depot_inv E a -> depot_inv E (pop_st n a))
  /\ live_blocks (pop_st n a) = live_blocks a /\ as_sec (pop_st n a) = as_sec a
  /\ as_nprim_ever (pop_st n a) = as_nprim_ever a + 1 /\ as_ndepot_ins (pop_st n a) = as_ndepot_ins a /\ as_residue (pop_st n a) = as_residue a
  /\ same_fp a (pop_st n a) /\ gapR (pop_st n a) = gapR a + 4096 * 160 /\ gapD (pop_st n a) = gapD a
  /\ as_regions (pop_st n a) = as_regions a /\ as_ptr_committed (pop_st n a) = as_ptr_committed a
  /\ as_node_blocks (pop_st n a) = as_node_blocks a /\ as_store_blocks (pop_st n a) = as_store_blocks a.
Proof.
  intros E n a.
  assert (RB : regions_bytes (pop_st n a) = regions_bytes a) by (unfold regions_bytes, get_region; destruct a; reflexivity).
  assert (GR : gapR (pop_st n a) = gapR a + 4096 * 160) by (unfold gapR; rewrite RB; destruct a; cbn -[Z.add Z.mul Z.sub regions_bytes]; lia).
  destruct a. unfold same_fp, gapD. rewrite RB.
  repeat lazymatch goal with |- _ /\ _ => split end; first [intros H; exact H | reflexivity | exact GR].
Qed.

(* [comment removed for export] *)
Lemma live_block_off_thread : forall E a blo bsz, AWf E [] [] a -> In (blo, bsz) (live_blocks a) ->
  blo + bsz <= alloc_ceiling /\ (blo + bsz <= ae_thread E \/ ae_thread E + 4096 <= blo).
Proof.
  intros E a blo bsz WF LIVE. pose proof WF as (WE & WR & _ & _ & _ & (_ & _ & WS3 & _) & _).
  destruct (live_block_loc E [] [] a blo bsz WF LIVE) as (k & cm & Hk & _ & _ & _ & L1 & L2 & LOC).
  rewrite blk_hi_span in L2. unfold blk_lo in L1.
  destruct WE as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & _ & _ & E13 & _ & E15 & _ & _ & _ & E19 & _).
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & R1 & R2). rewrite blk_hi_span in R2. unfold blk_lo, region_beg in R1, R2.
    destruct (proj2 WR c' Hc') as ((_ & _) & _ & R3 & _). unfold region_of in R3.
    unfold kFreeArrayOffset, kRegionSize, kSpaceSize, kLargestClassID in *. clear -L1 L2 R1 R2 R3 Hc' E3 E4 E5 E19. split; nia.
  - destruct LOC as (sc & Hsc & R1 & R2). rewrite blk_hi_span in R2. unfold blk_lo in R1.
    destruct (WS3 sc Hsc) as (_ & _ & CE & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X.
    unfold kPageSize in *. clear -L1 L2 R1 R2 CE X. split; lia.
Qed.

(* [comment removed for export] *)
Section CaT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation INST := 0xaa518.

(* [comment removed for export] *)
Definition PP (s1 : aps) (mo1 : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo1) (aSc s1) x.
Lemma PP_KIP : forall s1 mo1 R R', ATOKc R R' s1 mo1 -> KIP (aSc s1) (aNc s1) (aEBc s1) (PP s1 mo1) mo1.
Proof. intros s1 mo1 R R' T1. split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ T1)| intros x Hx; exact Hx]. Qed.

(* [comment removed for export] *)
Definition SIDE_hit (s : aps) (n : Z) : Prop := from_primary n = true /\ get_cache (aps_alloc s) (malloc_class n) <> [].

Theorem ca_srz_hit : ca_srz_case E0 FSB0 HR0 L0 RES0 EB0 PL0 SIDE_hit.
Proof.
  intro. intros until K. cbv zeta. intros [PR NE] KN TOK CHG GC AIV ABUD Hn NBIG SK LOC LO SPA SPH TP CONT.
  pose proof alloc_ceiling_range as CR. pose proof A_bundle.kHighMemBeg_val as KHB.
  destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss & Hcs).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & RLE).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  assert (EE : aps_env s = E0) by (destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _); exact EE).
  set (a := aps_alloc s) in *.
  set (c := hc n). assert (Ec : malloc_class n = c) by reflexivity. rewrite Ec in NE.
  set (l := get_cache a c) in *. set (x := List.last l 0). set (ab := hab E0 n a).
  assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
  pose proof (malloc_class_ok n N64) as [HCc NEEDc]. rewrite Ec in HCc, NEEDc.
  assert (NEED : needed n = needed1 n) by (unfold needed; rewrite PR; reflexivity).
  pose proof (needed1_ge n) as NG.
  assert (SZ : 1 <= needed n <= 65536) by (rewrite NEED; pose proof (class_size_mod c HCc) as [_ CS]; clear -NG NEEDc CS Hn; lia).
  assert (Ecc : class_id (needed n) = c) by (rewrite NEED; reflexivity).
  (* [comment removed for export] *)
  pose proof Hrep as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof (Hwf) as (WE & WR & WC & _). pose proof WC as (_ & WCI & WC3).
  assert (CI : as_cache_inited a = true).
  { destruct (as_cache_inited a) eqn:CI0; [reflexivity| exfalso]. destruct (WCI eq_refl) as [CE _]. apply NE. subst l. unfold get_cache. rewrite CE. reflexivity. }
  destruct (Tcache c ltac:(unfold kNumClasses, kLargestClassID in *; clear -HCc; lia)) as [PCR0 (cjunk & CARR & CLEN0)].
  unfold percls_cells in PCR0. fold l in PCR0, CARR, CLEN0. rewrite CI in PCR0. rewrite (row_max_count_reg E0 c HCc), (row_class_size_reg E0 c HCc) in PCR0.   (* [comment removed for export] *)
  set (cws := map (fun z : Z => Z_to_bv 64 z) l ++ cjunk) in CARR.
  assert (CLEN : length cws = 16%nat) by (subst cws; rewrite length_app, length_map; exact CLEN0).
  assert (LLEN : (1 <= length l)%nat) by (clear -NE; subst l; destruct (get_cache a c); [exfalso; exact (NE eq_refl)| cbn; lia]).
  set (cnt := zlen l) in *.
  assert (CNT : 1 <= cnt <= 16) by (subst cnt; unfold zlen; clear -LLEN CLEN0; lia).
  assert (CNTH : nth_error cws (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 x)).
  { subst cws cnt x. unfold zlen. replace (Z.to_nat (Z.of_nat (length l) - 1)) with (Nat.pred (length l)) by (clear -LLEN; lia).
    apply nth_error_map_app. apply last_nth_error. exact NE. }
  (* [comment removed for export] *)
  assert (INx : In x l) by (subst x; rewrite (app_removelast_last 0 NE) at 2; apply in_app_iff; right; left; reflexivity).
  destruct (WC3 c HCc) as (_ & _ & WCx). destruct (WCx x INx) as (CARVED & XAL & XNF).
  destruct (proj2 WR c HCc) as (RG1 & RG2 & RG3 & _). cbv zeta in RG1, RG2, RG3. unfold region_of in RG1, RG2, RG3.
  pose proof CARVED as (kx & Kx0 & KxE & KxB). unfold chunk_of_compact, region_beg in KxE. unfold region_of in KxB.
  pose proof (class_size_mod c HCc) as [CSM CSZ].
  assert (XR : 0 <= x < 2^28) by (unfold kFreeArrayOffset in RG3; unfold kRegionSize in KxE; clear -Kx0 KxE KxB RG1 RG3 CSZ; nia).
  assert (Eab : ab = SB + c * 2^32 + 16 * x) by (subst ab; unfold hab, hx, chunk_of_compact, region_beg, kRegionSize; reflexivity).
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & _).
  (* [comment removed for export] *)
  destruct PL0OK as (_ & _ & (TR1 & TR2 & _) & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ Hrt) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof ENV as ENV'. destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  (* [comment removed for export] *)
  assert (ISB : rw_cells asegs m 0xaa538 [C8 (Z_to_bv 64 SB)]).
  { pose proof Rins as (Iin & _). unfold ae_instance in Iin. rewrite IC0 in Iin. cbn [aic_instance asan_ic kInsSpaceBeg Z.add] in Iin.
    apply (rwc_split asegs m _ [C8 (Z_to_bv 64 SB)] [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (ae_region_info E0)); C1 (Z_to_bv 8 0)]) in Iin.
    exact (proj1 Iin). }
  assert (CST : rw_cells asegs m (T + 208 + 2576) [C8 (Z_to_bv 64 (as_cache_allocated a))]).
  { unfold kThrCacheStats in Tcst. apply (rwc_split asegs m _ [C8 (Z_to_bv 64 (as_cache_allocated a))] [C8 (Z_to_bv 64 (as_cache_mapped a))]) in Tcst.
    replace (T + 208 + 2576) with (T + (208 + 2560) + 16) by (clear; lia). exact (proj1 Tcst). }
  unfold kThrCache, kPerClassSize in PCR0, CARR.
  (* [comment removed for export] *)
  set (P := PP s mo).
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, PP. apply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PDAT : forall y k, 0xa4000 <= y -> y + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, PP. apply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENV' ENV0); clear -H1 H2; lia. }
  assert (PCA : forall y k, T + 208 <= y -> y + Z.of_nat k <= T + 208 + 2584 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P, PP. apply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); clear -H1 H2; lia. }
  pose proof (PP_KIP s mo R0 R0' ATK) as KIP0.
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg asegs (aSc s) (aNc s) (aEBc s) P).
  { eapply (ca_hit_walk_all P ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo SB (T + 208) (needed n) cnt
              (as_cache_allocated a) (Z_to_bv 64 (max_count c)) cws x);
      rewrite ?Ecc;
      [ exact SK | exact LOC | clear -LO; unfold K_CA in *; lia | clear -SPH; lia | exact Hmi | exact SZ | exact CNT
      | clear -WE2 WE3 WE4 WE5 CR KHB; unfold kSpaceSize in *; lia | exact WE1
      | clear -Tlo Timg; lia | clear -Thi; lia | clear -T8; Z.div_mod_to_equations; lia
      | exact ISB | exact PCR0 | exact CARR | exact CLEN | exact CNTH | clear -XR; lia | exact CST
      | exact PSTK | exact PDAT | exact PCA ]. }
  { exact KIP0. }
  intros ms2 mo2 HQ AG2 KIP2.
  destruct HQ as (t0' & t1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & MI2 & SK2 & ROW2 & CST2).
  rewrite ?Ecc in MU2, ROW2, CST2.
  pose proof (magree_frame _ _ AG2) as (Ffds2 & Fvm2 & Flz2 & Ffs2 & Fh2 & Ftid2 & _).
  destruct KIP2 as [KIA2 _].
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG2 KIA2) as TOK2.
  pose proof (AKern_frame _ _ _ _ Fvm2 Flz2 Hkern) as AK2.
  (* [comment removed for export] *)
  destruct ABUD as (BU1 & BU2 & BU3).
  assert (ACH : acharge n = kCmPrim) by (unfold acharge; rewrite PR; reflexivity). unfold kCmPrim in ACH.
  assert (NP12 : 0 <= as_nprim_ever a <= 12000) by (unfold kInitialCredit in BU3; clear -BU1 BU2 BU3 ACH; lia).
  pose proof (room_of_binv a c Hbinv HCc NP12) as ROOM.
  destruct (pop_st_spec E0 n a PR NE HCc Hwf ROOM) as (WF1 & PF & CI1 & AV & EXX).
  set (a1 := pop_st n a) in *.
  pose proof (pop_keep E0 n a) as (Kcs & Ksst & Kres & Kqb & Kdi & Klive & Ksec & Knp & Knd & Kresd & Ksfp & KgR & KgD & Kreg & Kptr & Knb & Ksb). fold a1 in Kcs, Ksst, Kres, Kqb, Kdi, Klive, Ksec, Knp, Knd, Kresd, Ksfp, KgR, KgD, Kreg, Kptr, Knb, Ksb.
  assert (AK1 : AKern E0 a1 mo2) by (eapply AKern_ext; [exact Kreg| exact Kptr| exact Ksec| exact Knb| exact Ksb| exact AK2]).
  (* [comment removed for export] *)
  assert (OUT : forall z, z < bv_unsigned sp - 48 -> (z < T + 208 + 80 * c \/ T + 208 + 80 * c + 4 <= z) -> (z < T + 208 + 2576 \/ T + 208 + 2584 <= z) ->
                0 <= z -> m2 (wa z) = m (wa z)).
  { intros z Z1 Z2 Z3 Z0. apply MU2. rewrite wa_unsigned by (clear -Z0 Z1 SPH; lia). cbn [outside]. clear -Z1 Z2 Z3. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  assert (REP1 : ARep asegs E0 (DepotR asegs E0) a1 m2).
  { subst a1. eapply (ARep_capop asegs E0 n a m m2 (bv_unsigned sp - 48) WM2).
    - intros z Hz NF. unfold FPWca in NF. unfold kThrCache, kPerClassSize, kThrCacheStats in NF. fold c in NF. apply OUT; clear -Hz NF; lia.
    - clear -LOC LO; unfold K_CA in LO; lia.
    - exact Hrep.
    - exact Hwf.
    - exact (blocks_sep_of E0 a mo ENV0 Hwf Hkern).
    - clear -Tlo Thi Timg. repeat split; lia.
    - intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia.
    - rewrite EI1. clear; lia.
    - exact IMGR.
    - unfold kNumClasses, kLargestClassID in *. clear -HCc. lia.
    - exact NE.
    - exact CI.
    - unfold kThrCache, kPerClassSize. fold c.
      apply (rwc_split asegs m2 _ [C4 (Z_to_bv 64 (cnt - 1))] [C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c))]) in ROW2.
      replace (T + 208 + 80 * c) with (T + 208 + 80 * c) by reflexivity. exact (proj1 ROW2).
    - unfold kThrCacheStats. replace (T + 2768 + 16) with (T + 208 + 2576) by (clear; lia). exact CST2.
    - exists mo. exact Hkern.
    - exact TDN. }
  (* [comment removed for export] *)
  destruct PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & _ & CT & DT & _).
  pose proof CR0 as (_ & (CP1 & CP2 & _) & _). pose proof DR0 as (_ & (DP1 & DP2 & _) & _).
  assert (RT2 : rt_misc5 FSB0 PL0 E0 m2).
  { apply (rt_misc5_agree E0 FSB0 PL0 m m2 Hrt). intros z Hz. destruct (rt_fpc_where E0 FSB0 PL0 z Hz) as [(Z1 & _)|RH].
    - apply OUT; clear -Z1 LOC LO CR Timg HCc; unfold K_CA, kLargestClassID in *; lia.
    - unfold rt_high2 in RH. apply OUT; clear -RH LOC LO CR Tlo Thi CT DT CP1 CP2 CC1 CC2 DP1 DP2 DD1 DD2 HCc; unfold K_CA, kLargestClassID in *; lia. }
  (* [comment removed for export] *)
  assert (TOK1 : RTOKc (C - ca_cost n) (C' - ca_gcost n) (sA a1 s) mo2).
  { unfold ca_cost, ca_gcost. rewrite PR. replace (C' - 0) with C' by (clear; lia).
    rewrite <- (sA_self s) in TOK2. fold a in TOK2.
    apply (RTOK_same_fp_pay E0 FSB0 HR0 L0 RES0 EB0 C C' (C - 160) s a a1 mo2 TOK2 Ksfp); clear -KgR KgD CHG ACH; lia. }
  (* [comment removed for export] *)
  assert (AB8 : ab = 8 * (ab / 8)) by (rewrite Eab; clear -WE1; Z.div_mod_to_equations; lia).
  assert (CS8 : class_size c = 8 * (class_size c / 8)) by (clear -CSM; Z.div_mod_to_equations; lia).
  assert (ABR : kHighMemBeg <= ab /\ ab + class_size c <= alloc_ceiling).
  { pose proof (carved_in_space E0 a c _ HCc WR CARVED) as [I1 I2]. fold x in I1, I2. change (chunk_of_compact SB c x) with ab in I1, I2 || rewrite <- Eab in I1, I2 || idtac.
    unfold hab, hx in *. unfold kRegionSize, kSpaceSize in *. clear -I1 I2 WE2 WE3 WE4 WE5 Eab. lia. }
  assert (SHm : rw_cells asegs m (kShadowBase + ab / 8) [CB (Z.to_nat (class_size c / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8)))]).
  { apply shadow_join; [| clear -CSZ CS8; lia]. intros g Hg. apply (Rsh g kAsanHeapLeftRedzoneMagic).
    apply (Sh_cache_block E0 [] [] a c x); [exact Hwf| exact HCc| exact INx|]. fold ab. rewrite <- Eab || idtac.
    change (chunk_of_compact SB c x) with (hab E0 n a). fold ab. clear -Hg AB8 CS8. lia. }
  assert (SH2 : rw_cells asegs m2 (kShadowBase + ab / 8) [CB (Z.to_nat (class_size c / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8)))]).
  { eapply (AF_unwind.rw_cells_agree asegs m m2); [| exact SHm]. intros z Hz. cbn [cells_size csize Nat.add] in Hz. rewrite Nat.add_0_r, Z2Nat.id in Hz by (clear -CSZ CS8; lia).
    pose proof (proj1 WF1) as WEx. pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE14 & _).
    unfold app_mem in WE14. rewrite KHB, kLowAppEnd_val in WE14. unfold kShadowBase in Hz. rewrite KHB in ABR.
    apply OUT; clear -Hz WE14 ABR CR LOC LO AB8 CS8 HCc; unfold K_CA, kLargestClassID in *; lia. }
  (* [comment removed for export] *)
  apply CONT with (a1 := a1) (ab := ab). unfold ca_post.
  split; [exact SK2|]. split; [exact WM2|].
  split.
  { exists [(bv_unsigned sp - 48, bv_unsigned sp); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 208 + 2576, T + 208 + 2584)].
    split; [exact MU2|]. split.
    - repeat (apply Forall_cons; [unfold aw_ok; cbn [fst snd]|]); [.. | apply Forall_nil].
      + left. clear -LO; unfold K_CA in LO; lia.
      + right; right; left. exists (T + kThrCache, kPerClassSize * kNumClasses). split; [unfold arep_thr_ranges; do 3 right; left; reflexivity|]. cbn [fst snd]. unfold kThrCache, kPerClassSize, kNumClasses, kLargestClassID in *. clear -HCc. lia.
      + right; right; left. exists (T + kThrCacheStats + 16, 16). split; [unfold arep_thr_ranges; do 4 right; left; reflexivity|]. cbn [fst snd]. unfold kThrCacheStats. clear. lia.
    - repeat (apply Forall_cons; [cbn [fst snd]; intros blo bsz LIVE; destruct (live_block_off_thread E0 a blo bsz Hwf LIVE) as [LB1 LB2]|]); [.. | apply Forall_nil].
      + right; right. clear -LB1 LOC LO; unfold K_CA in LO; lia.
      + right. unfold kLargestClassID in HCc. clear -LB2 HCc. lia.
      + right. clear -LB2. lia. }
  split; [exists 1%nat, [], [], []; subst a1; exact (arun_ca_op_hit E0 n a 1%nat [] PR NE)|].
  split; [split; [exact WF1| split; [exact AK1| split; [exact (Kres Hres)| split; [exact (Kqb Hqb)| split; [exact (Kdi Hdi)| split; [exact MI2| split; [exact RT2| split; [exact (Ksst Hss)| exact (Kcs Hcs)]]]]]]]]|].
  split; [exact TOK1|].
  split; [rewrite Ffs2; reflexivity|]. split; [rewrite Ffds2; reflexivity|]. split; [rewrite Ftid2; reflexivity|].
  split; [rewrite Eab, ?Ecc; reflexivity|].
  split; [apply ARep_ARepX; exact REP1|].
  unfold ca_span. rewrite PR, Ec. split.
  { exists (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8))). split; [exact SH2| intros _; reflexivity]. }
  split; [exact CI1|]. split; [exact AV| exact EXX].
Qed.
End CaT.
End RC__1.
