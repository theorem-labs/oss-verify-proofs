(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap fin_maps.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf10
  AsanBudget AsanBudget2 AsanSecCount AsanDepot AsanFrame AsanRepFrame AsanRepFrame2 AsanHit AsanRepHit AsanRepX AsanRealloc AsanRepEnq AsanRepX2 AsanRepNew AsanRepTail.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_base A_iface AF_place AF_fakestack_rep A_live A_bundle A_benv5 A_balloc5 AF_alloc_iface AF_ca_iface AF_caT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Lemma tspan_ca_span : forall n, tspan n = ca_span n. Proof. intros n. reflexivity. Qed.

(* [comment removed for export] *)
Lemma arun_ret : forall {R} (s : astate) (o : aout R) orc, arun 0%nat (SRet (s, o)) orc = Some (s, o, [], orc).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Section RUN.
Variable E : aenv.
Variables (a a1 a2 : astate) (n ab id : Z) (key : list Z).
Variables (fA : nat) (orcA : list aans) (evsA : list aev) (orcA' : list aans) (fD : nat) (orcD : list aans) (evsD : list aev) (orcD' : list aans).
Hypothesis Hn : 0 < n <= 2^27.
Hypothesis RUNA : arun fA (ca_op E n a) orcA = Some (a1, ONorm (Some ab), evsA, orcA').
Hypothesis RUND : arun fD (depot_put E key a1) orcD = Some (a2, ONorm id, evsD, orcD').
Hypothesis FRESH : as_chunks a2 !! tcb n ab = None.

(* [comment removed for export] *)
Lemma arun_orc_app : forall {R} f (t : stree aev aans (astate * aout R)) orc s o evs orc',
  arun f t orc = Some (s, o, evs, orc') -> exists used, orc = used ++ orc' /\ forall tail, arun f t (used ++ tail) = Some (s, o, evs, tail).
Proof.
  intros R f. induction f as [|f IH]; intros t orc s o evs orc' H; destruct t as [[s0 o0]|e k]; cbn in H |- *.
  - injection H as <- <- <- <-. exists []. split; [reflexivity| intros tail; reflexivity].
  - destruct orc; discriminate.
  - injection H as <- <- <- <-. exists []. split; [reflexivity| intros tail; reflexivity].
  - destruct orc as [|x rest]; [discriminate|].
    destruct (arun f (k x) rest) as [[[[s1 o1] evs1] orc1]|] eqn:HR; [| discriminate]. injection H as <- <- <- <-.
    destruct (IH _ _ _ _ _ _ HR) as (used & -> & RUN). exists (x :: used). split; [reflexivity|].
    intros tail. cbn [app]. rewrite (RUN tail). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arun_poison_zero : forall s u L tail, 0 <= L ->
  exists f orc evs, arun f (poison_zero u L s) (orc ++ tail) = Some (s, ONorm tt, evs, tail).
Proof.
  intros s u L tail HL. unfold poison_zero. exists 0%nat, [], []. reflexivity.
Qed.

Theorem arun_amalloc_core : exists fuel orc evs orc',
  arun fuel (amalloc_core E key n a) orc = Some (tail_st n ab id a2, ONorm (Some (tub n ab)), evs, orc').
Proof.
  destruct (arun_orc_app _ _ _ _ _ _ _ RUNA) as (uA & _ & RA).
  destruct (arun_orc_app _ _ _ _ _ _ _ RUND) as (uD & _ & RD).
  destruct (arun_poison_zero (upd_dead (delete (tcb n ab)) (upd_chunks (fun ch => <[tcb n ab := tcm n ab id]> ch) a2)) (tub n ab) ((req n / 8) * 8) []
              ltac:(unfold req; clear -Hn; Z.div_mod_to_equations; lia)) as (fP & uP & evsP & RP). rewrite app_nil_r in RP.
  exists (fA + (fD + (fP + 0)))%nat, (uA ++ uD ++ uP), (evsA ++ (evsD ++ (evsP ++ []))), [].
  unfold amalloc_core. unfold acheck at 1. replace (n <? 2 ^ 40) with true by (symmetry; apply Z.ltb_lt; clear -Hn; lia).
  unfold abind at 1. cbn [aret sbind fst snd].
  (* [comment removed for export] *)
  pose proof (RA (uD ++ uP)) as RA'. unfold ca_op, abind in RA'. cbn [aupd sbind fst snd] in RA'.
  unfold abind at 1. cbn [aupd sbind fst snd]. unfold abind at 1.
  change (malloc_class n) with (class_id (needed1 n)) in RA'.
  eapply (arun_sbind _ _ fA (fD + (fP + 0))%nat); [exact RA'|].
  cbn [sbind fst snd]. unfold abind at 1.
  (* [comment removed for export] *)
  eapply (arun_sbind _ _ fD (fP + 0)%nat); [exact (RD uP)|].
  cbn [sbind fst snd]. unfold abind at 1. cbn [aget sbind fst snd]. unfold abind at 1. unfold acheck.
  change (ab + rz_size n - kChunkHeaderSize) with (tcb n ab). rewrite FRESH. cbn [aret sbind fst snd].
  unfold abind at 1. cbn [aupd sbind fst snd].
  unfold abind at 1.
  eapply (arun_sbind _ _ fP 0%nat).
  - match goal with |- arun _ ?t _ = _ => change t with (poison_zero (tub n ab) ((req n / 8) * 8) (upd_dead (delete (tcb n ab)) (upd_chunks (fun ch => <[tcb n ab := tcm n ab id]> ch) a2))) end.
    exact RP.
  - cbn [sbind fst snd]. unfold abind. cbn [aupd sbind fst snd aret]. reflexivity.
Qed.
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CASEC.
Variable E : aenv.
Definition SECM (S0 : list secchunk) (s : astate) : Prop := forall sc, In sc S0 -> In sc (as_sec s).
Ltac secm_same := match goal with H : SECM ?d ?st |- SECM ?d _ =>
  unfold SECM in *; first [exact H | destruct st; cbn in *; first [exact H | intros sc__ Hsc__; apply in_app_iff; left; exact (H sc__ Hsc__)]] end.
Lemma ensure_secm : forall d c nf, presW (SECM d) (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; secm_same. Qed.
Lemma populate_secm : forall d c r, presW (SECM d) (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_secm; secm_same. Qed.
Lemma gfa_secm : forall d c n, presW (SECM d) (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_secm; secm_same. Qed.
Lemma refill_secm : forall d c, presW (SECM d) (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_secm; secm_same. Qed.
Lemma cache_pop_secm : forall d c, presW (SECM d) (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_secm; secm_same. Qed.
Lemma sec_alloc_secm : forall d nd, presW (SECM d) (sec_alloc E nd).
Proof. intros; unfold sec_alloc. pw; try apply call_mmap_anon_W; try apply call_mmap_fixed_W; secm_same. Qed.
Lemma ca_op_secm : forall d n, presW (SECM d) (ca_op E n).
Proof. intros; unfold ca_op. pw; [secm_same| apply cache_pop_secm| apply sec_alloc_secm]. Qed.
Theorem ca_op_sec : forall s0 n, hoareW (fun s => s = s0) (ca_op E n) (fun s' _ => forall sc, In sc (as_sec s0) -> In sc (as_sec s')).
Proof.
  intros s0 n. eapply hoareW_conseq; [apply (ca_op_secm (as_sec s0) n)| intros s ->; intros sc H; exact H| intros s' r H; exact H].
Qed.
End CASEC.

Section AT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).

Variables (a a1 a2 : astate) (mo3 : Model) (n ab id : Z) (key : list Z).
Variables (fA : nat) (orcA : list aans) (evsA : list aev) (orcA' : list aans) (fD : nat) (orcD : list aans) (evsD : list aev) (orcD' : list aans).
#[local] Notation a' := (tail_st n ab id a2).
#[local] Notation prim := (from_primary n).
#[local] Notation c := (malloc_class n).
#[local] Notation ub := (tub n ab).
#[local] Notation cb := (tcb n ab).

(* [comment removed for export] *)
Hypothesis WF0 : AWf E0 [] [] a.
Hypothesis RES0 : res_ok a.
Hypothesis QB0 : AQbound a.
Hypothesis DI0 : depot_inv E0 a.
Hypothesis BI0 : binv a.
Hypothesis SS0 : sstats_ok a.
Hypothesis CS0 : csmall a.
Hypothesis ABUD : abudget_pre a n.
Hypothesis Hn : 0 < n <= 2^27.
Hypothesis NBIG : nbig_live a <= 8000.
(* [comment removed for export] *)
Hypothesis RUNA : arun fA (ca_op E0 n a) orcA = Some (a1, ONorm (Some ab), evsA, orcA').
Hypothesis WF1 : AWf E0 [] [] a1.
Hypothesis SS1 : sstats_ok a1.
Hypothesis SIDE : if prim then as_cache_inited a1 = true /\ avail E0 [] a1 c ab /\ (exists x, ab = chunk_of_compact SB c x /\ (16 * x) mod class_size c = 0)
                  else exists r0, ab = r0 + kPageSize /\ as_sec a1 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E0 a r0 (map_size n).
(* [comment removed for export] *)
Hypothesis KEY : depot_ok E0 a1 key /\ zlen key + 1 <= 32.
Hypothesis RUND : arun fD (depot_put E0 key a1) orcD = Some (a2, ONorm id, evsD, orcD').
Hypothesis WF2 : AWf E0 [] [] a2.
Hypothesis AK2 : AKern E0 a2 mo3.
(* [comment removed for export] *)
Hypothesis EIMG : fst (ae_img E0) = 0x10000 /\ 0x5f3000 <= snd (ae_img E0).

(* [comment removed for export] *)
Hypothesis CAF_DK : as_ndepot_ins a1 = as_ndepot_ins a /\ as_keys a1 = as_keys a /\ as_frames a1 = as_frames a /\ as_node_blocks a1 = as_node_blocks a
  /\ as_store_blocks a1 = as_store_blocks a /\ as_store_stored a1 = as_store_stored a /\ as_chunks a1 = as_chunks a /\ as_dead a1 = as_dead a
  /\ as_tq a1 = as_tq a /\ as_gq a1 = as_gq a.
Hypothesis CAF_NP : as_nprim_ever a1 = as_nprim_ever a + bprim n.
Hypothesis CAF_RS : if prim then as_residue a1 = as_residue a else as_residue a1 = as_residue a ++ residue_pages (ab - kPageSize) (map_size n).

(* [comment removed for export] *)
Definition NDI (K : Z) (s : astate) : Prop := as_ndepot_ins s = K.
Lemma call_mmap_ordie_ndi : forall K l fl, presW (NDI K) (call_mmap_ordie E0 l fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_ndi : forall K cnt, presW (NDI K) (store_alloc E0 cnt).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try apply call_mmap_ordie_ndi; unfold NDI in *; cbn; assumption. Qed.
Lemma depot_put_nd1 : forall s0, hoareW (fun s => s = s0) (depot_put E0 key) (fun s' _ => NDI (as_ndepot_ins s0 + 1) s').
Proof.
  intros s0. unfold depot_put. apply hoareW_get_bind. intros s ->. apply hoareW_upd_bind.
  eapply hoareW_conseq with (P := NDI (as_ndepot_ins s0 + 1)) (Q := fun s' _ => NDI (as_ndepot_ins s0 + 1) s');
    [| intros s1 (s & -> & ->); unfold NDI; destruct s0; reflexivity| intros ? ? H; exact H].
  change (hoareW ?P ?m (fun s' _ => ?P s')) with (presW P m).
  pw; try apply call_mmap_ordie_ndi; try apply store_alloc_ndi; unfold NDI in *; cbn; assumption.
Qed.
Lemma ND12 : nd_same a1 a2 /\ as_ndepot_ins a2 = as_ndepot_ins a1 + 1.
Proof.
  split; [exact (hoareW_arun _ _ _ a1 _ _ a2 id _ _ (depot_put_nd E0 a1 key) (nd_same_refl a1) RUND)|].
  exact (hoareW_arun _ _ _ a1 _ _ a2 id _ _ (depot_put_nd1 a1) eq_refl RUND).
Qed.

(* [comment removed for export] *)
Lemma REQ : req n = n. Proof. unfold req. clear -Hn. lia. Qed.
Lemma BPRIM : bprim n = (if prim then 1 else 0). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma SIDE2 : if prim then as_cache_inited a2 = true /\ avail E0 [] a2 c ab /\ (exists x, ab = chunk_of_compact SB c x /\ (16 * x) mod class_size c = 0)
              else exists r0, ab = r0 + kPageSize /\ as_sec a2 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E0 a r0 (map_size n).
Proof.
  pose proof (proj1 ND12) as ND. pose proof ND as (_ & Hci & _ & _ & _ & _ & _ & Hsec & _).
  generalize SIDE. destruct prim; intros S.
  - destruct S as (CI & AV & X). split; [rewrite Hci; exact CI|]. split; [exact (avail_nd E0 [] a1 a2 _ _ ND AV)| exact X].
  - destruct S as (r0 & E1 & E2 & E3). exists r0. split; [exact E1|]. split; [rewrite Hsec; exact E2| exact E3].
Qed.

Lemma BS2 : blocks_sep E0 a2. Proof. exact (blocks_sep_of E0 a2 mo3 ENV0 WF2 AK2). Qed.
Lemma IMG_IN2 : forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> fst (ae_img E0) <= fst r /\ fst r + snd r <= fst (ae_img E0) + snd (ae_img E0).
Proof.
  pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _). destruct EIMG as [EI1 EI2].
  intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia.
Qed.
Lemma RENV2 : renv_ok E0 a2.
Proof.
  pose proof ENV0 as ENV. destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  destruct PL0OK as (_ & _ & (TR1 & TR2 & _) & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  destruct EIMG as [EI1 EI2].
  split; [exact BS2|]. split; [clear -Tlo Thi Timg; repeat split; lia|]. split; [exact IMG_IN2|]. split; [rewrite EI1; clear; lia|]. split; [exact IMGR|].
  split; [| split; [exists mo3; exact AK2| split; [exact TDN| exact DNP]]].
  intros x y Hx Hy. unfold arep_img_ranges, ae_instance in Hx. unfold depot_static in Hy. rewrite IC0 in Hx, Hy.
  cbn -[Z.add Z.le In] in Hx, Hy.
  destruct Hy as [<-|[<-|[]]]; cbn [fst snd]; repeat (destruct Hx as [<-|Hx]; [cbn [fst snd]; lia|]); destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma NFP2 : forall x, ab <= x < ab + tspan n -> ~ arep_fp E0 (DepotFP E0) a2 x.
Proof.
  pose proof CAF_DK as (_ & _ & _ & _ & _ & _ & CH1 & _). pose proof (proj1 ND12) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CH2 & _).
  exact (newblk_fp_free E0 a a2 n ab WF0 WF2 ltac:(rewrite CH2; exact CH1) BS2 IMG_IN2 Hn SIDE2).
Qed.
Lemma BLK2 : if tprim n then carved E0 a2 (tc n) ab else exists sc, In sc (as_sec a2) /\ sc_map_beg sc + kPageSize = ab /\ sc_map_size sc = map_size n.
Proof.
  unfold tprim, tc. generalize SIDE2. destruct prim; intros S.
  - destruct S as (_ & (CV & _) & _). exact CV.
  - destruct S as (r0 & E1 & E2 & _). exists (mkSec r0 (map_size n) (needed n)). split; [rewrite E2; apply in_app_iff; right; left; reflexivity|].
    cbn. split; [symmetry; exact E1| reflexivity].
Qed.
Lemma RZF : 16 <= trz n /\ trz n + rounded n <= needed n /\ needed n <= tspan n /\ n <= rounded n.
Proof.
  pose proof (rz_size_pos n) as R. pose proof (rounded_ge n) as (G1 & G2 & G3). unfold trz, tspan, tprim, tc, needed, needed1.
  destruct (from_primary n) eqn:PR.
  - assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
    pose proof (malloc_class_ok n N64) as [_ ND]. unfold malloc_class, needed1 in ND |- *. clear -R G1 ND Hn. repeat split; lia.
  - unfold round_up, kPageSize. clear -R G1 Hn. repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.
Lemma FRESH2 : as_chunks a2 !! cb = None.
Proof.
  destruct (as_chunks a2 !! cb) as [cm'|] eqn:L; [exfalso| reflexivity].
  pose proof RZF as (R1 & R2 & R3 & R4).
  pose proof WF2 as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ L) as (KB & _).
  apply (NFP2 cb); [unfold tcb, tub, kChunkHeaderSize; clear -R1 R2 R3 R4 Hn; lia|].
  do 6 right; left. exists cb, cm'. split; [exact L|]. left. rewrite <- KB. unfold kChunkHeaderSize in *. clear. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation K := kShadowBase.
(* [comment removed for export] *)
Lemma newblk_geo :
     ab mod 8 = 0 /\ tspan n mod 8 = 0 /\ 0 < tspan n /\ ab + tspan n <= alloc_ceiling
  /\ ((kHighMemBeg <= ab /\ SB + kRegionSize <= ab /\ ab + tspan n <= SB + kSpaceSize /\ ae_resv_beg E0 <= ab /\ ab + tspan n <= ae_resv_beg E0 + kResvLen)
      \/ (exists sc, In sc (as_sec a2) /\ sc_map_beg sc + kPageSize = ab /\ ab + tspan n = sc_map_beg sc + sc_map_size sc
           /\ 0x603000 <= sc_map_beg sc /\ (ab + tspan n <= kLowAppEnd \/ kHighMemBeg <= ab)))
  /\ (forall z, ab <= z < ab + tspan n -> sh_excluded E0 z = false).
Proof.
  pose proof (proj1 WF2) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  pose proof WF2 as (_ & WR & _ & _ & _ & (_ & _ & S3 & _) & _). destruct EIMG as [EI1 EI2]. pose proof alloc_ceiling_range as CR.
  assert (EXCL : forall z, (ae_resv_beg E0 <= z < ae_resv_beg E0 + kResvLen /\ ~ (SB + kSpaceSize <= z < SB + kSpaceSize + kPageSize))
                           \/ (exists sc, In sc (as_sec a2) /\ sc_map_beg sc <= z < sc_map_beg sc + sc_map_size sc) -> sh_excluded E0 z = false).
  { intros z Hz. unfold sh_excluded.
    assert (NF : ~ (ae_fs_beg E0 <= z < ae_fs_beg E0 + ae_fs_len E0) /\ ~ (ae_iarena E0 <= z < ae_iarena E0 + kIArenaLen) /\ ~ (SB + kSpaceSize <= z < SB + kSpaceSize + kPageSize)).
    { destruct Hz as [[R NRI]|(sc & Hsc & R)].
      - unfold kResvLen in R. split; [clear -R E12; lia|]. split; [clear -R E27; lia| exact NRI].
      - destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SP & SR).
        pose proof (SR _ E9) as X9. pose proof (SR _ E24) as X24. pose proof (SR _ E7) as X7. cbn [fst snd] in X9, X24, X7. unfold kSpaceSize, kPageSize in *.
        split; [clear -R X9; lia|]. split; [clear -R X24; lia| clear -R X7 E3 E4; lia]. }
    destruct NF as (N1 & N2 & N3).
    replace (in_fakestack E0 z) with false by (symmetry; unfold in_fakestack; apply Bool.andb_false_iff; destruct (Z_lt_le_dec z (ae_fs_beg E0)); [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -N1 l; lia).
    replace (in_iarena E0 z) with false by (symmetry; unfold in_iarena; apply Bool.andb_false_iff; destruct (Z_lt_le_dec z (ae_iarena E0)); [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -N2 l; lia).
    replace (in_reginfo E0 z) with false by (symmetry; unfold in_reginfo; apply Bool.andb_false_iff; destruct (Z_lt_le_dec z (SB + kSpaceSize)); [left; apply Z.leb_gt| right; apply Z.ltb_ge]; clear -N3 l; lia).
    reflexivity. }
  pose proof RZF as (R1 & R2 & R3 & R4).
  generalize SIDE2 BLK2. unfold tspan, tprim, tc. destruct prim eqn:PR; intros S2 B2.
  - (* [comment removed for export] *)
    destruct S2 as (_ & _ & (x & Hab & _)).
    assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
    pose proof (malloc_class_ok n N64) as [HCc _]. pose proof (class_size_mod c HCc) as [CSM CSZ].
    pose proof (carved_in_space E0 a2 c ab HCc WR B2) as [SP1 SP2].
    assert (AB8 : ab mod 8 = 0) by (rewrite Hab; unfold chunk_of_compact, region_beg, kRegionSize; clear -E1; Z.div_mod_to_equations; lia).
    rewrite kHighMemBeg_val in E2 |- *. unfold kResvLen, kSpaceSize, kRegionSize, kPageSize in *.
    split; [exact AB8|]. split; [clear -CSM; Z.div_mod_to_equations; lia|]. split; [clear -CSZ; lia|]. split; [clear -SP2 E4 E5; lia|]. split.
    + left. clear -SP1 SP2 E2 E3 E4. repeat split; lia.
    + intros z Hz. apply EXCL. left. clear -Hz SP1 SP2 E3 E4. lia.
  - (* [comment removed for export] *)
    destruct S2 as (r0 & Hab & Hsec & FR). destruct FR as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof (map_size_facts n) as (MS1 & MS2 & MS3).
    set (sc := mkSec r0 (map_size n) (needed n)).
    assert (Hsc : In sc (as_sec a2)) by (rewrite Hsec; apply in_app_iff; right; left; reflexivity).
    assert (SPAN : ab + round_up (needed n) kPageSize = r0 + map_size n) by (rewrite Hab; unfold map_size; clear; lia).
    pose proof (F6 _ E29) as X29. rewrite EI1 in X29. cbn [fst snd] in X29.
    assert (NS : ~ n <= 64512) by (intros LE; pose proof (proj2 (from_primary_iff n ltac:(clear -Hn; lia)) LE); congruence).
    assert (LOW : 0x603000 <= r0).
    { unfold app_mem in F2. rewrite kHighMemBeg_val in F2. unfold kPageSize in *. clear -F2 X29 EI2 MS2 NS R1 R2 R4. lia. }
    unfold kPageSize in *. rewrite kHighMemBeg_val in *.
    split; [rewrite Hab; clear -F1; Z.div_mod_to_equations; lia|]. split; [unfold round_up; clear; Z.div_mod_to_equations; lia|].
    split; [clear -MS3 SPAN Hab; lia|]. split; [clear -F3 SPAN; lia|]. split.
    + right. exists sc. split; [exact Hsc|]. unfold sc. cbn [sc_map_beg sc_map_size]. split; [symmetry; exact Hab|]. split; [exact SPAN|]. split; [exact LOW|].
      unfold app_mem in F2. rewrite ?kHighMemBeg_val in F2. clear -F2 SPAN Hab. lia.
    + intros z Hz. apply EXCL. right. exists sc. split; [exact Hsc|]. unfold sc. cbn [sc_map_beg sc_map_size]. clear -Hz SPAN Hab. lia.
Qed.

(* [comment removed for export] *)
Lemma newblk_aw : forall lo usp x y, ab <= x -> y <= ab + tspan n -> aw_ok E0 a a' lo usp (x, y).
Proof.
  intros lo usp x y Hx Hy. pose proof newblk_geo as (_ & _ & _ & _ & LOC & _). unfold aw_ok. cbn [fst snd].
  destruct LOC as [(_ & _ & _ & R1 & R2)|(sc & Hsc & L1 & L2 & _)].
  - do 3 right; left. clear -Hx Hy R1 R2. lia.
  - do 5 right; left. exists sc. split; [right; rewrite tl_sec; exact Hsc|]. unfold kPageSize in L1. clear -Hx Hy L1 L2. lia.
Qed.
(* [comment removed for export] *)
Lemma newblk_sh_aw : forall lo usp x y, K + ab / 8 <= x -> y <= K + (ab + tspan n + 7) / 8 -> aw_ok E0 a a' lo usp (x, y).
Proof.
  intros lo usp x y Hx Hy. pose proof newblk_geo as (AB8 & SP8 & POS & CE & LOC & EX). pose proof alloc_ceiling_range as CR.
  unfold aw_ok. cbn [fst snd]. do 8 right. split.
  - unfold LSHI, A_base.A_SB. unfold kShadowBase in Hx, Hy. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in LOC |- *.
    destruct LOC as [(HI & _)|(sc & _ & L1 & L2 & LOW & [LO'|HI])].
    + right. clear -Hx Hy HI CE CR AB8 SP8. Z.div_mod_to_equations. lia.
    + left. unfold kPageSize in L1. clear -Hx Hy LO' LOW L1 AB8 SP8. Z.div_mod_to_equations. lia.
    + right. clear -Hx Hy HI CE CR AB8 SP8. Z.div_mod_to_equations. lia.
  - intros z Hz. apply EX. unfold A_base.A_SB. unfold kShadowBase in Hx, Hy. clear -Hx Hy Hz AB8 SP8. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma newblk_vs_live : forall blo bsz, In (blo, bsz) (live_blocks a) -> blo + bsz <= ab \/ ab + tspan n <= blo.
Proof.
  intros blo bsz LIVE. pose proof CAF_DK as (_ & _ & _ & _ & _ & _ & CH1 & _). pose proof (proj1 ND12) as (_ & _ & _ & _ & _ & _ & _ & Hsec & _ & _ & _ & _ & _ & CH2 & _).
  assert (LIVE2 : In (blo, bsz) (live_blocks a2)) by (unfold live_blocks, chunk_list in *; rewrite CH2, CH1; exact LIVE).
  destruct (AF_tkit.live_block_loc E0 [] [] a2 blo bsz WF2 LIVE2) as (k & cm & Hk & _ & _ & POS & L1 & L2 & LOC).
  pose proof WF2 as (WE & WR & _ & _ & _ & (_ & _ & S3 & _) & _). pose proof WE as (E1 & E2 & E3 & E4 & _).
  pose proof RZF as (R1 & R2 & R3 & R4). pose proof NFP2 as NFP. unfold tspan, tprim in NFP.
  generalize SIDE2 BLK2. unfold tspan, tprim, tc. destruct prim eqn:PR; intros S2 B2.
  - assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
    pose proof (malloc_class_ok n N64) as [HCc _]. pose proof (carved_in_space E0 a2 c ab HCc WR B2) as [SP1 SP2].
    destruct (cm_prim cm) as [c'|] eqn:PC.
    + destruct LOC as (Hc' & G1 & G2). destruct S2 as (_ & (_ & _ & _ & NCB & _) & _).
      destruct (block_where E0 [] [] a2 k cm WF2 Hk) as [(J1 & J2 & c'' & Hc'' & PC'' & CV'' & _ & _ & SPAN)|(sc & Hsc & PCn & _)]; [| rewrite PC in PCn; discriminate].
      destruct (carved_blocks_disjoint E0 a2 c ab c'' (blk_lo cm) HCc Hc'' WR B2 CV'') as [[_ EQ]|D].
      * exfalso. apply NCB. exists k, cm. split; [exact Hk| unfold blk_lo in EQ; symmetry; exact EQ].
      * clear -D L1 L2 SPAN. lia.
    + destruct LOC as (sc & Hsc & G1 & G2). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SSP & _). unfold kPageSize, kSpaceSize, kRegionSize in *.
      clear -L1 L2 G1 G2 SSP SP1 SP2. lia.
  - destruct S2 as (r0 & Hab & Hsec2 & FR). destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). pose proof (map_size_facts n) as (MS1 & MS2 & MS3).
    assert (SPAN : ab + round_up (needed n) kPageSize = r0 + map_size n) by (rewrite Hab; unfold map_size; clear; lia).
    destruct (cm_prim cm) as [c'|] eqn:PC.
    + destruct LOC as (Hc' & G1 & G2). destruct (proj2 WR c' Hc') as (W1 & _ & W3 & _). cbv zeta in W1, W3. unfold region_of in W1, W3.
      unfold region_beg, kRegionSize, kFreeArrayOffset, kSpaceSize, kLargestClassID, kPageSize in *. clear -L1 L2 G1 G2 W1 W3 F4 SPAN Hab Hc'. nia.
    + destruct LOC as (sc & Hsc & G1 & G2). rewrite Hsec2 in Hsc. apply in_app_iff in Hsc. destruct Hsc as [Hsc|[<-|[]]].
      * destruct (F5 sc Hsc); unfold kPageSize in *; clear -L1 L2 G1 G2 SPAN Hab H; lia.
      * (* [comment removed for export] *)
        exfalso. cbn [sc_map_beg sc_map_size] in G1, G2.
        apply (NFP (cm_chunk_beg cm)); [| do 6 right; left; exists k, cm; split; [exact Hk| left; clear; lia]].
        pose proof (chunk_meta_in_block E0 [] [] a2 k cm (cm_chunk_beg cm) WF2 Hk ltac:(left; clear; lia)) as [BL BU].
        unfold kPageSize in *. clear -BL BU G1 G2 SPAN Hab. lia.
Qed.
(* [comment removed for export] *)
Lemma newblk_sh_vs_live : forall blo bsz, In (blo, bsz) (live_blocks a) -> blo + bsz <= K + ab / 8 \/ K + (ab + tspan n + 7) / 8 <= blo.
Proof.
  intros blo bsz LIVE. pose proof newblk_geo as (AB8 & SP8 & POS & CE & LOCn & _). pose proof alloc_ceiling_range as CR.
  assert (AB0 : 0 <= ab) by (destruct LOCn as [(H1 & _)|(sc0 & _ & M1 & _ & M2 & _)]; [rewrite kHighMemBeg_val in H1; clear -H1; lia| unfold kPageSize in M1; clear -M1 M2; lia]).
  clear LOCn.
  destruct (AF_tkit.live_block_loc E0 [] [] a blo bsz WF0 LIVE) as (k & cm & Hk & _ & _ & BP & L1 & L2 & LOC).
  pose proof WF0 as (WE & WR & _ & _ & _ & (_ & _ & S3 & _) & _). pose proof WE as (E1 & E2 & E3 & E4 & _). rewrite kHighMemBeg_val in E2.
  unfold kShadowBase.
  assert (SHB : 2147450880 + (ab + tspan n + 7) / 8 <= 17594333495296) by (clear -CE CR; Z.div_mod_to_equations; lia).
  destruct (cm_prim cm) as [c'|].
  - destruct LOC as (Hc' & G1 & G2).
    right. unfold region_beg, kRegionSize, kLargestClassID in *. clear -L1 G1 E2 E3 Hc' SHB. lia.
  - destruct LOC as (sc & Hsc & G1 & G2). destruct (S3 sc Hsc) as (_ & AM & CEs & _). unfold app_mem, kPageSize in *. rewrite kLowAppEnd_val, kHighMemBeg_val in AM.
    destruct AM as [[_ LO']|[HI _]]; [left; clear -L1 L2 G1 G2 LO' AB0; Z.div_mod_to_equations; lia| right; clear -L1 G1 HI SHB; lia].
Qed.

(* [comment removed for export] *)
Lemma RUNC : exists fuel orc evs orc', arun fuel (amalloc_core E0 key n a) orc = Some (a', ONorm (Some ub), evs, orc').
Proof. exact (arun_amalloc_core E0 a a1 a2 n ab id key fA orcA evsA orcA' fD orcD evsD orcD' Hn RUNA RUND FRESH2). Qed.

(* [comment removed for export] *)
Lemma malloc_pre0 : malloc_pre a n /\ depot_ok E0 a key.
Proof.
  pose proof CAF_DK as (_ & KY & _). destruct ABUD as (B1 & B2 & B3). destruct KEY as [[K1 K2] K3].
  split.
  - unfold malloc_pre. destruct (from_primary n) eqn:PR.
    + assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
      pose proof (malloc_class_ok n N64) as [HC _]. unfold malloc_class in HC.
      apply (room_of_binv a _ BI0 HC). assert (ACH : acharge n = kCmPrim) by (unfold acharge; rewrite PR; reflexivity). unfold kCmPrim in ACH. unfold kInitialCredit in B3. clear -B1 B2 B3 ACH. lia.
    + pose proof (n_chunks_bound E0 a WF0 QB0 BI0) as X. unfold nbig_live in NBIG. unfold zlen in X. unfold kChunksBlockCount. clear -X NBIG. lia.
  - split; [exact K1|]. unfold depot_n_ids in *. rewrite <- KY. exact K2.
Qed.

Theorem INV' : AWf E0 [] [] a' /\ res_ok a' /\ AQbound a' /\ depot_inv E0 a' /\ binv a' /\ sstats_ok a' /\ csmall a'.
Proof.
  destruct RUNC as (fuel & orc & evs & orc' & RUN). destruct malloc_pre0 as [MP DOK].
  split.
  { destruct (from_primary n) eqn:PR.
    - exact (proj1 (hoare_arun _ _ _ a _ _ a' _ _ _ (amalloc_core_prim_spec E0 [] [] a key n DOK ltac:(clear -Hn; lia) PR WF0 MP) eq_refl RUN)).
    - exact (proj1 (hoare_arun _ _ _ a _ _ a' _ _ _ (amalloc_core_sec_spec E0 [] [] a key n DOK ltac:(clear -Hn; lia) PR WF0 MP) eq_refl RUN)). }
  split; [exact (hoareW_arun _ _ _ a _ _ a' _ _ _ (amalloc_core_res E0 key n) RES0 RUN)|].
  split.
  { pose proof (hoareW_arun _ _ _ a _ _ a' _ _ _ (amalloc_core_qs E0 (as_tq a) (as_gq a) key n) (conj eq_refl eq_refl) RUN) as [Q1 Q2].
    destruct QB0 as [X Y]. unfold AQbound, tq_bytes, gq_bytes in *. rewrite Q1, Q2. split; [exact X| exact Y]. }
  split; [exact (hoareW_arun _ _ _ a _ _ a' _ _ _ (amalloc_core_di E0 a key n (proj2 KEY) DI0) eq_refl RUN)|].
  split; [exact (proj1 (hoareW_arun _ _ _ a _ _ a' _ _ _ (amalloc_core_cnt E0 a key n ltac:(clear -Hn; lia) BI0 (nbatch_bound a BI0 QB0)) eq_refl RUN))|].
  pose proof (proj1 ND12) as ND. pose proof ND as (_ & _ & _ & _ & _ & _ & _ & Hsec & _ & Hsst & _ & _ & _ & Hch & _).
  split.
  { destruct SS1 as [S1 S2]. unfold sstats_ok, sec_bytes in *. rewrite tl_sec_stats, tl_sec, Hsst, Hsec. split; [exact S1| exact S2]. }
  pose proof CAF_DK as (_ & _ & _ & _ & _ & _ & CH1 & _).
  intros k cm Hk. rewrite tl_chunks in Hk. destruct (decide (k = cb)) as [->|NE].
  - rewrite lookup_insert_eq in Hk. injection Hk as <-. unfold tcm. cbn [cm_n]. rewrite REQ. clear -Hn. lia.
  - rewrite lookup_insert_ne in Hk by congruence. rewrite Hch, CH1 in Hk. exact (CS0 k cm Hk).
Qed.

(* [comment removed for export] *)
Theorem ACCT : aacct a a' n.
Proof.
  pose proof ND12 as [ND NDp]. pose proof ND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hres & Hnp & _).
  pose proof CAF_DK as (DK1 & _). unfold aacct.
  assert (E1 : as_nprim_ever a' = as_nprim_ever a + bprim n) by (rewrite <- CAF_NP, <- Hnp; unfold tail_st; destruct a2; reflexivity).
  assert (E2 : as_ndepot_ins a' = as_ndepot_ins a + 1) by (rewrite <- DK1, <- NDp; unfold tail_st; destruct a2; reflexivity).
  assert (E3 : as_residue a' = as_residue a1) by (rewrite <- Hres; unfold tail_st; destruct a2; reflexivity).
  rewrite E1, E2, E3. unfold bprim, acharge, arefund. generalize CAF_RS. destruct prim; intros RS.
  - rewrite RS. unfold kCmPrim. clear. pose proof (zlen_nonneg (as_residue a)). lia.
  - rewrite RS.
    pose proof (map_size_facts n) as (_ & _ & MS2).
    pose proof (residue_pages_len (ab - kPageSize) (map_size n) ltac:(unfold kPageSize in MS2; clear -MS2; lia)) as L.
    unfold zlen in *. rewrite length_app, Nat2Z.inj_add. destruct (map_size n <? kBigMapSize); clear -L; lia.
Qed.

(* [comment removed for export] *)
Lemma filter_perm : forall {X} (f : X -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros X f l l' P. induction P as [|x l1 l2 P IH|x y l1|l1 l2 l3 P1 IH1 P2 IH2]; cbn.
  - apply Permutation_refl.
  - destruct (f x); [apply perm_skip; exact IH| exact IH].
  - destruct (f y); destruct (f x); try apply perm_swap; try apply Permutation_refl; apply perm_skip; apply Permutation_refl.
  - etransitivity; [exact IH1| exact IH2].
Qed.
Theorem LIVE' : Permutation (live_blocks a') ((ub, n) :: live_blocks a).
Proof.
  pose proof (proj1 ND12) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hch & _). pose proof CAF_DK as (_ & _ & _ & _ & _ & _ & CH1 & _).
  pose proof (cm_geo a2 n ab id ltac:(clear -Hn; lia)) as (_ & G2 & _ & G4 & G5 & _).
  unfold live_blocks, chunk_list. rewrite (tl_chunks a2 n ab id), <- CH1, <- Hch.
  etransitivity.
  { apply Permutation_map. apply filter_perm. apply map_to_list_insert. exact FRESH2. }
  cbn [List.filter map snd]. rewrite G5. cbn [List.filter map snd]. rewrite G2, G4, REQ. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Lemma mod16_of_div : forall x, (16 | x) -> x mod 16 = 0.
Proof. intros x H. apply Z.mod_divide; [lia| exact H]. Qed.
Lemma div16_pow2 : forall k r, 0 <= r -> (16 | 16 * k * 2 ^ r). 
Proof. intros k r Hr. exists (k * 2 ^ r). lia. Qed.
Lemma div_of_mod : forall m x, 0 < m -> x mod m = 0 -> (m | x).
Proof. intros m x Hm H. apply Z.mod_divide; [lia| exact H]. Qed.

Theorem ABLK : ablock_range ACONSTS ub n.
Proof.
  pose proof alloc_ceiling_range as CR. pose proof RZF as (R1 & R2 & R3 & R4). destruct EIMG as [EI1 EI2].
  pose proof WF2 as (WE & WR & _ & _ & _ & WS & _). pose proof WS as (_ & _ & WS3 & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  unfold ablock_range, tub. cbn [c_img_hi ACONSTS]. rewrite kHighMemBeg_val in E2.
  generalize BLK2. unfold tspan in R3. unfold tprim, tc in *. destruct (from_primary n) eqn:PR; intros B; rewrite ?PR in R3.
  - assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
    pose proof (malloc_class_ok n N64) as [HC _].
    pose proof (carved_in_space E0 a2 (malloc_class n) ab HC WR B) as [SP1 SP2].
    pose proof B as (k & Hk & Hab & Hk1). unfold region_beg in Hab. pose proof (class_size_mod (malloc_class n) HC) as [CM _].
    pose proof (rz_log_range n) as RL. unfold trz, rz_size in *. unfold kSpaceSize, kRegionSize in *.
    split; [clear -SP1 E2 E3 R1; lia|].
    split.
    { apply mod16_of_div. rewrite Hab. apply Z.divide_add_r; [| exists (2 ^ rz_log n); clear; lia].
      apply Z.divide_add_r; [apply Z.divide_add_r|].
      - eapply Z.divide_trans; [| apply (div_of_mod (2^16) SB); [clear; lia| exact E1]]. exists 4096. reflexivity.
      - apply Z.divide_mul_r. exists (2^28). reflexivity.
      - apply Z.divide_mul_r. eapply Z.divide_trans; [| apply (div_of_mod 32); [clear; lia| exact CM]]. exists 2. reflexivity. }
    split; [clear -Hn; lia|]. split; [clear -SP2 E4 E5 R2 R3 R4; lia| clear -SP1 E2 E3 R1; lia].
  - destruct B as (sc & Hsc & Eab & Esz). destruct (WS3 sc Hsc) as (MOD & AM & CE & POS & MODS & SSP & RSV).
    pose proof (RSV _ E29) as XI. rewrite EI1 in XI.
    destruct (ak_sec _ _ _ AK2 sc Hsc) as [_ (INS & _)]. destruct INS as (e & _ & LOe & _). unfold elo in LOe. pose proof (bv_unsigned_in_range _ (fst e)) as BR.
    pose proof (map_size_facts n) as (_ & MG & _). pose proof (rz_log_range n) as RL. unfold trz, rz_size, kPageSize in *.
    assert (NEED : 65536 < needed n) by (unfold needed, from_primary in *; rewrite PR in *; apply Z.leb_gt in PR; unfold kMaxSize in PR; pose proof (rz_size_pos n); clear -PR H; lia).
    split; [rewrite <- Eab; clear -LOe BR; lia|].
    split.
    { apply mod16_of_div. rewrite <- Eab. apply Z.divide_add_r; [| exists (2 ^ rz_log n); clear; lia].
      apply Z.divide_add_r; [| exists 256; reflexivity]. eapply Z.divide_trans; [| apply (div_of_mod 4096); [clear; lia| exact MOD]]. exists 256. reflexivity. }
    split; [clear -Hn; lia|]. split; [rewrite <- Eab; rewrite Esz in CE; clear -CE R2 R3 R4 MG; lia| ].
    rewrite <- Eab. rewrite Esz in XI. clear -XI LOe BR EI2 NEED MG. lia.
Qed.

(* [comment removed for export] *)
Theorem atail_facts :
     (exists fuel orc evs orc', arun fuel (amalloc_core E0 key n a) orc = Some (a', ONorm (Some ub), evs, orc'))
  /\ (AWf E0 [] [] a' /\ res_ok a' /\ AQbound a' /\ depot_inv E0 a' /\ binv a' /\ sstats_ok a' /\ csmall a')
  /\ aacct a a' n
  /\ Permutation (live_blocks a') ((ub, n) :: live_blocks a)
  /\ ablock_range ACONSTS ub n
  /\ as_chunks a2 !! cb = None /\ AsanRepEnq.renv_ok E0 a2
  /\ (if tprim n then carved E0 a2 (tc n) ab else exists sc, In sc (as_sec a2) /\ sc_map_beg sc + kPageSize = ab /\ sc_map_size sc = map_size n)
  /\ (forall x, ab <= x < ab + tspan n -> ~ arep_fp E0 (DepotFP E0) a2 x)
  /\ nd_same a1 a2.
Proof.
  split; [exact RUNC|]. split; [exact INV'|]. split; [exact ACCT|]. split; [exact LIVE'|]. split; [exact ABLK|].
  split; [exact FRESH2|]. split; [exact RENV2|]. split; [exact BLK2|]. split; [exact NFP2| exact (proj1 ND12)].
Qed.

(* [comment removed for export] *)
Theorem atail_wfacts :
     (forall lo usp x y, ab <= x -> y <= ab + tspan n -> aw_ok E0 a a' lo usp (x, y))
  /\ (forall lo usp x y, kShadowBase + ab / 8 <= x -> y <= kShadowBase + (ab + tspan n + 7) / 8 -> aw_ok E0 a a' lo usp (x, y))
  /\ (forall blo bsz, In (blo, bsz) (live_blocks a) -> blo + bsz <= ab \/ ab + tspan n <= blo)
  /\ (forall blo bsz, In (blo, bsz) (live_blocks a) -> blo + bsz <= kShadowBase + ab / 8 \/ kShadowBase + (ab + tspan n + 7) / 8 <= blo).
Proof.
  pose proof atail_facts as AF. clear AF.
  split; [exact newblk_aw|]. split; [exact newblk_sh_aw|]. split; [exact newblk_vs_live| exact newblk_sh_vs_live].
Qed.
End AT.
End RC__1.
