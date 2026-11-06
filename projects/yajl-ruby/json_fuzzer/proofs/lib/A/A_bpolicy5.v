(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanRepFrame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_base A_policy5 AF_place AF_fakestack_rep A_bundle A_benv5 A_balloc5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Lemma eager_rw_lazy_disjoint : forall mo x n, eager_rw mo x n -> lazy_disjoint mo x (x + n).
Proof.
  intros mo x n (_ & _ & C) l sz Hin. pose proof (C (l, sz) Hin) as X. unfold elo, ehi in X. cbn [fst snd] in X. lia.
Qed.

Lemma page_size_val : page_size = 4096.
Proof. reflexivity. Qed.

Lemma acc_ok_of_lazy_disjoint : forall mo S lo hi (a : Z) (k : nat),
  lazy_disjoint mo lo hi -> 0 <= lo -> hi <= 2^64 -> lo <= a -> a + Z.of_nat k <= hi -> acc_ok (m_vm_lazy mo) S (Z_to_bv 64 a, k).
Proof.
  intros mo S lo hi a k HD Hlo Hhi Ha Hk.
  destruct k as [|k'].
  - right. split; [unfold acc_nowrap; cbn [fst snd]; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)); unfold bv_modulus in *; lia| intros kk Hkk; cbn in Hkk; lia].
  - left. eapply lazy_disjoint_acc_out; [exact HD| lia| lia| lia| exact Hk| lia].
Qed.

(* [comment removed for export] *)
Lemma page_base_of_shadow : forall a', 0 <= a' < 2^47 ->
  page_base_of (A_SB + a' / 8) = Z_to_bv 64 (shadow_page a') /\ 0 <= shadow_page a' < 2^45 /\ shadow_page a' mod 4096 = 0.
Proof.
  intros a' Ha. unfold page_base_of, shadow_page, round_down, mem_to_shadow. rewrite page_size_val, A_SB_val.
  change kShadowBase with 2147450880. change kPageSize with 4096.
  split; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac wfe_open WE :=
  destruct WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                  WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).

Section Pol.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).

#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation A0c := (A_bundle.A0 E0 FSB0 HR0).

Definition POL (s : aps) (mo : Model) (a : Z) (k : nat) : Prop := acc_ok (m_vm_lazy mo) (aSc s) (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma pol_of_pages_budgeted : forall s mo lo hi a k,
  pages_budgeted (aSc s) lo hi -> 0 <= lo -> hi < 2^64 -> lo <= a -> a + Z.of_nat k <= hi -> POL s mo a k.
Proof.
  intros s mo lo hi a k PB H0 H1 H2 H3. unfold POL. right.
  eapply pages_budgeted_acc_inS; [exact PB| lia| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma aS_intro_A0 : forall s lo hi z,
  In (lo, hi) A0c -> lo mod 4096 = 0 -> 0 <= lo -> hi <= 2^64 -> lo <= z < hi -> aSc s (page_base_of z).
Proof.
  intros s lo hi z Hin AL Hlo Hhi Hz. unfold A_bundle.aS, A_policy5.aS, A_policy5.aSa, page_base_of. rewrite page_size_val.
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). split; [Z.div_mod_to_equations; lia|].
  left. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. Z.div_mod_to_equations; lia.
Qed.
Lemma pages_budgeted_A0 : forall s lo hi a b,
  In (lo, hi) A0c -> lo mod 4096 = 0 -> 0 <= lo -> hi <= 2^64 -> lo <= a -> b <= hi -> pages_budgeted (aSc s) a b.
Proof. intros s lo hi a b Hin Hal Hlo Hhi Ha Hb z Hz. eapply aS_intro_A0; eauto. lia. Qed.
Lemma pol_A0 : forall s mo lo hi a k,
  In (lo, hi) A0c -> lo mod 4096 = 0 -> 0 <= lo -> hi < 2^64 -> lo <= a -> a + Z.of_nat k <= hi -> POL s mo a k.
Proof.
  intros s mo lo hi a k Hin AL H0 H1 H2 H3.
  apply (pol_of_pages_budgeted s mo lo hi); [| lia| lia| lia| lia]. eapply pages_budgeted_A0; eauto; lia.
Qed.
(* [comment removed for export] *)
Lemma pol_S0 : forall s mo lo hi a k,
  In (lo, hi) (S0_ivs5 E0 FSB0) -> lo mod 4096 = 0 -> 0 <= lo -> hi < 2^64 -> lo <= a -> a + Z.of_nat k <= hi -> POL s mo a k.
Proof. intros s mo lo hi a k Hin. apply pol_A0. unfold A_bundle.A0. apply in_app_iff. left. exact Hin. Qed.

(* [comment removed for export] *)
Lemma pol_low_shadow : forall s mo a k, 0x7fff7000 <= a -> a + Z.of_nat k <= 0x8fff7000 -> POL s mo a k.
Proof.
  intros s mo a k H1 H2. apply (pol_S0 s mo 0x7fff7000 0x8fff7000); [| reflexivity| lia| lia| lia| lia].
  unfold S0_ivs5. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pol_stack_shadow : forall s mo a k, A_SB + alloc_ceiling / 8 <= a -> a + Z.of_nat k <= kHighMemBeg -> POL s mo a k.
Proof.
  intros s mo a k H1 H2. pose proof alloc_ceiling_range as CR. rewrite kHighMemBeg_val in *.
  pose proof (pgdn_le (sh alloc_ceiling)) as L. pose proof (pgdn_mod (sh alloc_ceiling)) as M.
  apply (pol_S0 s mo (pgdn (sh alloc_ceiling)) kHighMemBeg); rewrite ?kHighMemBeg_val;
    [| exact M| unfold pgdn, sh in *; rewrite A_SB_val in *; Z.div_mod_to_equations; lia| lia| unfold sh in *; lia| lia].
  unfold S0_ivs5. do 2 right. left. reflexivity.
Qed.

Section WithState.
Variables (s : aps) (mo : Model).
Hypothesis K : AKern E0 (aps_alloc s) mo.
Hypothesis WE : wf_env E0.
Hypothesis EV : ENVOK E0 FSB0 s.
Hypothesis ENV0 : env0_ok5 E0.

Let EE : aps_env s = E0.
Proof. destruct EV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _). exact EE. Qed.
Let EFS : aps_fsbase s = FSB0.
Proof. destruct EV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EFS & _). exact EFS. Qed.

Let bvu64 : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Lemma store_blocks_above_img : forall b, In b (as_store_blocks (aps_alloc s)) -> 0x603000 <= b.
Proof.
  intros b Hb. pose proof EV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  wfe_open WE.
  destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & _ & _ & _ & _ & B6).
  pose proof (B6 _ WE29) as X. rewrite EI1 in X. cbn [fst snd] in X. unfold app_mem, kStoreBlockBytes in *. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in B1. clear -B1 X EI2. lia.
Qed.
Lemma node_blocks_above_img : forall b, In b (as_node_blocks (aps_alloc s)) -> 0x603000 <= b.
Proof.
  intros b Hb. pose proof EV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  wfe_open WE.
  destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & _ & _ & _ & _ & B6).
  pose proof (B6 _ WE29) as X. rewrite EI1 in X. cbn [fst snd] in X. unfold app_mem, kDepotNodeBlockBytes in *. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in B1. clear -B1 X EI2. lia.
Qed.
Lemma ptr_above_img : 0x603000 <= ae_ptr_array E0.
Proof.
  pose proof EV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  wfe_open WE. unfold img_sep, app_mem in *. rewrite EI1 in WE33. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE16. clear -WE16 WE33 EI2. lia.
Qed.
Lemma store0_placed : 0x603000 <= ae_store_blk E0 /\ ae_store_blk E0 + 2^23 <= alloc_ceiling
  /\ (ae_store_blk E0 + 2^23 <= 0x7fff7000 \/ kHighMemBeg <= ae_store_blk E0).
Proof.
  pose proof ENV0 as (_ & _ & _ & N4 & _). unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kStoreBlockBytes in N4.
  rewrite kHighMemBeg_val. exact N4.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lazy_disjoint_gen' : forall lo hi,
  (hi <= 0x7fff7000 \/ kHighMemBeg <= lo) ->
  (hi <= ae_store_blk E0 \/ ae_store_blk E0 + 2^23 <= lo) ->
  (forall b, In b (as_store_blocks (aps_alloc s)) -> hi <= b \/ b + kStoreBlockBytes <= lo) ->
  (hi <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= lo) ->
  (hi <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= lo) ->
  lazy_disjoint mo lo hi.
Proof.
  clear ENV0.
  intros lo hi Hband HS0 HSB HP HR l sz Hin.
  pose proof (ak_lazy _ _ _ K (l, sz) Hin) as HL. unfold elo, ehi in HL. cbn [fst snd] in HL.
  pose proof (bvu64 l). pose proof (bvu64 sz).
  rewrite kHighMemBeg_val in *.
  destruct HL as [HL | [HL | [(b & Hb & HL1 & HL2) | [HL | (HL0 & HL1 & _)]]]].
  - lia.
  - lia.
  - destruct (HSB b Hb); lia.
  - destruct (as_ptr_committed (aps_alloc s) =? 0); change kPtrArrayCommit with 131072 in HL; lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_stack' : forall lo hi, alloc_ceiling <= lo -> lazy_disjoint mo lo hi.
Proof.
  intros lo hi Hlo. pose proof alloc_ceiling_range as CR. pose proof store0_placed as (S1 & S2 & S3).
  wfe_open WE.
  apply lazy_disjoint_gen'.
  - right. rewrite kHighMemBeg_val. clear -CR Hlo. lia.
  - right. clear -S2 Hlo. lia.
  - intros b Hb. destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & B2 & _). right. exact (Z.le_trans _ _ _ B2 Hlo).
  - right. change kPtrArrayLen with 0x800000. clear -WE17 Hlo. lia.
  - right. change kResvLen with 0x2000011000. clear -WE5 Hlo. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_img' : forall lo hi, hi <= 0x603000 -> lazy_disjoint mo lo hi.
Proof.
  intros lo hi Hhi. pose proof store0_placed as (S1 & S2 & S3). pose proof ptr_above_img as PA.
  pose proof WE as WE'. wfe_open WE'.
  apply lazy_disjoint_gen'.
  - left. clear -Hhi. lia.
  - left. clear -S1 Hhi. lia.
  - intros b Hb. left. pose proof (store_blocks_above_img b Hb). clear -H Hhi. lia.
  - left. clear -PA Hhi. lia.
  - left. rewrite kHighMemBeg_val in WE2. clear -WE2 Hhi. lia.
Qed.

Lemma pol_stack' : forall a k, alloc_ceiling <= a -> a + Z.of_nat k <= 2^64 -> POL s mo a k.
Proof.
  intros a k H1 H2. unfold POL. pose proof alloc_ceiling_range as CR.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) a (2^64)); [| clear -CR H1; lia| lia| lia| lia].
  apply lazy_disjoint_stack'. exact H1.
Qed.

Lemma pol_img' : forall a k, 0 <= a -> a + Z.of_nat k <= 0x603000 -> POL s mo a k.
Proof.
  intros a k H1 H2. unfold POL.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) 0 0x603000); [| lia| lia| lia| lia].
  apply lazy_disjoint_img'. lia.
Qed.

(* [comment removed for export] *)
Lemma pol_resv_range' : forall r0 rl a k, resv_range_ok E0 r0 rl -> r0 <= a -> a + Z.of_nat k <= r0 + rl -> POL s mo a k.
Proof.
  intros r0 rl a k (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) H1 H2. unfold POL. pose proof alloc_ceiling_range as CR.
  destruct R2 as (P1 & P2 & P3 & P4). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) r0 (r0 + rl)); [| clear -P1; lia| clear -P2 CR; lia| exact H1| exact H2].
  apply lazy_disjoint_gen'; [rewrite kHighMemBeg_val; exact P4| exact R6| | exact R7| exact R4].
  intros b Hb. destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B6).
  destruct (B6 _ R1) as [X|X]; cbn [fst snd] in X; [right| left]; exact X.
Qed.

(* [comment removed for export] *)
Lemma pol_thread' : forall a k, ae_thread E0 <= a -> a + Z.of_nat k <= ae_thread E0 + 4096 -> POL s mo a k.
Proof.
  intros a k H1 H2. unfold POL. pose proof alloc_ceiling_range as CR.
  pose proof (ak_thread _ _ _ K) as T. pose proof (eager_rw_lazy_disjoint _ _ _ T) as LD. change kPageSize with 4096 in LD.
  wfe_open WE. unfold app_mem in WE14. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE14.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) (ae_thread E0) (ae_thread E0 + 4096)); [exact LD| clear -WE14; lia| clear -WE15 CR; lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma pol_node_block' : forall b a k,
  In b (ae_depot_nodes E0 :: as_node_blocks (aps_alloc s)) -> b <= a -> a + Z.of_nat k <= b + kDepotNodeBlockBytes -> POL s mo a k.
Proof.
  intros b a k [<- | Hb] H1 H2; unfold POL; pose proof alloc_ceiling_range as CR.
  - pose proof (ak_depot_nodes _ _ _ K) as T. pose proof (eager_rw_lazy_disjoint _ _ _ T) as LD.
    pose proof ENV0 as (_ & _ & N3 & _). unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kDepotNodeBlockBytes in *.
    eapply (acc_ok_of_lazy_disjoint mo (aSc s) (ae_depot_nodes E0) (ae_depot_nodes E0 + 2^20)); [exact LD| clear -N3; lia| clear -N3 CR; lia| lia| lia].
  - pose proof (proj2 (ak_node_blocks _ _ _ K b Hb)) as T. pose proof (eager_rw_lazy_disjoint _ _ _ T) as LD.
    pose proof (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & B2 & _).
    unfold app_mem, kDepotNodeBlockBytes in *. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in B1.
    eapply (acc_ok_of_lazy_disjoint mo (aSc s) b (b + 2^20)); [exact LD| clear -B1; lia| clear -B2 CR; lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma pol_ptr_head' : forall a k,
  as_ptr_committed (aps_alloc s) = kChunksBlockCount ->
  ae_ptr_array E0 <= a -> a + Z.of_nat k <= ae_ptr_array E0 + kPtrArrayCommit -> POL s mo a k.
Proof.
  intros a k HP H1 H2. unfold POL. pose proof alloc_ceiling_range as CR.
  pose proof (ak_ptr_head _ _ _ K HP) as T. pose proof (eager_rw_lazy_disjoint _ _ _ T) as LD.
  wfe_open WE. unfold app_mem in WE16. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE16. change kPtrArrayCommit with 131072 in *.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) (ae_ptr_array E0) (ae_ptr_array E0 + 131072)); [exact LD| clear -WE16; lia| clear -WE17 CR; lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma pol_space_shadow' : forall a k,
  A_SB + ae_space_beg E0 / 8 <= a -> a + Z.of_nat k <= A_SB + (ae_space_beg E0 + 2^37) / 8 -> POL s mo a k.
Proof.
  intros a k H1 H2. pose proof alloc_ceiling_range as CR.
  wfe_open WE. rewrite kHighMemBeg_val in WE2. change kSpaceSize with (2^37) in WE4.
  rewrite A_SB_val in *.
  apply (pol_S0 s mo (pgdn (sh (ae_space_beg E0))) (pgup (sh (ae_space_beg E0 + 2^37)))).
  - unfold S0_ivs5. right. left. reflexivity.
  - apply pgdn_mod.
  - unfold pgdn, sh. rewrite A_SB_val. clear -WE2 WE3. Z.div_mod_to_equations. lia.
  - unfold pgup, pgdn, sh. rewrite A_SB_val. clear -WE2 WE3 WE4 WE5 CR. Z.div_mod_to_equations. lia.
  - pose proof (pgdn_le (sh (ae_space_beg E0))) as X. unfold sh in X |- *. rewrite A_SB_val in *. clear -X H1. lia.
  - pose proof (pgup_ge (sh (ae_space_beg E0 + 2^37))) as X. unfold sh in X |- *. rewrite A_SB_val in *. clear -X H2. lia.
Qed.

(* [comment removed for export] *)
Lemma pol_reginfo' : forall a k,
  ae_space_beg E0 + 2^37 <= a -> a + Z.of_nat k <= ae_space_beg E0 + 2^37 + 4096 -> POL s mo a k.
Proof.
  intros a k H1 H2. pose proof alloc_ceiling_range as CR.
  wfe_open WE. rewrite kHighMemBeg_val in WE2. change kSpaceSize with (2^37) in WE4.
  apply (pol_S0 s mo (ae_space_beg E0 + 2^37) (ae_space_beg E0 + 2^37 + 4096)).
  - unfold S0_ivs5. do 5 right. left. reflexivity.
  - clear -WE1. Z.div_mod_to_equations. nia.
  - clear -WE2 WE3; lia. - clear -WE2 WE3 WE4 WE5 CR; lia. - exact H1. - exact H2.
Qed.

(* [comment removed for export] *)
Lemma pol_fs_shadow' : forall a k,
  A_SB + FSB0 / 8 <= a -> a + Z.of_nat k <= A_SB + (FSB0 + kFsBytes) / 8 -> POL s mo a k.
Proof.
  intros a k H1 H2. pose proof alloc_ceiling_range as CR.
  pose proof EV as (_ & _ & V3 & V4 & _). rewrite EFS in V3, V4. unfold app_mem in V3. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in V3.
  rewrite A_SB_val in *. rewrite kFsBytes_val in *.
  apply (pol_S0 s mo (pgdn (sh FSB0)) (pgup (sh (FSB0 + kFsBytes)))); rewrite ?kFsBytes_val.
  - unfold S0_ivs5. do 3 right. left. reflexivity.
  - apply pgdn_mod.
  - unfold pgdn, sh. rewrite A_SB_val. clear -V3. Z.div_mod_to_equations. lia.
  - unfold pgup, pgdn, sh. rewrite A_SB_val. clear -V3 V4 CR. Z.div_mod_to_equations. lia.
  - pose proof (pgdn_le (sh FSB0)) as X. unfold sh in X |- *. rewrite A_SB_val in *. clear -X H1. lia.
  - pose proof (pgup_ge (sh (FSB0 + 11571200))) as X. unfold sh in X |- *. rewrite A_SB_val in *. clear -X H2. lia.
Qed.

(* [comment removed for export] *)
Lemma pol_store_block' : forall b a k,
  In b (ae_store_blk E0 :: as_store_blocks (aps_alloc s)) -> b <= a -> a + Z.of_nat k <= b + kStoreBlockBytes -> POL s mo a k.
Proof.
  intros b a k [<- | Hb] H1 H2; pose proof alloc_ceiling_range as CR.
  - pose proof store0_placed as (S1 & S2 & S3).
    pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AL0 & _).
    unfold kStoreBlockBytes in H2.
    apply (pol_S0 s mo (ae_store_blk E0) (ae_store_blk E0 + 2^23)); [| exact AL0| clear -S1; lia| clear -S2 CR; lia| exact H1| exact H2].
    unfold S0_ivs5. do 4 right. left. reflexivity.
  - pose proof (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & B2 & B3 & _).
    unfold app_mem in B1. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in B1. change kPageSize with 4096 in B3. unfold kStoreBlockBytes in *.
    apply (pol_of_pages_budgeted s mo b (b + 2^23)); [| clear -B1; lia| clear -B2 CR; lia| exact H1| exact H2].
    intros z Hz. unfold A_bundle.aS, A_policy5.aS, A_policy5.aSa, page_base_of. rewrite page_size_val.
    rewrite unsigned_lit by (clear -B1 B2 CR Hz; Z.div_mod_to_equations; lia). split; [clear -Hz B1; Z.div_mod_to_equations; lia|].
    do 3 right. exists b. split; [exact Hb|]. unfold kStoreBlockBytes. clear -B3 Hz B1. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_fs' : lazy_disjoint mo FSB0 (FSB0 + kFsBytes).
Proof.
  pose proof EV as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & _). rewrite EE, EFS in *.
  wfe_open WE. rewrite EF1, EF2 in WE22, WE12.
  unfold app_mem in V3. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in V3.
  apply lazy_disjoint_gen'; [rewrite kHighMemBeg_val; rewrite kFsBytes_val in *; clear -V3; lia| exact V6| | |].
  - intros b Hb. destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B6).
    destruct (B6 _ EIN) as [X|X]; cbn [fst snd] in X; [right| left]; exact X.
  - change kPtrArrayLen with 0x800000. clear -WE22. lia.
  - change kResvLen with 0x2000011000. clear -WE12. lia.
Qed.
Lemma pol_fs' : forall a k, FSB0 <= a -> a + Z.of_nat k <= FSB0 + kFsBytes -> POL s mo a k.
Proof.
  intros a k H1 H2. unfold POL. pose proof alloc_ceiling_range as CR.
  pose proof EV as (_ & _ & V3 & V4 & _). rewrite EFS in V3, V4. unfold app_mem in V3. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in V3.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) FSB0 (FSB0 + kFsBytes)); [exact lazy_disjoint_fs'| clear -V3; lia| clear -V4 CR; lia| exact H1| exact H2].
Qed.

End WithState.

(* [comment removed for export] *)
Lemma pol_sec_shadow' : forall (s : aps) (mo : Model) sc a k,
  res_ok (aps_alloc s) -> In sc (as_sec (aps_alloc s)) ->
  sc_map_beg sc mod 4096 = 0 -> 0 < sc_map_beg sc -> sc_map_beg sc + sc_map_size sc <= alloc_ceiling ->
  0 < sc_map_size sc -> sc_map_size sc mod 4096 = 0 ->
  A_SB + sc_map_beg sc / 8 <= a -> a + Z.of_nat k <= A_SB + (sc_map_beg sc + sc_map_size sc) / 8 -> POL s mo a k.
Proof.
  intros s mo sc a k RES Hsc M1 M2 M3 M4 M5 H1 H2. pose proof alloc_ceiling_range as CR.
  rewrite A_SB_val in *.
  apply (pol_of_pages_budgeted s mo (2147450880 + sc_map_beg sc / 8) (2147450880 + (sc_map_beg sc + sc_map_size sc) / 8));
    [| clear -M2; Z.div_mod_to_equations; lia| clear -M3 CR; Z.div_mod_to_equations; lia| exact H1| exact H2].
  intros z Hz.
  set (a' := sc_map_beg sc + 8 * (z - (2147450880 + sc_map_beg sc / 8))).
  assert (Ha' : sc_map_beg sc <= a' < sc_map_beg sc + sc_map_size sc) by (subst a'; clear -Hz; Z.div_mod_to_equations; lia).
  assert (Ez : z = A_SB + a' / 8).
  { subst a'. rewrite A_SB_val. clear -Hz. Z.div_mod_to_equations. lia. }
  rewrite Ez. destruct (page_base_of_shadow a' ltac:(clear -Ha' M2 M3 CR; lia)) as (-> & R1 & R2).
  unfold A_bundle.aS, A_policy5.aS, aSa. cbv zeta. rewrite unsigned_lit by (clear -R1; lia). split; [exact R2|].
  destruct (Z.ltb_spec (sc_map_size sc) kBigMapSize) as [SM|BG].
  - (* [comment removed for export] *)
    right. right. left. apply (RES sc Hsc). unfold residue_pages.
    replace (sc_map_size sc <? kBigMapSize) with true by (symmetry; apply Z.ltb_lt; exact SM).
    apply shadow_page_in_hull. exact Ha'.
  - pose proof (shadow_page_big (sc_map_beg sc) (sc_map_size sc) a' M1 M4 Ha') as BIG.
    destruct (remap_range (sc_map_beg sc) (sc_map_size sc)) as [pb plen] eqn:RR.
    destruct BIG as [[I1 I2] | BD].
    + right. left. exists sc. split; [exact Hsc|]. split; [clear -BG; lia|]. rewrite RR. cbn [fst snd]. change kPageSize with 4096 in I2. clear -I1 I2. lia.
    + right. right. left. apply (RES sc Hsc). unfold residue_pages.
      replace (sc_map_size sc <? kBigMapSize) with false by (symmetry; apply Z.ltb_ge; clear -BG; lia).
      cbn. destruct BD as [-> | ->]; tauto.
Qed.

(* [comment removed for export] *)
Section WithAWf.
Variables (s : aps) (mo : Model) (P : list Z) (D : list batch).
Hypothesis K : AKern E0 (aps_alloc s) mo.
Hypothesis WF : AWf E0 P D (aps_alloc s).
Hypothesis EV : ENVOK E0 FSB0 s.
Hypothesis ENV0 : env0_ok5 E0.
Let WE : wf_env E0. Proof. exact (proj1 WF). Qed.

Lemma pol_stack : forall a k, alloc_ceiling <= a -> a + Z.of_nat k <= 2^64 -> POL s mo a k.
Proof. intros. eapply pol_stack'; eassumption. Qed.
Lemma pol_img : forall a k, 0 <= a -> a + Z.of_nat k <= 0x603000 -> POL s mo a k.
Proof. intros. eapply pol_img'; eassumption. Qed.
Lemma pol_resv_range : forall r0 rl a k, resv_range_ok E0 r0 rl -> r0 <= a -> a + Z.of_nat k <= r0 + rl -> POL s mo a k.
Proof. intros. eapply pol_resv_range'; eassumption. Qed.
Lemma pol_thread : forall a k, ae_thread E0 <= a -> a + Z.of_nat k <= ae_thread E0 + 4096 -> POL s mo a k.
Proof. intros. eapply pol_thread'; eassumption. Qed.
Lemma pol_node_block : forall b a k,
  In b (ae_depot_nodes E0 :: as_node_blocks (aps_alloc s)) -> b <= a -> a + Z.of_nat k <= b + kDepotNodeBlockBytes -> POL s mo a k.
Proof. intros. eapply pol_node_block'; eassumption. Qed.
Lemma pol_ptr_head : forall a k,
  as_ptr_committed (aps_alloc s) = kChunksBlockCount ->
  ae_ptr_array E0 <= a -> a + Z.of_nat k <= ae_ptr_array E0 + kPtrArrayCommit -> POL s mo a k.
Proof. intros. eapply pol_ptr_head'; eassumption. Qed.
Lemma pol_space_shadow : forall a k,
  A_SB + ae_space_beg E0 / 8 <= a -> a + Z.of_nat k <= A_SB + (ae_space_beg E0 + 2^37) / 8 -> POL s mo a k.
Proof. intros. eapply pol_space_shadow'; eassumption. Qed.
Lemma pol_reginfo : forall a k,
  ae_space_beg E0 + 2^37 <= a -> a + Z.of_nat k <= ae_space_beg E0 + 2^37 + 4096 -> POL s mo a k.
Proof. intros. eapply pol_reginfo'; eassumption. Qed.
Lemma pol_fs_shadow : forall a k, A_SB + FSB0 / 8 <= a -> a + Z.of_nat k <= A_SB + (FSB0 + kFsBytes) / 8 -> POL s mo a k.
Proof. intros. eapply pol_fs_shadow'; eassumption. Qed.
Lemma pol_store_block : forall b a k,
  In b (ae_store_blk E0 :: as_store_blocks (aps_alloc s)) -> b <= a -> a + Z.of_nat k <= b + kStoreBlockBytes -> POL s mo a k.
Proof. intros. eapply pol_store_block'; eassumption. Qed.
Lemma pol_fs : forall a k, FSB0 <= a -> a + Z.of_nat k <= FSB0 + kFsBytes -> POL s mo a k.
Proof. intros. eapply pol_fs'; eassumption. Qed.

(* [comment removed for export] *)
Lemma pol_user : forall c a k, 1 <= c <= kLargestClassID ->
  region_beg (ae_space_beg E0) c <= a -> a + Z.of_nat k <= region_beg (ae_space_beg E0) c + rg_mapped_user (get_region (aps_alloc s) c) ->
  (0 < Z.of_nat k) ->
  POL s mo a k.
Proof.
  intros c a k Hc H1 H2 Hk. unfold POL. pose proof alloc_ceiling_range as CR.
  assert (HU : 0 < rg_mapped_user (get_region (aps_alloc s) c)) by lia.
  pose proof (ak_user _ _ _ K c Hc HU) as U. pose proof (eager_rw_lazy_disjoint _ _ _ U) as LD.
  pose proof (proj1 WF) as (_ & W2 & W3 & W4 & W5 & _). rewrite kHighMemBeg_val in W2.
  pose proof (proj2 (proj1 (proj2 WF)) c Hc) as RG. cbv zeta in RG. unfold region_of in RG.
  destruct RG as (R1 & _ & R3 & _). unfold kFreeArrayOffset in R3.
  unfold kLargestClassID in Hc. change kSpaceSize with (2^37) in W4.
  assert (RB : ae_space_beg E0 <= region_beg (ae_space_beg E0) c
               /\ region_beg (ae_space_beg E0) c + rg_mapped_user (get_region (aps_alloc s) c) <= 2^64).
  { unfold region_beg. change kRegionSize with 4294967296. clear -Hc W2 W3 W4 W5 R3 CR. nia. }
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) (region_beg (ae_space_beg E0) c)
            (region_beg (ae_space_beg E0) c + rg_mapped_user (get_region (aps_alloc s) c))); [exact LD| clear -RB W2 W3; lia| clear -RB; lia| exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma pol_fa : forall c a k, 1 <= c <= kLargestClassID ->
  free_array (ae_space_beg E0) c <= a -> a + Z.of_nat k <= free_array (ae_space_beg E0) c + rg_mapped_fa (get_region (aps_alloc s) c) ->
  (0 < Z.of_nat k) ->
  POL s mo a k.
Proof.
  intros c a k Hc H1 H2 Hk. unfold POL. pose proof alloc_ceiling_range as CR.
  assert (HU : 0 < rg_mapped_fa (get_region (aps_alloc s) c)) by lia.
  pose proof (ak_fa _ _ _ K c Hc HU) as U. pose proof (eager_rw_lazy_disjoint _ _ _ U) as LD.
  pose proof (proj1 WF) as (_ & W2 & W3 & W4 & W5 & _). rewrite kHighMemBeg_val in W2.
  pose proof (proj2 (proj1 (proj2 WF)) c Hc) as RG. cbv zeta in RG. unfold region_of in RG.
  destruct RG as (_ & _ & _ & _ & F1 & _ & F3 & _). unfold kFreeArraySize in F3.
  unfold kLargestClassID in Hc. change kSpaceSize with (2^37) in W4.
  assert (RB : ae_space_beg E0 <= free_array (ae_space_beg E0) c
               /\ free_array (ae_space_beg E0) c + rg_mapped_fa (get_region (aps_alloc s) c) <= 2^64).
  { unfold free_array, region_beg, kFreeArrayOffset. change kRegionSize with 4294967296. clear -Hc W2 W3 W4 W5 F1 F3 CR. nia. }
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) (free_array (ae_space_beg E0) c)
            (free_array (ae_space_beg E0) c + rg_mapped_fa (get_region (aps_alloc s) c))); [exact LD| clear -RB W2 W3; lia| clear -RB; lia| exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma pol_sec_map : forall sc a k,
  In sc (as_sec (aps_alloc s)) -> sc_map_beg sc <= a -> a + Z.of_nat k <= sc_map_beg sc + sc_map_size sc -> POL s mo a k.
Proof.
  intros sc a k Hsc H1 H2. unfold POL. pose proof alloc_ceiling_range as CR.
  pose proof (proj2 (ak_sec _ _ _ K sc Hsc)) as T. pose proof (eager_rw_lazy_disjoint _ _ _ T) as LD.
  destruct WF as (_ & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  destruct (WS3 sc Hsc) as (M1 & M2 & M3 & _). unfold app_mem in M2. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in M2.
  eapply (acc_ok_of_lazy_disjoint mo (aSc s) (sc_map_beg sc) (sc_map_beg sc + sc_map_size sc)); [exact LD| clear -M2; lia| clear -M3 CR; lia| exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma pol_sec_shadow : forall sc a k,
  res_ok (aps_alloc s) -> In sc (as_sec (aps_alloc s)) ->
  A_SB + sc_map_beg sc / 8 <= a -> a + Z.of_nat k <= A_SB + (sc_map_beg sc + sc_map_size sc) / 8 -> POL s mo a k.
Proof.
  intros sc a k RES Hsc H1 H2.
  destruct WF as (_ & WR & WC & WK & WQ & WS & WD). destruct WS as (_ & _ & WS3 & _).
  destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6). change kPageSize with 4096 in *. unfold app_mem in M2. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in M2.
  eapply pol_sec_shadow'; [exact RES| exact Hsc| exact M1| clear -M2; lia| exact M3| exact M4| exact M5| exact H1| exact H2].
Qed.
End WithAWf.
End Pol.
End RC__1.
