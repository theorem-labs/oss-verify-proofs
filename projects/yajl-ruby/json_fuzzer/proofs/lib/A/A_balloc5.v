(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot
  AsanBudget AsanBudget2 AsanRepFrame AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_live A_policy5 A_budget5 A_slack5 A_bundle A_benv5 AI_shadow AI_lowshadow AYajlRep AF_fakestack_rep AF_place.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Section Balloc.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.
(* [comment removed for export] *)
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Variable rt_fp : aenv -> Z -> Prop.
Hypothesis RTMisc_agree : forall m m', RTMisc E0 m -> (forall a, rt_fp E0 a -> m' (wa a) = m (wa a)) -> RTMisc E0 m'.
Hypothesis rt_fp_where2 : forall a, rt_fp E0 a -> (0x10000 <= a < 0x603000 /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Variable so_fp : Z -> Prop.
Hypothesis StdioRep_agree : forall so m m', StdioRep so m -> (forall a, so_fp a -> m' (wa a) = m (wa a)) -> StdioRep so m'.
Hypothesis so_fp_where2 : forall a, so_fp a -> 0x10000 <= a < 0x603000 /\ ~ in_cells img_mut a.

#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (A_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (A_bundle.aN E0 FSB0 HR0).
#[local] Notation aNzc := (A_bundle.aNz E0 FSB0 HR0).
#[local] Notation aEBc := (A_bundle.aEB EB0).
#[local] Notation ENVOKc := (ENVOK E0 FSB0).

Ltac ahk_open H :=
  destruct H as (Hrep & Hwf & Hkern & Hkvm & Hres & Hqb & Hdi & Hbinv & Hbm & Hfs & Hicp & Hyst & Hlow & Hrt & Hso & Hkm & Hli & Hbud & Hmi & Henv & Hycl & Hss & Hcs).
(* [comment removed for export] *)
Ltac cstat := try clear HR0_ok; try clear EB0_ok; try clear ENV_depot; try clear HS_tot.
Ltac chyps := cstat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sA (a : astate) (s : aps) : aps := aps_set_alloc a s.

Definition ATOK (R R' : Z) (s : aps) (mo : Model) : Prop :=
     KIA (aSc s) (aNc s) (aEBc s) mo
  /\ (0 <= R /\ OSL aEBc aNzc R s mo)
  /\ ENVOKc s
  /\ vm_limit (m_vmmaps mo) = 2^39
  /\ KVM L0 RES0 mo (aps_alloc s)
  /\ (0 <= R' /\ PSL R' (m_vmmaps mo)).

Lemma ATOK_KIA : forall R R' s mo, ATOK R R' s mo -> KIA (aSc s) (aNc s) (aEBc s) mo.
Proof. intros R R' s mo (K & _). exact K. Qed.
Lemma ATOK_LI : forall R R' s mo, ATOK R R' s mo -> LI (aSc s) (aNc s) (aEBc s) mo.
Proof. intros R R' s mo ((L & _) & _). exact L. Qed.
Lemma ATOK_KVM : forall R R' s mo, ATOK R R' s mo -> KVM L0 RES0 mo (aps_alloc s).
Proof. intros R R' s mo (_ & _ & _ & _ & KV & _). exact KV. Qed.
Lemma ATOK_OSL : forall R R' s mo, ATOK R R' s mo -> 0 <= R /\ OSL aEBc aNzc R s mo.
Proof. intros R R' s mo (_ & O & _). exact O. Qed.
Lemma ATOK_PSL : forall R R' s mo, ATOK R R' s mo -> 0 <= R' /\ PSL R' (m_vmmaps mo).
Proof. intros R R' s mo (_ & _ & _ & _ & _ & P). exact P. Qed.
Lemma ATOK_ENVOK : forall R R' s mo, ATOK R R' s mo -> ENVOKc s.
Proof. intros R R' s mo (_ & _ & E & _). exact E. Qed.
Lemma ATOK_limit : forall R R' s mo, ATOK R R' s mo -> vm_limit (m_vmmaps mo) = 2^39.
Proof. intros R R' s mo (_ & _ & _ & V & _). exact V. Qed.
Lemma ATOK_le : forall R R' Q Q' s mo, ATOK R R' s mo -> 0 <= Q <= R -> 0 <= Q' <= R' -> ATOK Q Q' s mo.
Proof.
  chyps.
  intros R R' Q Q' s mo (K & [O1 O2] & E & V & KV & [P1 P2]) HQ HQ'. split; [exact K|]. split; [split; [lia| eapply OSL_weaken; [| exact O2]; lia]|].
  split; [exact E|]. split; [exact V|]. split; [exact KV|]. split; [lia| eapply PSL_weaken; [| exact P2]; lia].
Qed.
Lemma ATOK_magree : forall R R' s mo mo', ATOK R R' s mo -> magree mo mo' -> KIA (aSc s) (aNc s) (aEBc s) mo' -> ATOK R R' s mo'.
Proof.
  chyps.
  intros R R' s mo mo' (K & O & E & V & KV & P) Hag K'. pose proof (magree_vmmaps _ _ Hag) as MV.
  split; [exact K'|]. split; [unfold OSL in *; rewrite MV; exact O|]. split; [exact E|].
  rewrite <- MV in V. split; [exact V|]. split; [eapply KVM_magree; [exact KV| exact Hag]|]. rewrite MV. exact P.
Qed.
(* [comment removed for export] *)
Lemma ATOK_backing_room : forall R R' s mo nZ, ATOK R R' s mo -> 0 <= nZ <= 4096 * R ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros R R' s mo nZ (K & [O1 O2] & _) HnZ. destruct K as (L & _).
  eapply (OSL_grant aEBc aNzc R s mo _ _ nZ L); [apply AHK_aN_bound; exact HR0_ok| exact O2| exact HnZ].
Qed.
Lemma ATOK_window : forall R R' s mo nZ, ATOK R R' s mo -> 0 <= nZ <= NMAXA ->
  page_size + nZ + gap_weight nZ (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= alloc_top (m_vmmaps mo).
Proof.
  chyps.
  intros R R' s mo nZ (K & _ & _ & _ & KV & [P1 P2]) HnZ. apply (PSL_window R'); [exact P2| exact P1| exact HnZ|].
  destruct KV as (_ & _ & _ & _ & _ & TOP). rewrite TOP. pose proof alloc_ceiling_range. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ATOK_open : forall s LB LF m mo R,
  AHKc s LB LF m mo -> 0 <= R <= aps_credit s -> nbig LB <= 8000 -> ATOK R OPSLACK s mo.
Proof.
  intros s LB LF m mo R H HR NB.
  pose proof (AHK_osl _ _ _ _ _ _ _ _ HR0_ok EB0_ok ENV_depot s LB LF m mo R H HR) as O.
  pose proof (AHK_psl _ _ _ _ _ _ _ _ ENV_depot HS_tot s LB LF m mo H NB) as P.
  ahk_open H. destruct Hkm as (Kh & Kmi & Klim).
  split; [split; [exact Hli| split; [exact Kmi| exact Kh]]|]. split; [split; [lia| exact O]|]. split; [exact Henv|].
  split; [exact Klim|]. split; [exact Hkvm|]. split; [unfold OPSLACK; lia| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_fp (a a' : astate) : Prop :=
  regions_bytes a' = regions_bytes a /\ as_sec a' = as_sec a /\ as_ptr_committed a' = as_ptr_committed a
  /\ as_residue a' = as_residue a /\ as_node_blocks a' = as_node_blocks a /\ as_store_blocks a' = as_store_blocks a.

Lemma same_fp_refl : forall a, same_fp a a. Proof. intros; repeat split; reflexivity. Qed.
Lemma same_fp_sym : forall a a', same_fp a a' -> same_fp a' a.
Proof. intros a a' (H1 & H2 & H3 & H4 & H5 & H6). repeat split; congruence. Qed.
Lemma same_fp_trans : forall a b c, same_fp a b -> same_fp b c -> same_fp a c.
Proof. intros a b c (H1 & H2 & H3 & H4 & H5 & H6) (G1 & G2 & G3 & G4 & G5 & G6). repeat split; congruence. Qed.

Lemma aS_same : forall a a' s w, same_fp a a' -> aSc (sA a' s) w <-> aSc (sA a s) w.
Proof.
  chyps.
  intros a a' s w (H1 & H2 & H3 & H4 & H5 & H6). unfold A_bundle.aS, A_policy5.aS, aSa, sA, in_interiors, in_stores. cbn [aps_alloc aps_set_alloc].
  rewrite H2, H4, H6. tauto.
Qed.
Lemma cover_same : forall a a' s, same_fp a a' -> cover (A0 E0 FSB0 HR0) (aps_alloc (sA a' s)) = cover (A0 E0 FSB0 HR0) (aps_alloc (sA a s)).
Proof.
  chyps.
  intros a a' s (H1 & H2 & H3 & H4 & H5 & H6). unfold cover, cover_int, cover_res, cover_st, sA. cbn [aps_alloc aps_set_alloc].
  rewrite H2, H4, H6. reflexivity.
Qed.
Lemma aN_same : forall a a' s, same_fp a a' -> aNc (sA a' s) = aNc (sA a s).
Proof. intros. unfold A_bundle.aN, A_policy5.aN, aNa. rewrite (cover_same a a' s H). reflexivity. Qed.
Lemma aEB_same : forall a a' s, same_fp a a' -> aEBc (sA a' s) = aEBc (sA a s).
Proof.
  chyps.
  chyps.
  intros a a' s (H1 & H2 & H3 & H4 & H5 & H6). unfold A_bundle.aEB, A_policy5.aEB, aEBa, a_eager_bytes, AsanState.sec_bytes, sA. cbn [aps_alloc aps_set_alloc].
  rewrite H1, H2, H3, H5. reflexivity.
Qed.
Lemma aNz_same : forall a a' s, same_fp a a' -> aNzc (sA a' s) = aNzc (sA a s).
Proof.
  chyps.
  intros a a' s (H1 & H2 & H3 & H4 & H5 & H6). unfold A_bundle.aNz, A_policy5.aNz, aNza, interiors_bound, sA. cbn [aps_alloc aps_set_alloc].
  rewrite H2, H4, H6. reflexivity.
Qed.
Lemma amaps_same : forall a a', same_fp a a' -> amaps a' = amaps a.
Proof. intros a a' (H1 & H2 & H3 & H4 & H5 & H6). unfold amaps. rewrite H2, H5, H6. reflexivity. Qed.

Lemma LI_ext : forall (S S' : word -> Prop) N EB mo, (forall w, S w <-> S' w) -> LI S N EB mo -> LI S' N EB mo.
Proof.
  chyps.
  chyps.
  intros S S' N EB mo E [L1 L2 L3 L4 L5]. constructor; auto.
  - apply Forall_forall. intros p Hp. apply E. exact (proj1 (Forall_forall _ _) L2 p Hp).
  - intros l ND HF. apply L3; [exact ND|]. apply Forall_forall. intros p Hp. apply E. exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma ATOK_same_fp : forall R R' s a a' mo, ATOK R R' (sA a s) mo -> same_fp a a' -> ATOK R R' (sA a' s) mo.
Proof.
  chyps.
  intros R R' s a a' mo ((L & MI & HH) & [O1 O2] & E & V & KV & P) SF.
  split; [split; [| split; [exact MI| exact HH]]|].
  - rewrite (aN_same a a' s SF), (aEB_same a a' s SF). eapply LI_ext; [| exact L]. intros w. symmetry. apply aS_same. exact SF.
  - split; [split; [exact O1| unfold OSL in *; rewrite (aEB_same a a' s SF), (aNz_same a a' s SF); exact O2]|].
    split; [exact E|]. split; [exact V|]. split; [| exact P].
    unfold KVM in *. cbn [aps_alloc sA aps_set_alloc] in *. rewrite (amaps_same a a' SF). exact KV.
Qed.

(* [comment removed for export] *)
Lemma ATOK_aps : forall R R' s s' mo,
  ATOK R R' s mo -> aps_env s' = aps_env s -> aps_fsbase s' = aps_fsbase s -> aps_alloc s' = aps_alloc s -> ATOK R R' s' mo.
Proof.
  chyps.
  intros R R' s s' mo ((L & MI & HH) & [O1 O2] & E & V & KV & P) E1 E2 E3.
  assert (ES : forall w, aSc s w <-> aSc s' w) by (intros w; unfold A_bundle.aS, A_policy5.aS; rewrite E3; tauto).
  assert (EN : aNc s' = aNc s) by (unfold A_bundle.aN, A_policy5.aN; rewrite E3; reflexivity).
  assert (EE : aEBc s' = aEBc s) by (unfold A_bundle.aEB, A_policy5.aEB; rewrite E3; reflexivity).
  assert (EZ : aNzc s' = aNzc s) by (unfold A_bundle.aNz, A_policy5.aNz; rewrite E3; reflexivity).
  split; [split; [| split; [exact MI| exact HH]]|].
  - rewrite EN, EE. eapply LI_ext; [exact ES| exact L].
  - split; [split; [exact O1| unfold OSL in *; rewrite EE, EZ; exact O2]|]. split; [| split; [exact V| split; [rewrite E3; exact KV| exact P]]].
    unfold ENVOK in *. rewrite E1, E2. exact E.
Qed.

Lemma ATOK_sA_self : forall R R' s mo, ATOK R R' s mo -> ATOK R R' (sA (aps_alloc s) s) mo.
Proof. intros R R' s mo T. eapply ATOK_aps; [exact T| reflexivity| reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aw_ok (a a' : astate) (lo sp : Z) (iv : Z * Z) : Prop :=
  let x := fst iv in let y := snd iv in
     (lo <= x /\ y <= sp)                                                                            (* [comment removed for export] *)
  \/ (exists r, In r img_mut /\ fst r <= x /\ y <= fst r + snd r)                                    (* [comment removed for export] *)
  \/ (exists r, In r (arep_thr_ranges E0) /\ fst r <= x /\ y <= fst r + snd r)                       (* [comment removed for export] *)
  \/ (ae_resv_beg E0 <= x /\ y <= ae_resv_beg E0 + kResvLen)                                         (* [comment removed for export] *)
  \/ (ae_ptr_array E0 <= x /\ y <= ae_ptr_array E0 + kPtrArrayLen)                                   (* [comment removed for export] *)
  \/ (exists sc, (In sc (as_sec a) \/ In sc (as_sec a')) /\ sc_map_beg sc <= x /\ y <= sc_map_beg sc + sc_map_size sc)  (* [comment removed for export] *)
  \/ (exists b, In b (ae_depot_nodes E0 :: as_node_blocks a') /\ b <= x /\ y <= b + kDepotNodeBlockBytes)            (* [comment removed for export] *)
  \/ (exists b, In b (ae_store_blk E0 :: as_store_blocks a') /\ b <= x /\ y <= b + kStoreBlockBytes)                  (* [comment removed for export] *)
  \/ (((LSHI <= x /\ y <= A_SB + kLowAppEnd / 8) \/ (A_SB + kHighMemBeg / 8 <= x /\ y <= kHighMemBeg))                  (* [comment removed for export] *)
      /\ forall z, x <= z < y -> sh_excluded E0 (8 * (z - A_SB)) = false).

(* [comment removed for export] *)
Definition rest_fp (x : Z) : Prop :=
  fs_fp FSB0 x \/ in_cells icp_globals_cellsL x \/ in_cells ay_statics_cellsL x \/ in_cells ay_cells_cellsL x \/ (LSLO <= x < LSHI)
  \/ rt_fp E0 x \/ so_fp x.
(* [comment removed for export] *)
Definition restU (x : Z) : Prop :=
     (FSB0 <= x < FSB0 + kFsBytes)
  \/ (FS_SB + FSB0 / 8 <= x < FS_SB + FSB0 / 8 + kFsBytes / 8)
  \/ (0x10000 <= x < 0x603000 /\ ~ in_cells img_mut x)
  \/ (LSLO <= x < LSHI)
  \/ ((ae_thread E0 <= x < ae_thread E0 + 8) \/ (ae_thread E0 + 48 <= x < ae_thread E0 + 64))
  \/ (fp_ctx PL0 <= x < fp_ctx PL0 + 160)
  \/ (fp_dtls PL0 <= x < fp_dtls PL0 + 4096).
Lemma rest_fp_where : forall x, rest_fp x -> restU x.
Proof.
  cstat.
  intros x [H|[H|[H|[H|[H|[H|H]]]]]]; unfold restU.
  - unfold fs_fp, fs_shadow in H. tauto.
  - do 2 right; left. apply img_cells_not_mut. auto.
  - do 2 right; left. apply img_cells_not_mut. auto.
  - do 2 right; left. apply img_cells_not_mut. auto.
  - tauto.
  - destruct (rt_fp_where2 x H) as [X|[X|[X|X]]]; tauto.
  - do 2 right; left. apply so_fp_where2. exact H.
Qed.

(* [comment removed for export] *)
Lemma thr_ranges_where : forall r, In r (arep_thr_ranges E0) ->
  (ae_thread E0 + 8 <= fst r /\ fst r + snd r <= ae_thread E0 + 48) \/ (ae_thread E0 + 80 <= fst r /\ fst r + snd r <= ae_thread E0 + 3169).
Proof.
  clear. intros r Hr. unfold arep_thr_ranges in Hr.
  unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma kLowAppEnd_val : kLowAppEnd = 0x7fff7000. Proof. reflexivity. Qed.
Ltac zconsts :=
  unfold restU in *;
  rewrite ?kHighMemBeg_val, ?A_SB_val, ?kLowAppEnd_val in *;
  unfold kFsBytes, kResvLen, kPtrArrayLen, kDepotNodeBlockBytes, kStoreBlockBytes, kIArenaLen, FS_SB, LSLO, LSHI in *;
  change (2^23) with 8388608 in *; change (2^20) with 1048576 in *.

(* [comment removed for export] *)
Record sfacts : Prop := mkSF {
  sf_cr   : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000;
  sf_fs   : ae_fs_beg E0 = FSB0 /\ ae_fs_len E0 = kFsBytes;
  sf_fsp  : 0x603000 <= FSB0 /\ FSB0 + kFsBytes <= alloc_ceiling /\ (FSB0 + kFsBytes <= 0x7fff7000 \/ 0x10007fff8000 <= FSB0) /\ FSB0 mod 4096 = 0;
  sf_fsres: In (FSB0, kFsBytes) (ae_reserved E0);
  sf_T    : 0x1000 <= ae_thread E0 /\ ae_thread E0 + 4096 <= alloc_ceiling /\ (ae_thread E0 + 4096 <= 0x10000 \/ 0x603000 <= ae_thread E0)
            /\ (ae_thread E0 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ae_thread E0);
  sf_Tres : In (ae_thread E0, 4096) (ae_reserved E0);
  sf_Tfs  : ae_thread E0 + 4096 <= FSB0 \/ FSB0 + kFsBytes <= ae_thread E0;
  sf_ctx  : exists c0 cl, In (c0, cl) (ae_reserved E0) /\ c0 <= fp_ctx PL0 /\ fp_ctx PL0 + 160 <= c0 + cl /\ c0 + cl <= alloc_ceiling
              /\ 0x1000 <= c0 /\ (c0 + cl <= 0x10000 \/ 0x603000 <= c0) /\ (c0 + cl <= 0x7fff7000 \/ 0x10007fff8000 <= c0)
              /\ (c0 + cl <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= c0) /\ (c0 + cl <= FSB0 \/ FSB0 + kFsBytes <= c0)
              /\ (c0 + cl <= ae_store_blk E0 \/ ae_store_blk E0 + 2^23 <= c0) /\ (c0 + cl <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= c0)
              /\ (c0 + cl <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= c0)
              /\ (fp_ctx PL0 + 160 <= ae_thread E0 \/ ae_thread E0 + 4096 <= fp_ctx PL0);
  sf_dtls : exists d0 dl, In (d0, dl) (ae_reserved E0) /\ d0 <= fp_dtls PL0 /\ fp_dtls PL0 + 4096 <= d0 + dl /\ d0 + dl <= alloc_ceiling
              /\ 0x1000 <= d0 /\ (d0 + dl <= 0x10000 \/ 0x603000 <= d0) /\ (d0 + dl <= 0x7fff7000 \/ 0x10007fff8000 <= d0)
              /\ (d0 + dl <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= d0) /\ (d0 + dl <= FSB0 \/ FSB0 + kFsBytes <= d0)
              /\ (d0 + dl <= ae_store_blk E0 \/ ae_store_blk E0 + 2^23 <= d0) /\ (d0 + dl <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= d0)
              /\ (d0 + dl <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= d0)
              /\ (fp_dtls PL0 + 4096 <= ae_thread E0 \/ ae_thread E0 + 4096 <= fp_dtls PL0);
  sf_img  : In (ae_img E0) (ae_reserved E0) /\ fst (ae_img E0) = 0x10000 /\ 0x5f3000 <= snd (ae_img E0)
}.

Lemma sfacts_of : forall s, AWf E0 [] [] (aps_alloc s) -> ENVOKc s -> FSRep asegs E0 FSB0 (aps_fs s) [] = FSRep asegs E0 FSB0 (aps_fs s) [] ->
  FSB0 mod 4096 = 0 -> sfacts.
Proof.
  cstat.
  intros s WF ENV _ F4K. pose proof alloc_ceiling_range as CR.
  destruct ENV as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & [EI1 EI2]).
  pose proof (proj1 WF) as WE.
  pose proof WE as (_ & W2 & _ & _ & W5 & _ & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & W28 & W29 & W30 & W31 & W32 & W33 & W34 & W35).
  destruct PL0OK as ((c0 & cl & (CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7 & CR8) & CC1 & CC2) & (d0 & dl & (DR1 & DR2 & DR3 & DR4 & DR5 & DR6 & DR7 & DR8) & DD1 & DD2) & (TR1 & TR2 & TR3 & TR4 & TR5 & TR6 & TR7 & TR8) & CT & DT & CD & CTXA).
  rewrite EE, EFS in *. rewrite EF1, EF2 in *.
  constructor.
  - exact CR.
  - auto.
  - unfold app_mem, img_sep in *. rewrite EI1 in W34. zconsts. clear -V3 V4 W34 EI2 F4K. lia.
  - exact W9.
  - destruct TR2 as (P1 & P2 & P3 & P4). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. clear -P1 P2 P3 P4. lia.
  - exact W13.
  - exact W21.
  - exists c0, cl. destruct CR2 as (P1 & P2 & P3 & P4). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. repeat split; auto; clear -P1 P2 P3 P4; lia.
  - exists d0, dl. destruct DR2 as (P1 & P2 & P3 & P4). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. repeat split; auto; clear -P1 P2 P3 P4; lia.
  - auto.
Qed.

(* [comment removed for export] *)
Definition objapart (b len : Z) : Prop :=
  0 <= len /\ app_mem b len /\ b + len <= alloc_ceiling /\ (forall r, In r (ae_reserved E0) -> b + len <= fst r \/ fst r + snd r <= b).

Lemma sep_obj : forall b len x, sfacts -> objapart b len -> b <= x < b + len -> restU x -> False.
Proof.
  chyps.
  intros b len x SF (L0' & AM & CE & AP) Hx RU.
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)].
  pose proof (AP _ FR) as AF. pose proof (AP _ TRS) as AT. pose proof (AP _ IR) as AI. rewrite I1 in AI. cbn [fst snd] in AF, AT, AI.
  unfold app_mem in AM. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]].
  - clear -AF Hx R. lia.
  - clear -AM Hx R F1 F2 CR. Z.div_mod_to_equations. lia.
  - clear -AI I2 Hx R L0' AM. lia.
  - clear -AM Hx R. lia.
  - clear -AT Hx R. lia.
  - destruct CX as (c0 & cl & C1 & C2 & C3 & _). pose proof (AP _ C1) as AC. cbn [fst snd] in AC. clear -AC C2 C3 Hx R. lia.
  - destruct DX as (d0 & dl & D1 & D2 & D3 & _). pose proof (AP _ D1) as AD. cbn [fst snd] in AD. clear -AD D2 D3 Hx R. lia.
Qed.

Lemma sep_stack : forall lo x, sfacts -> alloc_ceiling <= lo -> lo <= x -> restU x -> False.
Proof.
  chyps.
  intros lo x SF LO Hx RU.
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)]. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR F1 F2 T2 LO Hx R; Z.div_mod_to_equations; lia).
  - destruct CX as (c0 & cl & _ & C2 & C3 & C4 & _). clear -C2 C3 C4 LO Hx R. lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & D4 & _). clear -D2 D3 D4 LO Hx R. lia.
Qed.

Lemma sep_imgmut : forall x, sfacts -> 0x10000 <= x < 0x603000 -> in_cells img_mut x -> restU x -> False.
Proof.
  chyps.
  intros x SF Hx IM RU.
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)]. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR F1 F2 T3 Hx R; Z.div_mod_to_equations; lia).
  - exact (NM IM).
  - destruct CX as (c0 & cl & _ & C2 & C3 & _ & _ & C6 & _). clear -C2 C3 C6 Hx R. lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & _ & _ & D6 & _). clear -D2 D3 D6 Hx R. lia.
Qed.

Lemma sep_thr : forall r x, sfacts -> In r (arep_thr_ranges E0) -> fst r <= x < fst r + snd r -> restU x -> False.
Proof.
  chyps.
  intros r x SF Hr Hx RU. pose proof (thr_ranges_where r Hr) as TW.
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)]. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR F1 F2 T1 T2 T3 T4 TF TW Hx R; Z.div_mod_to_equations; lia).
  - destruct CX as (c0 & cl & _ & C2 & C3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). clear -C2 C3 CT TW Hx R. lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & DT). clear -D2 D3 DT TW Hx R. lia.
Qed.

Lemma sep_resv : forall x, sfacts -> AWf E0 [] [] (astate0 E0) \/ (exists a, AWf E0 [] [] a) ->
  ae_resv_beg E0 <= x < ae_resv_beg E0 + kResvLen -> restU x -> False.
Proof.
  chyps.
  intros x SF WFX Hx RU.
  assert (WE : wf_env E0) by (destruct WFX as [W|[a W]]; exact (proj1 W)).
  pose proof WE as (_ & W2 & _ & _ & W5 & _ & _ & _ & _ & _ & _ & W12 & _ & _ & _ & _ & _ & _ & W19 & _).
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)].
  rewrite EF1, EF2 in *. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR W2 W5 W12 W19 F1 F2 Hx R; Z.div_mod_to_equations; lia).
  - destruct CX as (c0 & cl & _ & C2 & C3 & _ & _ & _ & _ & C8 & _). clear -C2 C3 C8 Hx R. lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & _ & _ & _ & _ & D8 & _). clear -D2 D3 D8 Hx R. lia.
Qed.

Lemma sep_ptr : forall x, sfacts -> wf_env E0 -> ae_ptr_array E0 <= x < ae_ptr_array E0 + kPtrArrayLen -> restU x -> False.
Proof.
  chyps.
  intros x SF WE Hx RU.
  pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W16 & W17 & _ & _ & _ & _ & W22 & W23 & _ & _ & _ & _ & _ & _ & _ & _ & _ & W33 & _).
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)].
  rewrite EF1, EF2 in *. unfold app_mem, img_sep in W16, W33. rewrite I1 in W33. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR W16 W17 W22 W23 W33 I2 F1 F2 Hx R; Z.div_mod_to_equations; lia).
  - destruct CX as (c0 & cl & _ & C2 & C3 & _ & _ & _ & _ & _ & _ & _ & C11 & _). clear -C2 C3 C11 Hx R. lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & _ & _ & _ & _ & _ & _ & _ & D11 & _). clear -D2 D3 D11 Hx R. lia.
Qed.

Lemma sep_shadow : forall x, sfacts ->
  ((LSHI <= x < A_SB + kLowAppEnd / 8) \/ (A_SB + kHighMemBeg / 8 <= x < kHighMemBeg)) ->
  sh_excluded E0 (8 * (x - A_SB)) = false -> restU x -> False.
Proof.
  chyps.
  intros x SF Hx EX RU.
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)].
  unfold sh_excluded, in_fakestack in EX. rewrite EF1, EF2 in EX.
  apply Bool.orb_false_iff in EX as [EX _]. apply Bool.orb_false_iff in EX as [EX _]. apply Bool.andb_false_iff in EX.
  zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR F1 F2 F3 T4 Hx R; Z.div_mod_to_equations; lia).
  - destruct EX as [EX|EX]; [apply Z.leb_gt in EX| apply Z.ltb_ge in EX]; clear -EX F4 R Hx; Z.div_mod_to_equations; lia.
  - destruct CX as (c0 & cl & _ & C2 & C3 & _ & _ & _ & C7 & _). clear -C2 C3 C7 Hx R. Z.div_mod_to_equations; lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & _ & _ & _ & D7 & _). clear -D2 D3 D7 Hx R. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma sec_objapart : forall a sc, AWf E0 [] [] a -> In sc (as_sec a) -> objapart (sc_map_beg sc) (sc_map_size sc).
Proof.
  chyps.
  intros a sc WF Hsc. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & SC3 & _) & _).
  destruct (SC3 sc Hsc) as (_ & Q2 & Q3 & Q4 & _ & _ & QR). split; [lia|]. split; [exact Q2|]. split; [exact Q3| exact QR].
Qed.
Lemma blocks_objapart : forall a' mo' b len, AKern E0 a' mo' ->
  (In b (as_node_blocks a') /\ len = kDepotNodeBlockBytes) \/ (In b (as_store_blocks a') /\ len = kStoreBlockBytes) -> objapart b len.
Proof.
  chyps.
  intros a' mo' b len K H. destruct (ak_blocks_sep _ _ _ K b len H) as (B1 & B2 & _ & _ & _ & BR).
  split; [destruct H as [[_ ->]|[_ ->]]; unfold kDepotNodeBlockBytes, kStoreBlockBytes; lia|]. split; [exact B1|]. split; [exact B2| exact BR].
Qed.

(* [comment removed for export] *)
Lemma sep_blk0 : forall x, sfacts -> wf_env E0 ->
  (ae_depot_nodes E0 <= x < ae_depot_nodes E0 + kDepotNodeBlockBytes) \/ (ae_store_blk E0 <= x < ae_store_blk E0 + kStoreBlockBytes) ->
  restU x -> False.
Proof.
  cstat.
  intros x SF WE Hx RU.
  destruct ENV0 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & _).
  destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)].
  destruct PL0OK as (_ & _ & (_ & _ & _ & _ & _ & TR6 & _ & TR8) & _).
  rewrite EF1, EF2 in *. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, img_sep in N3, N4, N5, N6. rewrite I1 in N5, N6. zconsts.
  destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR N3 N4 N5 N6 N8 N9 I2 TR6 TR8 F1 F2 Hx R; Z.div_mod_to_equations; lia).
  - destruct CX as (c0 & cl & _ & C2 & C3 & _ & _ & _ & _ & _ & _ & C10 & _ & C12 & _). clear -C2 C3 C10 C12 Hx R. lia.
  - destruct DX as (d0 & dl & _ & D2 & D3 & _ & _ & _ & _ & _ & _ & D10 & _ & D12 & _). clear -D2 D3 D10 D12 Hx R. lia.
Qed.

(* [comment removed for export] *)
Lemma aw_ok_sep : forall (a a' : astate) (mo' : Model) (lo sp : Z) (iv : Z * Z) (x : Z),
  sfacts -> AWf E0 [] [] a -> AWf E0 [] [] a' -> AKern E0 a' mo' -> alloc_ceiling <= lo ->
  aw_ok a a' lo sp iv -> fst iv <= x < snd iv -> rest_fp x -> False.
Proof.
  cstat.
  intros a a' mo' lo sp [x0 y0] x SF WF WF' K' LO AW Hx RF. cbn [fst snd] in *.
  apply rest_fp_where in RF. pose proof (proj1 WF) as WE.
  unfold aw_ok in AW. cbn [fst snd] in AW.
  destruct AW as [T|[T|[T|[T|[T|[T|[T|[T|T]]]]]]]].
  - eapply (sep_stack lo x SF LO); [lia| exact RF].
  - destruct T as (r & Hr & R1 & R2). pose proof (img_mut_low r Hr) as [M1 M2].
    apply (sep_imgmut x SF ltac:(lia) ltac:(exists r; split; [exact Hr| lia]) RF).
  - destruct T as (r & Hr & R1 & R2). eapply (sep_thr r x SF Hr); [lia| exact RF].
  - eapply (sep_resv x SF (or_intror (ex_intro _ a WF))); [lia| exact RF].
  - eapply (sep_ptr x SF WE); [lia| exact RF].
  - destruct T as (sc & Hsc & R1 & R2).
    assert (OB : objapart (sc_map_beg sc) (sc_map_size sc)) by (destruct Hsc as [Hsc|Hsc]; [exact (sec_objapart a sc WF Hsc)| exact (sec_objapart a' sc WF' Hsc)]).
    eapply (sep_obj _ _ x SF OB); [lia| exact RF].
  - destruct T as (b & [<-|Hb] & R1 & R2).
    + eapply (sep_blk0 x SF WE); [left; lia| exact RF].
    + eapply (sep_obj _ _ x SF (blocks_objapart a' mo' b _ K' (or_introl (conj Hb eq_refl)))); [lia| exact RF].
  - destruct T as (b & [<-|Hb] & R1 & R2).
    + eapply (sep_blk0 x SF WE); [right; lia| exact RF].
    + eapply (sep_obj _ _ x SF (blocks_objapart a' mo' b _ K' (or_intror (conj Hb eq_refl)))); [lia| exact RF].
  - destruct T as (RG & EXC). eapply (sep_shadow x SF); [clear -RG Hx; lia| exact (EXC x Hx)| exact RF].
Qed.

(* [comment removed for export] *)
Lemma outside_of_Forall : forall (Pw : Z * Z -> Prop) W x,
  Forall Pw W -> (forall iv, Pw iv -> fst iv <= x < snd iv -> False) -> outside W x.
Proof.
  chyps.
  intros Pw W x FW H. induction FW as [|[u v] W' Huv FW IH]; cbn; [exact I|].
  split; [| exact IH]. intros C. exact (H (u, v) Huv C).
Qed.

Lemma aw_munch_rest : forall (a a' : astate) (mo' : Model) (lo sp : Z) W (m m' : mem) x,
  sfacts -> AWf E0 [] [] a -> AWf E0 [] [] a' -> AKern E0 a' mo' -> alloc_ceiling <= lo ->
  munch W m m' -> Forall (aw_ok a a' lo sp) W -> rest_fp x -> m' (wa x) = m (wa x).
Proof.
  cstat.
  intros a a' mo' lo sp W m m' x SF WF WF' K' LO MU FW RF.
  assert (Rx : 0 <= x < 2^64).
  { pose proof (rest_fp_where x RF) as RU.
    destruct SF as [CR [EF1 EF2] (F1 & F2 & F3 & F4) FR (T1 & T2 & T3 & T4) TRS TF CX DX (IR & I1 & I2)]. zconsts.
    destruct RU as [R|[R|[[R NM]|[R|[R|[R|R]]]]]]; try (clear -CR F1 F2 T1 T2 R; Z.div_mod_to_equations; lia).
    - destruct CX as (c0 & cl & _ & C2 & C3 & C4 & C5 & _). clear -CR C2 C3 C4 C5 R. lia.
    - destruct DX as (d0 & dl & _ & D2 & D3 & D4 & D5 & _). clear -CR D2 D3 D4 D5 R. lia. }
  apply MU. rewrite wa_unsigned by exact Rx.
  eapply outside_of_Forall; [exact FW|]. intros iv Hiv Hin.
  exact (aw_ok_sep a a' mo' lo sp iv x SF WF WF' K' LO Hiv Hin RF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AHK_close : forall s s' LB LF m mo (a' : astate) (m' : mem) (mo' : Model) (LB' : list ablock) W (lo sp : Z) R R',
  AHKc s LB LF m mo ->
  (* [comment removed for export] *)
  aps_env s' = aps_env s -> aps_fsbase s' = aps_fsbase s -> aps_fs s' = aps_fs s -> aps_so s' = aps_so s -> aps_alloc s' = a' ->
  (* [comment removed for export] *)
  ARep asegs E0 (AsanDepot.DepotR asegs E0) a' m' -> AWf E0 [] [] a' -> AKern E0 a' mo' -> res_ok a' -> AQbound a' -> depot_inv E0 a' -> binv a' -> sstats_ok a' -> csmall a' ->
  blocks_match LB' a' ->
  ATOK R R' (sA a' s) mo' -> mem_inv asegs m' ->
  (* [comment removed for export] *)
  munch W m m' -> Forall (aw_ok (aps_alloc s) a' lo sp) W -> alloc_ceiling <= lo ->
  (* [comment removed for export] *)
  0 <= aps_credit s' -> 0 <= as_nprim_ever a' -> 0 <= as_ndepot_ins a' ->
  10000 * as_nprim_ever a' + zlen (as_residue a') + as_ndepot_ins a' + DEP LB' + aps_credit s'
    <= 10000 * as_nprim_ever (aps_alloc s) + zlen (as_residue (aps_alloc s)) + as_ndepot_ins (aps_alloc s) + DEP LB + aps_credit s ->
  AHKc s' LB' LF m' mo'.
Proof.
  cstat.
  intros s s' LB LF m mo a' m' mo' LB' W lo sp R R' H Q1 Q2 Q3 Q4 Q5 RP WF' K' RO QB DI BI SS CS BM TOK MI' MU FW LO C0 C1 C2 ACC'.
  pose proof H as H0. ahk_open H.
  pose proof Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & EIMG).
  assert (TOK' : ATOK R R' s' mo').
  { eapply ATOK_aps; [exact TOK| | |]; unfold sA, aps_set_alloc; cbn [aps_env aps_fsbase aps_alloc]; assumption. }
  rewrite EE in Q1. rewrite EFS in Q2.
  assert (WF0 : AWf E0 [] [] (aps_alloc s)) by (rewrite <- EE; exact Hwf).
  assert (F4K : FSB0 mod 4096 = 0) by (destruct Hfs as (G1 & _); rewrite EFS in G1; exact G1).
  assert (SF : sfacts) by (apply (sfacts_of s); [exact WF0| exact Henv| reflexivity| exact F4K]).
  rewrite EE, EFS in *.
  assert (AG : forall x, rest_fp x -> m' (wa x) = m (wa x)).
  { intros x RX. eapply (aw_munch_rest (aps_alloc s) a' mo' lo sp W m m' x); try eassumption. }
  pose proof (ATOK_KVM _ _ _ _ TOK') as KV. rewrite Q5 in KV.
  unfold AHK. rewrite Q1, Q2, Q3, Q4, Q5.
  split; [exact RP|]. split; [exact WF'|]. split; [exact K'|]. split; [exact KV|]. split; [exact RO|]. split; [exact QB|]. split; [exact DI|]. split; [exact BI|].
  split; [exact BM|].
  split. { eapply FSRep_agree; [| exact Hfs]. intros x Hx. apply AG. left. exact Hx. }
  split. { eapply icp_globals_agree; [exact Hicp|]. intros x Hx. apply AG. right; left. exact Hx. }
  split. { eapply ay_statics_agree; [exact Hyst|]. intros x Hx. apply AG. do 2 right; left. exact Hx. }
  split. { eapply low_shadow_agree; [exact Hlow|]. intros x Hx. apply AG. do 4 right; left. exact Hx. }
  split. { eapply RTMisc_agree; [exact Hrt|]. intros x Hx. apply AG. do 5 right; left. exact Hx. }
  split. { eapply StdioRep_agree; [exact Hso|]. intros x Hx. apply AG. do 6 right. exact Hx. }
  destruct TOK' as ((L & KM1 & KM2) & OS & _ & LIM & _).
  split; [split; [exact KM2| split; [exact KM1| exact LIM]]|].
  split; [exact L|].
  split. { unfold BUDGET, ACC in *. rewrite Q5. destruct Hbud as (B0 & B1 & B2 & B3). clear -B0 B1 B2 B3 C0 C1 C2 ACC'. lia. }
  split; [exact MI'|].
  split. { unfold ENVOK. rewrite Q1, Q2. unfold ENVOK in Henv. rewrite ?EE, ?EFS in Henv. exact Henv. }
  split. { eapply ay_cells_agree; [exact Hycl|]. intros x Hx. apply AG. do 3 right; left. exact Hx. }
  split; [exact SS| exact CS].
Qed.

End Balloc.
End RC__1.
