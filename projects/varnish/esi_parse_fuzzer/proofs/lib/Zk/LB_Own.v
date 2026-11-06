(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Monad MSafe STree Malloc Mall7vg MProg KInv KNodes RzImpl KLink KLinkC.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.Prelim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Monad OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Ext MI_Cnt MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_T80p LB_Inv LB_Sum LB_Ljn7 LB_Bound LB_Tree LB_StmtA LB_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Ctrl.

Module LB_KRoom.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import AgentLib RelSpec MmapSim AllocSim RefNodes BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Monad MSafe STree Malloc MProg KInv KNodes KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Tree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.Prelim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Monad OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree.KRoom.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MI_Inv LB_Inv LB_Sum LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition esz (e : word * word) : Z := bv_unsigned (snd e).

Lemma live_bytes_zsum : forall l, live_bytes l = zsum (map esz l).
Proof. induction l as [|[a n] l IH]; [reflexivity|]. rewrite live_bytes_cons. cbn [map]. rewrite zsum_cons, IH. reflexivity. Qed.

Lemma live_bytes_filter_split (f : word * word -> bool) l :
  live_bytes l = live_bytes (List.filter f l) + live_bytes (List.filter (fun x => negb (f x)) l).
Proof.
  induction l as [|[a n] l IH]; [reflexivity|]. cbn [List.filter]. rewrite live_bytes_cons.
  destruct (f (a, n)); cbn [negb]; rewrite live_bytes_cons; lia.
Qed.

Lemma pwdisj_filter f l : pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction 1 as [|e l Hd Hl IH]; cbn [List.filter]; [constructor|].
  destruct (f e); [| exact IH]. constructor; [| exact IH]. intros e' He'. apply filter_In in He' as [He' _]. exact (Hd e' He').
Qed.

Lemma filter_length_le {A} (f : A -> bool) l : (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma esz_elo_ehi e : esz e = ehi e - elo e.
Proof. unfold esz, ehi, elo. lia. Qed.

(* [comment removed for export] *)
Lemma disj_window_bytes : forall (k : nat) (l : list (word * word)) lo hi,
  (length l <= k)%nat -> pwdisj l -> (forall e, In e l -> elo e < ehi e) ->
  (forall e, In e l -> lo <= elo e /\ ehi e <= hi) -> lo <= hi -> live_bytes l <= hi - lo.
Proof.
  induction k as [|k IH]; intros l lo hi Hlen HP HN HW Hlh.
  - destruct l; [cbn; lia| cbn in Hlen; lia].
  - destruct l as [|[ea en] t]; [cbn; lia|]. inversion HP as [|e0 t0 Hd Ht]; subst.
    set (e := (ea, en)) in *.
    set (f := fun x : word * word => ehi x <=? elo e).
    rewrite live_bytes_cons.
    pose proof (HN e (or_introl eq_refl)) as Ne. pose proof (HW e (or_introl eq_refl)) as [We1 We2].
    rewrite (live_bytes_filter_split f t).
    assert (B1 : live_bytes (List.filter f t) <= elo e - lo).
    { apply (IH _ lo (elo e)).
      - pose proof (filter_length_le f t). cbn in Hlen. lia.
      - apply pwdisj_filter. exact Ht.
      - intros x Hx. apply filter_In in Hx as [Hx _]. apply HN. right. exact Hx.
      - intros x Hx. apply filter_In in Hx as [Hx Fx]. unfold f in Fx. apply Z.leb_le in Fx. split; [exact (proj1 (HW x (or_intror Hx)))| exact Fx].
      - lia. }
    assert (B2 : live_bytes (List.filter (fun x => negb (f x)) t) <= hi - ehi e).
    { apply (IH _ (ehi e) hi).
      - pose proof (filter_length_le (fun x => negb (f x)) t). cbn in Hlen. lia.
      - apply pwdisj_filter. exact Ht.
      - intros x Hx. apply filter_In in Hx as [Hx _]. apply HN. right. exact Hx.
      - intros x Hx. apply filter_In in Hx as [Hx Fx]. unfold f in Fx. apply negb_true_iff in Fx. apply Z.leb_gt in Fx.
        split; [destruct (Hd x Hx) as [D|D]; [exact D| lia]| exact (proj2 (HW x (or_intror Hx)))].
      - lia. }
    pose proof (esz_elo_ehi e) as Ee. unfold esz, e in Ee. cbn [snd] in Ee. fold e in Ee. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Lemma KL_brk_extent L pbrk mo : KL L pbrk mo ->
  brk_extent L <= BB L + 2 * PGSZ /\ 0 <= BB L /\ BB L mod PGSZ = 0 /\ 0 <= brk_extent L.
Proof.
  intros HK. unfold brk_extent, BB.
  destruct (ld_brkreg L) as [[b l]|] eqn:ER.
  - destruct (kl_brkreg _ _ _ HK b l ER) as (_ & _ & L2 & LM & _).
    destruct (ld_brk L) eqn:EP; unfold PGSZ in *; try (split; [lia| split; [lia| split; [exact LM| lia]]]).
    (* [comment removed for export] *)
    pose proof (kl_phase _ _ _ HK) as P. rewrite EP in P. destruct P as (_ & _ & _ & NR & _). congruence.
  - destruct (ld_brk L); unfold PGSZ; split; try lia; split; try lia; split; try lia; reflexivity.
Qed.

Theorem KL_maps_count L pbrk mo : KL L pbrk mo -> Z.of_nat (length (vm_maps (m_vmmaps mo))) <= kcnt L + 2.
Proof.
  intros HK. destruct (KL_brk_extent L pbrk mo HK) as (BE & B0 & BM & _).
  pose proof (Z.div_mod (BB L) PGSZ ltac:(unfold PGSZ; lia)) as DM. rewrite BM, Z.add_0_r in DM.
  assert (D0 : 0 <= BB L / PGSZ) by (apply Z.div_pos; unfold PGSZ; lia).
  pose proof (maps_len_bound L pbrk mo (Z.to_nat (BB L / PGSZ + 2)) HK ltac:(rewrite Z2Nat.id by lia; unfold PGSZ in *; lia)) as LEN.
  unfold kcnt. lia.
Qed.

(* [comment removed for export] *)
Lemma went_Z b n : 0 <= b < 2^64 -> 0 <= n < 2^64 -> elo (went b n) = b /\ esz (went b n) = n.
Proof. intros Hb Hn. unfold elo, esz, went, wz. cbn [fst snd]. rewrite !u64_lit by lia. auto. Qed.

Definition ledger_pairs (L : mled) : list (Z * Z) :=
  map (fun g : Z * Z => (fst g, mmap_len (snd g))) (ld_groups L)
  ++ map (fun m : Z * Z * Z => (fst (fst m), mmap_len (snd (fst m)))) (ld_metas L).

Lemma ledger_pairs_sum L : zsum (map snd (ledger_pairs L)) = gm L.
Proof.
  unfold ledger_pairs, gm. rewrite map_app, zsum_app, !map_map. cbn [snd]. reflexivity.
Qed.

Theorem KL_live_bytes L pbrk mo : KL L pbrk mo -> vm_live_bytes (m_vmmaps mo) <= gm L + BB L + 2 * PGSZ.
Proof.
  intros HK. destruct (KL_brk_extent L pbrk mo HK) as (BE & B0 & _ & E0).
  set (maps := vm_maps (m_vmmaps mo)). unfold vm_live_bytes. fold maps.
  pose proof (kl_wf _ _ _ HK) as [NE PW]. fold maps in NE, PW.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kl_brkb _ _ _ HK) as KB.
  set (start := bv_unsigned (vm_start_brk (m_vmmaps mo))) in *.
  set (ext := brk_extent L) in *.
  set (inbrk := fun e : word * word => (start <=? elo e) && (ehi e <=? start + ext)).
  rewrite (live_bytes_filter_split inbrk maps).
  (* [comment removed for export] *)
  assert (P1 : live_bytes (List.filter inbrk maps) <= ext).
  { replace ext with ((start + ext) - start) by lia.
    apply (disj_window_bytes (length (List.filter inbrk maps))); [lia| apply pwdisj_filter; exact PW| | |].
    - intros e He. apply filter_In in He as [He _]. exact (proj1 (NE e He)).
    - intros e He. apply filter_In in He as [_ Fe]. unfold inbrk in Fe. apply andb_prop in Fe as [F1 F2].
      apply Z.leb_le in F1. apply Z.leb_le in F2. auto.
    - subst ext. lia. }
  (* [comment removed for export] *)
  assert (P2 : live_bytes (List.filter (fun x => negb (inbrk x)) maps) <= gm L).
  { rewrite live_bytes_zsum, <- ledger_pairs_sum.
    apply (zsum_inj_le (fun x y : Z * Z => decide (x = y)) esz snd (fun e => (elo e, esz e))).
    - (* [comment removed for export] *)
      assert (ND : NoDup (map elo (List.filter (fun x => negb (inbrk x)) maps))).
      { apply pwdisj_nodup_elo; [apply pwdisj_filter; exact PW|]. intros e He. apply filter_In in He as [He _]. exact (proj1 (NE e He)). }
      apply NoDup_ListNoDup in ND. exact (List.NoDup_map_inv _ _ ND).
    - intros e He. apply filter_In in He as [He Fe]. apply negb_true_iff in Fe. cbn [snd]. split; [| lia].
      pose proof alloc_ceiling_lt as ACL.
      destruct (kl_complete _ _ _ HK e He) as [(b & l & Hin & ->)|[(b & l & k & Hin & ->)|(X1 & X2 & X3 & X4)]].
      + destruct (kl_groups _ _ _ HK b l Hin) as (G1 & G2 & _ & G4 & _). pose proof (mmap_len_ge l ltac:(lia)) as ML.
        destruct (went_Z b (mmap_len l) ltac:(lia) ltac:(lia)) as [-> ->].
        unfold ledger_pairs. apply in_or_app. left. apply in_map_iff. exists (b, l). auto.
      + destruct (kl_metas _ _ _ HK b l k Hin) as (G1 & G2 & _ & G4 & _). pose proof (mmap_len_ge l ltac:(lia)) as ML.
        destruct (went_Z b (mmap_len l) ltac:(lia) ltac:(lia)) as [-> ->].
        unfold ledger_pairs. apply in_or_app. right. apply in_map_iff. exists (b, l, k). auto.
      + exfalso. unfold inbrk in Fe. fold start in X1. apply andb_false_iff in Fe as [Fe|Fe]; [apply Z.leb_gt in Fe| apply Z.leb_gt in Fe]; subst ext; lia.
    - intros x y _ _ E. injection E as E1 E2. destruct x as [xa xn], y as [ya yn]. unfold elo, esz in E1, E2. cbn [fst snd] in E1, E2.
      apply bv_eq in E1. apply bv_eq in E2. subst. reflexivity.
    - intros [b n] Hy. cbn [snd]. unfold ledger_pairs in Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_map_iff in Hy as (x & E & Hx); injection E as _ <-.
      + destruct x as [xb xl]. destruct (kl_groups _ _ _ HK xb xl Hx) as (G1 & _). pose proof (mmap_len_ge xl ltac:(lia)). cbn [snd]. lia.
      + destruct x as [[xb xl] xk]. destruct (kl_metas _ _ _ HK xb xl xk Hx) as (G1 & _). pose proof (mmap_len_ge xl ltac:(lia)). cbn [fst snd]. lia. }
  subst ext. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RVK : Z := 16.
Definition RVS : Z := 2 ^ 24.
Definition resv_small (rv : list (Z * Z)) : Prop :=
  Z.of_nat (length rv) <= RVK /\ zsum (map snd rv) <= RVS.

Lemma resv_of_KL L pbrk mo : KL L pbrk mo -> resv_small (ld_resv L) ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo))) <= RVK /\ live_bytes (vm_reserved (m_vmmaps mo)) <= RVS.
Proof.
  intros HK [R1 R2]. rewrite (kl_resv _ _ _ HK) in R1, R2. rewrite length_map in R1. split; [exact R1|].
  rewrite live_bytes_zsum. rewrite map_map in R2. exact R2.
Qed.

(* [comment removed for export] *)
Lemma KL_gap L pbrk mo B nZ :
  KL L pbrk mo -> resv_small (ld_resv L) -> gm L + BB L <= B -> B <= BCAP -> kcnt L + 3 <= KCAP ->
  0 <= nZ <= B + 3 * PGSZ ->
  vm_gap_available (m_vmmaps mo) nZ = true.
Proof.
  intros HK HR HB HBC HKC HnZ. set (h := m_vmmaps mo).
  destruct (resv_of_KL L pbrk mo HK HR) as [RC RS]. fold h in RC, RS.
  pose proof (KL_maps_count L pbrk mo HK) as MC. pose proof (KL_live_bytes L pbrk mo HK) as MB. fold h in MC, MB. unfold vm_live_bytes in MB.
  pose proof (kl_ceil _ _ _ HK) as KC. unfold ceil_ok in KC. fold h in KC. pose proof alloc_ceiling_val as ACV.
  apply (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Gap04.vm_gap_available_of_bounds h nZ (RVK + KCAP) (RVS + BCAP + 2 * PGSZ)); [lia| | |].
  - rewrite length_app, Nat2Z.inj_add. lia.
  - rewrite OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Gap04.zsumf_esz_live, live_bytes_app. lia.
  - rewrite KC. unfold RVK, RVS, KCAP, BCAP, PGSZ in *.
    assert (P : (16 + 12288) * (nZ + 4095) <= (16 + 12288) * (2 ^ 32 + 3 * 4096 + 4095)) by (apply Z.mul_le_mono_nonneg_l; lia).
    lia.
Qed.

(* [comment removed for export] *)
Lemma KL_budget L pbrk mo B nZ :
  KL L pbrk mo -> gm L + BB L <= B -> B <= BCAP -> 0 <= nZ <= B + 3 * PGSZ ->
  (bw_on = true -> vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo)) ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros HK HB HBC HnZ HG. destruct bw_on eqn:EW; [exact (HG eq_refl)|].
  pose proof (KL_live_bytes L pbrk mo HK) as MB.
  pose proof (vm_backing_used_le_live mo (kl_minv _ _ _ HK) (kl_mat _ _ _ HK)) as BU.
  pose proof (bw_limit_off _ EW (kl_limit _ _ _ HK)) as KLim. unfold State.source_alloc_limit in KLim. unfold BCAP, PGSZ in *. lia.
Qed.

Theorem KL_mmap_nf L pbrk mo B len prot :
  KL L pbrk mo -> resv_small (ld_resv L) -> gm L + BB L <= B -> B <= BCAP -> kcnt L + 3 <= KCAP ->
  0 < len < LEN_MAX -> mmap_len len <= B + 3 * PGSZ -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  bw_gate_n (NMmap 0 len prot MAPF) mo ->
  nrefusable (NMmap 0 len prot MAPF) mo = false.
Proof.
  intros HK HR HB HBC HKC Hlen Hmax Hprot HG.
  destruct (rlen_mmap_len len Hlen) as [E1 E2].
  pose proof (KL_gap L pbrk mo B (mmap_len len) HK HR HB HBC HKC ltac:(lia)) as GAP.
  cbn -[rlen Z.eqb]. rewrite MAPF_eq, Z.eqb_refl. destruct Hprot as [-> | ->].
  - change (PROT_NONE =? NPROT_RW) with false. cbv iota. rewrite E1. apply OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Gap04.mmap_reserve_not_refusable. exact GAP.
  - change (PROT_RW =? NPROT_RW) with true. cbv iota. unfold grant_refusable. rewrite E1.
    apply OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Gap04.mmap_grant_not_refusable; [exact GAP|]. apply (KL_budget L pbrk mo B (mmap_len len) HK HB HBC ltac:(lia)).
    intros EW. rewrite <- E1. apply Z.leb_le. apply (bw_gate_n_mmap_rw 0 len mo EW); [| exact HG].
    unfold LEN_MAX in Hlen. intros E0. apply (f_equal bv_unsigned) in E0. unfold w in E0. rewrite !u64_lit in E0 by lia. lia.
Qed.

Theorem KL_mprotect_nf_B L pbrk mo B a len prot :
  KL L pbrk mo -> gm L + BB L <= B -> B <= BCAP ->
  nsafe (NMprotect a len prot) mo -> bw_gate_n (NMprotect a len prot) mo ->
  nrefusable (NMprotect a len prot) mo = false.
Proof.
  intros HK HB HBC HS HG. destruct bw_on eqn:EW.
  - (* [comment removed for export] *)
    pose proof HS as HS'. cbn [nsafe] in HS'. destruct HS' as (-> & _).
    cbn [nrefusable]. apply mprotect_not_refusable. exact (bw_gate_n_mprotect a len mo EW HS HG).
  - apply (KL_mprotect_nf L pbrk mo a len prot HK).
    pose proof (KL_live_bytes L pbrk mo HK) as MB. pose proof (bw_limit_off _ EW (kl_limit _ _ _ HK)) as KLim.
    unfold State.source_alloc_limit in KLim. unfold BCAP, PGSZ in *. lia.
Qed.

End CEIL.
End LB_KRoom.


Module LB_KLink.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Monad MSafe STree Malloc Mall7vg MProg KInv KNodes RzImpl KLink KLinkC.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.Prelim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Monad OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Sim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_T80p LB_Inv LB_Sum LB_Ljn7 LB_Bound LB_Tree LB_StmtA LB_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Ctrl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_StmtA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.LB_Grant OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ctrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Own.LB_KRoom.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twp {BW : BWorld} {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => forall eff mo', nsafe n mo -> nstep n mo eff mo' -> bw_gate_n n mo -> twp (k eff) mo' P
      (* [comment removed for export] *)
  end.

Lemma twp_mono {BW : BWorld} {R} (t : itree node R) : forall mo (P P' : R -> Model -> Prop),
  twp t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twp t mo P'.
Proof. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *; [auto|]. intros eff mo' Hs Hst Hg. eapply IH; eauto. Qed.

Lemma twp_bind {BW : BWorld} {A B} (t : itree node A) (f : A -> itree node B) : forall mo (P : B -> Model -> Prop),
  twp t mo (fun a mo1 => twp (f a) mo1 P) -> twp (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.bind node t f) mo P.
Proof. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|]. intros eff mo' Hs Hst Hg. apply IH. exact (H eff mo' Hs Hst Hg). Qed.

Lemma twp_true {BW : BWorld} {R} (t : itree node R) : forall mo, twp t mo (fun _ _ => True).
Proof. induction t as [r|n k IH]; intros mo; cbn; [exact I|]. intros eff mo' _ _ _. apply IH. Qed.

Lemma twf_twp_and {BW : BWorld} {R} (t : itree node R) : forall mo (P Q : R -> Model -> Prop),
  twf t mo P -> twp t mo Q -> twf t mo (fun r mo1 => P r mo1 /\ Q r mo1).
Proof.
  induction t as [r|n k IH]; intros mo P Q HF HW; cbn in *; [auto|].
  destruct HF as [Hs Hk]. split; [exact Hs|]. intros eff mo' Hst Hg. apply IH; [exact (Hk eff mo' Hst Hg)| exact (HW eff mo' Hs Hst Hg)].
Qed.

Definition etwp {BW : BWorld} {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twp t mo (fun r mo1 => match r with Unr => True | Ok a => Q a mo1 end).

Lemma etwf_etwp_and {BW : BWorld} {A} (t : itree node (exc A)) mo (P Q : A -> Model -> Prop) :
  etwf t mo P -> etwp t mo Q -> etwf t mo (fun a mo1 => P a mo1 /\ Q a mo1).
Proof.
  intros HF HW. unfold etwf, etwp in *. eapply twf_mono; [exact (twf_twp_and t mo _ _ HF HW)|].
  intros [|a] mo1 [H1 H2]; cbn in *; auto.
Qed.

Section WSpec.
Context {BW : BWorld}.
Context {St : Type}.

Definition wspec {A} (P : assn St) (m : Monad.M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwp (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_wspec_and {A} (P : assn St) (m : Monad.M St A) (Q1 Q2 : A -> assn St) :
  mspec P m Q1 -> wspec P m Q2 -> mspec P m (fun a s mo => Q1 a s mo /\ Q2 a s mo).
Proof. intros H1 H2 s mo HP. exact (etwf_etwp_and _ _ _ _ (H1 s mo HP) (H2 s mo HP)). Qed.

(* [comment removed for export] *)

Lemma wspec_triv {A} (P : assn St) (m : Monad.M St A) (Q : A -> assn St) : (forall a s mo, Q a s mo) -> wspec P m Q.
Proof. intros HQ s mo _. unfold etwp. eapply twp_mono; [apply twp_true|]. intros [|[a s1]] mo1 _; cbn; [exact I| apply HQ]. Qed.

Lemma wspec_conseq {A} (m : Monad.M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  wspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> wspec P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. unfold etwp. eapply twp_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [|[a s1]] mo1; cbn; auto.
Qed.

Lemma wspec_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> wspec P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma wspec_bind {A B} (m : Monad.M St A) (f : A -> Monad.M St B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
  wspec P m Q1 -> (forall a, wspec (Q1 a) (f a) Q) -> wspec P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind, etwp, ebind. apply twp_bind.
  eapply twp_mono; [exact (Hm s mo HP)|]. intros [|[a s1]] mo1 H1; cbn in *; [exact I|]. exact (Hf a s1 mo1 H1).
Qed.

Lemma wspec_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> forall rsp mo', nsafe n mo -> nstep n mo rsp mo' -> bw_gate_n n mo ->
     match dec rsp with Some a => Q a s mo' | None => True end) ->
  wspec P (msys n dec) Q.
Proof.
  intros H s mo HP. unfold msys, enode, etwp. cbn. intros rsp mo' Hs Hst Hg. specialize (H s mo HP rsp mo' Hs Hst Hg).
  destruct (dec rsp) as [a|]; cbn; [exact H| exact I].
Qed.

End WSpec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.

Lemma gcls_fixed a l p z : gcls (EMmap a l p MAPFX) z.
Proof. cbn. intros H. exfalso. revert H. vm_compute. discriminate. Qed.

Lemma addr_ok_not_err len a : 0 < len -> mmap_addr_ok len [] a = true -> is_err a = false.
Proof.
  intros Hlen H. unfold mmap_addr_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H3]. apply andb_prop in H as [_ H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. pose proof alloc_ceiling_lt. pose proof (mmap_len_ge len Hlen).
  unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem ev_step_gq L e s0 B :
  event_pre L e -> BOUNDX L e B -> B <= BCAP -> resv_small (ld_resv L) ->
  wspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo) (ev_step e) (fun z _ _ => gcls e z).
Proof.
  intros Hpre [HB HX] HBC HR.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - (* [comment removed for export] *) apply wspec_triv. intros; exact I.
  - (* [comment removed for export] *)
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    2:{ apply wspec_triv. intros; apply gcls_fixed. }
    pose proof (BOUND_mmap_now L len prot B HB) as HNOW.
    cbn [XB] in HX. change (Z.land MAPF MAP_FIXED =? 0) with true in HX. cbv iota in HX. destruct HX as [HX1 HX2].
    assert (NF : forall s mo, s = s0 /\ KL L (ps_brk s) mo -> bw_gate_n (NMmap 0 len prot MAPF) mo ->
                 nrefusable (NMmap 0 len prot MAPF) mo = false /\ ceil_ok mo).
    { intros s mo [-> HK] HG. split; [exact (KL_mmap_nf L _ mo B len prot HK HR HNOW HBC HX2 Hlen HX1 Hprot HG)| exact (kl_ceil _ _ _ HK)]. }
    unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
    assert (L63 : 0 < len < 2 ^ 63) by (unfold LEN_MAX in Hlen; lia).
    destruct Hprot as [-> | ->].
    + change (PROT_NONE =? 0) with true. cbv iota.
      eapply wspec_bind with (Q1 := fun x _ _ => exists a, x = MmOk a /\ mmap_addr_ok len [] a = true).
      * apply wspec_sys. intros s mo HP rsp mo' _ Hst HG. destruct (NF s mo HP HG) as [NR CE].
        destruct (nstep_dec_mmap_gen_nf len mo rsp mo' true L63 CE NR Hst) as (_ & a & Hd & Hok & _). cbv iota in Hd. rewrite Hd. eauto.
      * intros x. apply wspec_ret. intros s mo (a & -> & Hok). cbn. intros _. exact (addr_ok_not_err len a ltac:(lia) Hok).
    + change (PROT_RW =? 0) with false. cbv iota.
      eapply wspec_bind with (Q1 := fun x _ _ => exists a, x = MmOk a /\ mmap_addr_ok len [] a = true).
      * apply wspec_sys. intros s mo HP rsp mo' _ Hst HG. destruct (NF s mo HP HG) as [NR CE].
        destruct (nstep_dec_mmap_gen_nf len mo rsp mo' false L63 CE NR Hst) as (_ & a & Hd & Hok & _). cbv iota in Hd. rewrite Hd. eauto.
      * intros x. apply wspec_ret. intros s mo (a & -> & Hok). cbn. intros _. exact (addr_ok_not_err len a ltac:(lia) Hok).
  - (* [comment removed for export] *) apply wspec_triv. intros; exact I.
  - (* [comment removed for export] *)
    destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk).
    assert (HNOW : gm L + BB L <= B).
    { specialize (HB (TWO64 - ENOMEM) eq_refl). exact HB. }
    unfold ev_step.
    eapply wspec_bind with (Q1 := fun x _ _ => x = RgDone true).
    + apply wspec_sys. intros s mo [-> HK] rsp mo' HSAFE Hst HG.
      pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & _).
      rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk. pose proof alloc_ceiling_lt as Hcl.
      assert (MP : mmap_len PGSZ = PGSZ) by (apply mmap_len_of_aligned; unfold PGSZ; [lia| reflexivity]).
      destruct (nstep_dec_mprotect_nf (b + (1 + k) * PGSZ) PGSZ mo rsp mo' ltac:(unfold PGSZ in *; nia) ltac:(unfold PGSZ; lia)
                  ltac:(rewrite MP; unfold PGSZ in *; nia) (KL_mprotect_nf_B L _ mo B _ _ _ HK HNOW HBC HSAFE HG) Hst) as (_ & Hd & _).
      unfold dec_mprotect_rw. rewrite Hd. reflexivity.
    + intros x. apply wspec_ret. intros s mo ->. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Corollary ev_step_specQ L e (G : PState -> Model -> Prop) s0 B :
  gframe G -> event_pre L e -> BOUNDX L e B -> B <= BCAP -> resv_small (ld_resv L) ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step e)
        (fun z s mo => ev_step_post L e G s0 z s mo /\ gcls e z).
Proof.
  intros HG Hpre HBX HBC HR. apply mspec_wspec_and; [exact (ev_step_spec L e G s0 HG Hpre)|].
  eapply wspec_conseq; [exact (ev_step_gq L e s0 B Hpre HBX HBC HR)| intros s mo (E & HK & _); auto| auto].
Qed.

Lemma event_post_resv L e z : ld_resv (event_post L e z) = ld_resv L.
Proof.
  destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

(* [comment removed for export] *)
Theorem membed_specQ {R} B : B <= BCAP -> forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  gframe G -> qtree B L t Post -> resv_small (ld_resv L) ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ spath (C:=gcls) t r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  intros HBC t. induction t as [r|e k IH]; intros Post G L s0 HG Hq HR.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs). exists L.
    split; [constructor|]. split; [constructor|]. cbn in Hq. splits; auto.
  - cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HBX & Hk).
    eapply mspec_bind; [apply (ev_step_specQ L e G s0 B HG Hpre HBX HBC HR)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 ((Hans & HK1 & HG1 & Hm & Hfa & Hso) & Hg).
    eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans)); rewrite event_post_resv; exact HR| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & Hsp & HP & HK & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      split; [econstructor; eauto|]. splits; auto; congruence.
Qed.

End CEIL.
End LB_KLink.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Bound OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_StmtA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.LB_Grant OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ctrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Own.LB_KRoom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Own.LB_KLink.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Local Open Scope mspec_scope.

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition OWNQ (X : list (bptr * Z)) (G : PState -> Model -> Prop) : assn PState := fun s mo =>
  (exists st L BL LS, strip st = ps_m s /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL
      /\ SINV x0 st BL /\ AQ st BL PN /\ KL L (ps_brk s) mo /\ resv_small (ld_resv L)
      /\ Permutation (map xs X) (map bs BL))
  /\ G s mo.

Lemma OWNQ_intro X G s mo st L BL LS :
  strip st = ps_m s -> INVL x0 st L BL LS -> ld_live L = map bslot BL -> SINV x0 st BL -> AQ st BL PN ->
  KL L (ps_brk s) mo -> resv_small (ld_resv L) -> Permutation (map xs X) (map bs BL) -> G s mo -> OWNQ X G s mo.
Proof. intros. split; [exists st, L, BL, LS; repeat (split; [assumption|]); assumption| assumption]. Qed.

Lemma map_fst_xs (X : list (bptr * Z)) : map fst (map xs X) = map fst (map fst X).
Proof. rewrite !map_map. reflexivity. Qed.
Lemma map_fst_bs BL : map fst (map bs BL) = map bslot BL.
Proof. rewrite map_map. reflexivity. Qed.

Theorem OWNQ_OWN X G s mo : OWNQ X G s mo -> OWN (map fst X) G s mo.
Proof.
  intros [(st & L & BL & LS & E & INV & LIVE & SI & HAQ & HK & HR & HP) HG].
  assert (PS : Permutation (map fst (map fst X)) (map bslot BL)).
  { rewrite <- map_fst_xs, <- map_fst_bs. apply Permutation_map. exact HP. }
  split; [| split; [| exact HG]].
  - exists L. split; [exists st, BL, LS; auto|]. split; [exact HK|]. rewrite LIVE. intros c Hc. eapply Permutation_in; [exact PS| exact Hc].
  - eapply Permutation_NoDup; [apply Permutation_sym; exact PS|].
    apply NoDup_ListNoDup. exact (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))).
Qed.

(* [comment removed for export] *)
Definition QV (cs : mstate) (BL0 : list blk) : Prop := SINV x0 cs BL0 /\ AQ cs BL0 PN.

Lemma ctrl_eq_strip st : ctrl_eq st (strip st).
Proof. constructor; reflexivity. Qed.
Lemma ctrl_eq_sym' st st' : ctrl_eq st st' -> ctrl_eq st' st.
Proof. intros [C1 C2 C3 C4 C5 C6 C7 C8 C9]. constructor; congruence. Qed.

Lemma QV_of_witness st BL BL0 : SINV x0 st BL -> AQ st BL PN -> Permutation (map bs BL) (map bs BL0) -> QV (strip st) BL0.
Proof.
  intros SI HAQ HP. split.
  - apply (SINV_ctrl x0 st (strip st)); [apply ctrl_eq_strip|]. exact (SINV_bs x0 st BL BL0 HP SI).
  - apply (AQ_ctrl st (strip st)); [apply ctrl_eq_strip|]. exact (AQ_bs st BL BL0 PN HP HAQ).
Qed.

Lemma QV_to_witness st BL BL0 : QV (strip st) BL0 -> Permutation (map bs BL0) (map bs BL) -> SINV x0 st BL /\ AQ st BL PN.
Proof.
  intros [SI HAQ] HP. split.
  - apply (SINV_ctrl x0 (strip st) st); [apply ctrl_eq_sym'; apply ctrl_eq_strip|]. exact (SINV_bs x0 _ BL0 BL HP SI).
  - apply (AQ_ctrl (strip st) st); [apply ctrl_eq_sym'; apply ctrl_eq_strip|]. exact (AQ_bs _ BL0 BL PN HP HAQ).
Qed.

Theorem OWNQ_QV X G s mo BL0 : OWNQ X G s mo -> Permutation (map xs X) (map bs BL0) -> QV (ps_m s) BL0.
Proof.
  intros [(st & L & BL & LS & E & INV & LIVE & SI & HAQ & HK & HR & HP) HG] HP0. rewrite <- E.
  apply (QV_of_witness st BL BL0 SI HAQ). etransitivity; [apply Permutation_sym; exact HP| exact HP0].
Qed.

Lemma OWNQ_perm X Y G s mo : Permutation X Y -> OWNQ X G s mo -> OWNQ Y G s mo.
Proof.
  intros HXY [(st & L & BL & LS & E & INV & LIVE & SI & HAQ & HK & HR & HP) HG]. split; [| exact HG].
  exists st, L, BL, LS. repeat (split; [assumption|]). etransitivity; [| exact HP]. apply Permutation_map. apply Permutation_sym. exact HXY.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cpath_resv' {R} L (t : stree ev Z R) L' r : cpath L t L' r -> ld_resv L' = ld_resv L.
Proof. intros H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_resv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma no_overflow_of_room n : 0 <= n -> bigb n <= BCAP + 3 * PGSZ -> size_overflows n = false.
Proof.
  intros Hn HB. unfold size_overflows. apply Z.leb_gt. unfold bigb in HB.
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [GE|LT]; [| unfold MMAP_THRESHOLD in *; lia].
  pose proof (bigmap_lower n). pose proof (round_up_pg_spec (n + IB + UNIT)) as [[H1 _] _].
  unfold BCAP, PGSZ, IB, UNIT in *. lia.
Qed.

Theorem raw_malloc_spec_q X G n : gframe G -> 0 <= n ->
  zlen X + 1 <= NLIVE_CAP -> PHI PN + R63X X + bigb n <= BCAP + 3 * PGSZ ->
  mspec (OWNQ X G) (raw_malloc n)
        (fun r s mo => exists p, r = Some p /\ OWNQ ((p, n) :: X) G s mo /\ n < 2 ^ 63).
Proof.
  intros HG Hn HCNT HBYTES. unfold raw_malloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(st & L & BL & LS & E & INV & LIVE & SI & HAQ & HK & HR & HP) HGs]].
  pose proof (R63X_eq _ _ HP) as R63E.
  assert (ZL : zlen BL = zlen X).
  { apply Permutation_length in HP. rewrite !length_map in HP. unfold zlen. lia. }
  assert (HROOM : ROOM BL PN n) by (apply ROOM_PN; lia).
  assert (HBB : PHI PN + R63 BL + bigb n <= BCAP + 3 * PGSZ) by lia.
  assert (HOV : size_overflows n = false).
  { apply no_overflow_of_room; [exact Hn|]. pose proof (R63X_nonneg X). pose proof PHI_PN. lia. }
  (* [comment removed for export] *)
  assert (QT : qtree BCAP L (cmalloc (ps_m s1) n) (fun _ _ => True)).
  { rewrite <- E. exact (cmalloc_qtree st L BL LS PN n BCAP INV SI HAQ Hn HROOM HBB). }
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_specQ BCAP (Z.le_refl _) (cmalloc (ps_m s1) n) (fun _ _ => True) G L s1 HG QT HR)|].
    intros s mo [-> ->]. auto. }
  intros [stc' rc]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & CP & SP & _ & HK' & HG' & Hm & Hfa & Hso).
  eapply mspec_seq with (R := fun s mo => s = set_m stc' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cmalloc_grant_some gcls_undef gcls_mmap_ok gcls_mprot_ok (ps_m s1) n HOV SP) as [c ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2). rewrite <- E in Hf, HL2.
  pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
  destruct (malloc_simQ pans0 pupd0 pans0_range st L BL LS PN n BCAP tt ans o' st' rf INV SI HAQ Hn HROOM HBB FF) as (rc2 & Hf2 & RES).
  rewrite Hf in Hf2. assert (Est : stc' = strip st') by congruence. assert (Erc : Some c = rc2) by congruence. subst rc2.
  rewrite HL2 in RES.
  destruct rf as [pf|]; [| exfalso; exact RES].
  destruct RES as (off & LS' & Epf & INV' & SI' & HAQ').
  pose proof (KLink.cpath_live _ _ _ _ CP) as Hlive. pose proof (cpath_resv' _ _ _ _ CP) as Hresv.
  exists (c, fresh_off stc' c n). split; [reflexivity|]. split.
  - apply (OWNQ_intro _ G _ mo2 st' (set_live (c :: ld_live L') L') (((c, off), n) :: BL) LS').
    + cbn [ps_m set_m]. symmetry. exact Est.
    + apply INVL_set_live. exact INV'.
    + cbn [ld_live set_live map bslot fst]. rewrite Hlive, LIVE. reflexivity.
    + exact SI'.
    + exact HAQ'.
    + cbn [ps_brk set_m]. apply KL_set_live. exact HK'.
    + cbn [ld_resv set_live]. rewrite Hresv. exact HR.
    + cbn [map xs bs fst snd]. unfold bs at 1. cbn [bslot bsize fst snd]. apply perm_skip. exact HP.
    + apply (HG s2 _ mo2 _); [reflexivity| reflexivity| apply vm_only_refl| exact HG'].
  - unfold size_overflows in HOV. apply Z.leb_gt in HOV. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem raw_free_spec_q X G p n : gframe G ->
  mspec (OWNQ ((p, n) :: X) G) (raw_free p) (fun _ => OWNQ X G).
Proof.
  intros HG. unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(st & L & BL & LS & E & INV & LIVE & SI & HAQ & HK & HR & HP) HGs]].
  assert (Hin : In (fst p, n) (map bs BL)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_map_iff in Hin as ([[c off] n'] & Ebs & Hk). unfold bs in Ebs. cbn in Ebs.
  assert (Ec : c = fst p) by congruence. assert (En : n' = n) by congruence. subst n'.
  assert (Hlive : In (fst p) (ld_live L)) by (rewrite LIVE, <- Ec; change c with (bslot ((c, off), n)); apply in_map; exact Hk).
  assert (SR : MI_Ccma.SIMREL (ps_m s1) L) by (exists st, BL, LS; auto).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cfree (ps_m s1) (Some (fst p))) _ G L s1 HG (MI_Ccma.cfree_contract_sim _ _ _ SR Hlive))|].
    intros s mo [-> ->]. auto. }
  intros stc'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & CP & _ & HK' & HG' & Hm & Hfa & Hso).
  apply mspec_upd'. intros s mo [-> ->].
  (* [comment removed for export] *)
  destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL2).
  rewrite <- E, <- Ec in Hf, HL2.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
  unfold FREL in SF. cbn in SF.
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (_ & _ & LIVE' & LS' & INV').
  destruct (free_simQ pans0 pupd0 pans0_range st L BL LS PN c off n tt ans o' st' INV SI HAQ Hk FF) as [SI' HAQ'].
  rewrite HL2 in INV', LIVE'.
  pose proof (cpath_resv' _ _ _ _ CP) as Hresv.
  apply (OWNQ_intro _ G _ mo2 st' (set_live (ap_remove c (ld_live L')) L') (bl_remove c BL) LS').
  - cbn [ps_m set_m]. exact SF.
  - apply INVL_set_live. exact INV'.
  - cbn [ld_live set_live]. rewrite LIVE', LIVE. symmetry. apply MI_Ccma.bl_remove_map.
  - exact SI'.
  - exact HAQ'.
  - cbn [ps_brk set_m]. apply KL_set_live. exact HK'.
  - cbn [ld_resv set_live]. rewrite Hresv. exact HR.
  - pose proof (bl_remove_perm ((c, off), n) BL Hk (INVL_nodup_slots _ _ _ _ _ INV)) as BP. cbn [bs bslot bsize fst snd] in BP.
    apply (Permutation_cons_inv (l:=map xs X) (a:=bs ((c, off), n))). etransitivity; [| exact BP]. etransitivity; [| exact HP].
    cbn [map xs fst snd]. unfold bs. cbn [bslot bsize fst snd]. rewrite Ec. apply Permutation_refl.
  - apply (HG s2 _ mo2 _); [reflexivity| reflexivity| apply vm_only_refl| exact HG'].
Qed.

End CEIL.
