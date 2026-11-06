(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhBrkK OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.MhDissolve OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_contains_In : forall l (a sz lo n : word),
  In (a, sz) l -> bv_unsigned a <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains l lo n = true.
Proof.
  intros l a sz lo n Hin H1 H2. unfold map_contains. apply existsb_exists. exists (a, sz). split; [exact Hin|].
  cbn [fst snd]. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma maps_subtract_flat_map : forall (A : Type) (f : A -> list (word * word)) (l : list A) lo hi,
  maps_subtract (flat_map f l) lo hi = flat_map (fun x => maps_subtract (f x) lo hi) l.
Proof. induction l as [|a l IH]; intros lo hi; cbn; [reflexivity|]. rewrite maps_subtract_app, IH. reflexivity. Qed.

Lemma perm_maps_subtract : forall l l' lo hi, Permutation l l' -> Permutation (maps_subtract l lo hi) (maps_subtract l' lo hi).
Proof.
  intros l l' lo hi P. induction P as [|[a n] l1 l2 P IH|[a n] [b k] l1|]; cbn.
  - constructor.
  - apply Permutation_app_head. exact IH.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - etransitivity; eassumption.
Qed.

Lemma flat_map_ext_In : forall (A B : Type) (f g : A -> list B) (l : list A),
  (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; intros H; cbn; [reflexivity|].
  rewrite (H a ltac:(left; reflexivity)), IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma count_kind_cons : forall (f : rkind -> bool) r l,
  length (List.filter (fun x => f (rg_kind x)) (r :: l)) = ((if f (rg_kind r) then 1 else 0) + length (List.filter (fun x => f (rg_kind x)) l))%nat.
Proof. intros f r l. cbn. destruct (f (rg_kind r)); reflexivity. Qed.

Lemma filter_all_false : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros A f l H. induction l as [|a l IH]; cbn; [reflexivity|].
  rewrite (H a ltac:(left; reflexivity)). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma region_eq_dec : forall r1 r2 : region, {r1 = r2} + {r1 <> r2}.
Proof.
  intros r1 r2. destruct (region_eqb r1 r2) eqn:E.
  - left. apply region_eqb_eq. exact E.
  - right. intros H. apply region_eqb_eq in H. rewrite H in E. discriminate E.
Qed.

Lemma count_perm : forall (A : Type) (f : A -> bool) (l l' : list A), Permutation l l' -> length (List.filter f l) = length (List.filter f l').
Proof. intros A f l l' P. apply Permutation_length. apply perm_filter. exact P. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Common.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  Hypothesis XOK : xok X.

  Lemma regions_rng : forall r, In r (s_regions st) ->
    HEAPLO <= rg_base r /\ rg_base r + rg_len r <= CEIL /\ rg_base r mod 4096 = 0 /\ 0 < rg_len r /\ rg_len r mod 4096 = 0.
  Proof. intros r Hr. exact (wr_rng st (WF_regions st L HWF) r Hr). Qed.

  Lemma region_in_maps : forall r, In r (s_regions st) -> In (region_entry r) (vm_maps vm).
  Proof.
    intros r Hr. apply (Permutation_in _ (Permutation_sym (lx_maps st X vm HLG))). apply in_app_iff. right. apply in_map. exact Hr.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_apart : forall a n, 0 <= a -> 0 < n -> a + n <= CEIL ->
    region_free (vm_reserved vm ++ vm_maps vm) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
    (forall r, In r (s_regions st) -> a + n <= rg_base r \/ rg_base r + rg_len r <= a) /\
    (forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en <= 2 ^ 35 /\ ea + en <= CEIL /\ ea mod 4096 = 0 /\
                         (a + n <= ea \/ ea + en <= a)).
  Proof.
    intros a n Ha Hn Hce RF. ceil. rewrite region_free_app in RF. apply andb_true_iff in RF. destruct RF as [_ RF].
    split.
    - intros r Hr. pose proof (region_free_In _ _ _ _ _ RF (region_in_maps r Hr)) as D.
      destruct (regions_rng r Hr) as (R1 & R2 & R3 & R4 & R5). ceil; unfold HEAPLO in R1, R2.
      cbn [region_entry] in D. rewrite !u64_lit in D by lia. exact D.
    - intros e He. destruct (XOK e He) as (ea & en & -> & E1 & E2 & E3 & E4). exists ea, en.
      assert (Hin : In (Z_to_bv 64 ea, Z_to_bv 64 en) (vm_maps vm)).
      { apply (Permutation_in _ (Permutation_sym (lx_maps st X vm HLG))). apply in_app_iff. left. exact He. }
      pose proof (region_free_In _ _ _ _ _ RF Hin) as D. ceil; unfold HEAPLO in *. rewrite !u64_lit in D by lia.
      repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma guard_inside : forall en, In en (match guard_noacc (s_brk st) with Some b0 => [(Z_to_bv 64 b0, Z_to_bv 64 4096)] | None => [] end) ->
    exists b0, en = (Z_to_bv 64 b0, Z_to_bv 64 4096) /\ In (RG b0 8192 RBrk) (s_regions st).
  Proof.
    intros en Hen. pose proof (wr_brk st (WF_regions st L HWF)) as RB.
    unfold guard_noacc, guard_kind in Hen.
    destruct (s_brk st) as [|b0 b1 [| |]|[[g [| |]]|]]; cbn in Hen; try (destruct Hen; fail); destruct Hen as [<-|[]].
    - exists b0. split; [reflexivity|]. destruct RB as (_ & _ & Hin). exact Hin.
    - exists g. split; [reflexivity|]. destruct RB as (_ & Hin). exact Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma nr_inside : forall r en, In r (s_regions st) -> In en (noacc_of_region r) ->
    exists x y, en = (Z_to_bv 64 x, Z_to_bv 64 y) /\ rg_base r <= x /\ 0 < y /\ x + y <= rg_base r + rg_len r /\ 0 <= x /\ x + y < 2 ^ 64.
  Proof.
    intros r en Hr Hen. destruct (regions_rng r Hr) as (R1 & R2 & R3 & R4 & R5). ceil; unfold HEAPLO in R1, R2.
    destruct r as [rb rl [|ex|y]]; cbn in Hen; [destruct Hen | | destruct Hen].
    destruct (wr_meta st (WF_regions st L HWF) rb rl ex Hr) as (E1 & E2 & E3). cbn in R1, R2, R3, R4, R5. cbn [rg_base rg_len].
    cbn [rg_base rg_len] in Hen. destruct (ex =? 0) eqn:EX0.
    { destruct Hen as [<-|[]]. exists rb, rl. split; [reflexivity|]. lia. }
    destruct Hen as [<-|Hen].
    - exists rb, 4096. split; [reflexivity|]. lia.
    - destruct (4096 * (1 + ex) <? rl) eqn:T; [|destruct Hen]. apply Z.ltb_lt in T. destruct Hen as [<-|[]].
      exists (rb + 4096 * (1 + ex)), (rl - 4096 * (1 + ex)). split; [reflexivity|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma nr_subtract_apart : forall r lo hi, In r (s_regions st) -> lo < hi ->
    (hi <= rg_base r \/ rg_base r + rg_len r <= lo) ->
    maps_subtract (noacc_of_region r) lo hi = noacc_of_region r.
  Proof.
    intros r lo hi Hr Hlh D. apply maps_subtract_apart; [exact Hlh|].
    intros en Hen. destruct (nr_inside r en Hr Hen) as (x & y & -> & A1 & A2 & A3 & A4 & A5).
    exists x, y. split; [reflexivity|]. destruct D; repeat split; lia.
  Qed.

  Lemma guard_subtract_apart : forall lo hi, lo < hi ->
    (forall b0, In (RG b0 8192 RBrk) (s_regions st) -> hi <= b0 \/ b0 + 8192 <= lo) ->
    maps_subtract (match guard_noacc (s_brk st) with Some b0 => [(Z_to_bv 64 b0, Z_to_bv 64 4096)] | None => [] end) lo hi
    = match guard_noacc (s_brk st) with Some b0 => [(Z_to_bv 64 b0, Z_to_bv 64 4096)] | None => [] end.
  Proof.
    intros lo hi Hlh D. apply maps_subtract_apart; [exact Hlh|].
    intros en Hen. destruct (guard_inside en Hen) as (b0 & -> & Hin).
    destruct (regions_rng _ Hin) as (R1 & R2 & _). cbn in R1, R2. ceil; unfold HEAPLO in R1, R2.
    exists b0, 4096. split; [reflexivity|]. destruct (D b0 Hin); repeat split; lia.
  Qed.
End Common.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section C1.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  Hypothesis Hfl : s_flist st = [].
  Hypothesis Hac0 : c_avail_cnt (s_ctx st) = 0.
  Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  #[local] Notation cx := (s_ctx st).
  #[local] Notation ac := (c_area_cnt (s_ctx st)).
  Hypothesis Hac : ac > 0.
  (* [comment removed for export] *)
  Variables (b len e : Z).
  Hypothesis HR : In (RG b len (RMeta e)) (s_regions st) /\ 0 <= e /\ c_cursor cx = b + 4096 * (1 + e) /\ c_cursor cx + 4096 * ac = b + len.

  Definition c1_p : Z := c_cursor cx.
  Definition c1_R : region := RG b len (RMeta e).
  Definition c1_R' : region := RG b len (RMeta (e + 1)).
  Definition c1_regions1 : list region := c1_R' :: rremove c1_R (s_regions st).
  Definition c1_st1 : mst := MhAMetaN.st' st c1_p c1_regions1 (s_brk st) (ac - 1) (c_shift cx) (c_brk cx).
  Definition c1_vm1 : VmMaps :=
    mkVmMapsFull (vm_reserved vm) (vm_maps vm) (maps_subtract (vm_noaccess vm) c1_p (c1_p + 4096))
                 (vm_start_brk vm) (vm_brk vm) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm).

  Lemma c1_R_in : In c1_R (s_regions st). Proof. exact (proj1 HR). Qed.
  Lemma c1_R_rng : HEAPLO <= b /\ b + len <= CEIL /\ b mod 4096 = 0 /\ 0 < len /\ len mod 4096 = 0.
  Proof. exact (regions_rng st L HWF c1_R c1_R_in). Qed.
  Lemma c1_R_meta : 0 <= e /\ 4096 * (1 + e) <= len /\ len <= 2 ^ 24.
  Proof. exact (wr_meta st (WF_regions st L HWF) b len e c1_R_in). Qed.
  Lemma c1_p_val : c1_p = b + 4096 * (1 + e) /\ c1_p + 4096 * ac = b + len.
  Proof. unfold c1_p. destruct HR as (_ & _ & A & B). lia. Qed.
  Lemma c1_Hp : c1_p mod 4096 = 0 /\ HEAPLO <= c1_p /\ c1_p + 4096 <= CEIL.
  Proof.
    pose proof c1_R_rng as (R1 & R2 & R3 & R4 & R5). pose proof c1_p_val as [P1 P2]. pose proof c1_R_meta as (E1 & _).
    split; [rewrite P1, Z.add_mod, R3, Z.mul_comm, Z.mod_mul by lia; reflexivity | lia].
  Qed.
  Lemma c1_p_in_R : b <= c1_p /\ c1_p + 4096 <= b + len.
  Proof. pose proof c1_p_val. pose proof c1_R_meta. lia. Qed.

  Lemma c1_other_apart : forall r, In r (s_regions st) -> r <> c1_R -> rg_base r + rg_len r <= b \/ b + len <= rg_base r.
  Proof. intros r Hr Hne. destruct (wr_disj st (WF_regions st L HWF) r c1_R Hr c1_R_in Hne); cbn in *; lia. Qed.

  Lemma c1_Hp_areas : forall a, In a (s_areas st) -> a + 4096 <= c1_p \/ c1_p + 4096 <= a.
  Proof.
    intros a Ha. pose proof c1_p_in_R as [P1 P2]. pose proof c1_p_val as [P3 P4].
    destruct (wa_inreg st (WF_areas st L HWF) a Ha) as [(b2 & l2 & Hin & A1 & A2 & _)|(b2 & l2 & e2 & Hin & A1 & A2)].
    - destruct (c1_other_apart _ Hin ltac:(intros E; discriminate E)); cbn in *; lia.
    - destruct (region_eq_dec (RG b2 l2 (RMeta e2)) c1_R) as [E|NE].
      + unfold c1_R in E. injection E. intros -> -> ->. left. lia.
      + destruct (c1_other_apart _ Hin NE); cbn in *; [left | right]; try lia.
        destruct (wr_meta st (WF_regions st L HWF) b2 l2 e2 Hin). lia.
  Qed.

  Lemma c1_Hp_groups : forall x, is_group st x -> gspan st x <= c1_p \/ c1_p + 4096 <= g_mem st x.
  Proof.
    intros x Hx. pose proof c1_p_in_R as [P1 P2].
    destruct (group_apart_region st L HWF x c1_R Hx c1_R_in ltac:(intros y E; discriminate E)); cbn in *; lia.
  Qed.

  Lemma c1_regions1_In : forall r, In r c1_regions1 <-> r = c1_R' \/ (In r (s_regions st) /\ r <> c1_R).
  Proof. intros r. unfold c1_regions1. cbn. rewrite rremove_In. split; intros [A|A]; auto. Qed.

  Lemma c1_HRgrp : forall b0 l0 x, In (RG b0 l0 (RGroup x)) c1_regions1 <-> In (RG b0 l0 (RGroup x)) (s_regions st).
  Proof.
    intros b0 l0 x. rewrite c1_regions1_In. split.
    - intros [E|[A _]]; [discriminate E | exact A].
    - intros A. right. split; [exact A | intros E; discriminate E].
  Qed.
  Lemma c1_HRsub : forall r, In r (s_regions st) -> exists r', In r' c1_regions1 /\ rg_base r' = rg_base r /\ rg_len r' = rg_len r.
  Proof.
    intros r Hr. destruct (region_eq_dec r c1_R) as [->|NE].
    - exists c1_R'. split; [apply c1_regions1_In; left; reflexivity | split; reflexivity].
    - exists r. split; [apply c1_regions1_In; right; split; assumption | split; reflexivity].
  Qed.
  Lemma c1_HRold : forall a, In a (s_areas st) -> INREG c1_regions1 (s_brk st) a.
  Proof.
    intros a Ha. pose proof c1_p_val as [P3 P4].
    destruct (wa_inreg st (WF_areas st L HWF) a Ha) as [(b2 & l2 & Hin & A1 & A2 & A3)|(b2 & l2 & e2 & Hin & A1 & A2)].
    - left. exists b2, l2. split; [apply c1_regions1_In; right; split; [exact Hin | intros E; discriminate E]|]. repeat split; assumption.
    - right. destruct (region_eq_dec (RG b2 l2 (RMeta e2)) c1_R) as [E|NE].
      + unfold c1_R in E. injection E. intros -> -> ->. exists b, len, (e + 1). split; [apply c1_regions1_In; left; reflexivity|]. lia.
      + exists b2, l2, e2. split; [apply c1_regions1_In; right; split; assumption|]. lia.
  Qed.
  Lemma c1_HRnew : INREG c1_regions1 (s_brk st) c1_p.
  Proof.
    right. exists b, len, (e + 1). pose proof c1_p_val as [P3 P4]. pose proof c1_R_meta as (E1 & _).
    split; [apply c1_regions1_In; left; reflexivity|]. lia.
  Qed.
  Lemma c1_Hcur' : ac - 1 > 0 -> exists b0 l0 e0, In (RG b0 l0 (RMeta e0)) c1_regions1 /\ 0 <= e0 /\
                   c1_p + 4096 = b0 + 4096 * (1 + e0) /\ c1_p + 4096 + 4096 * (ac - 1) = b0 + l0.
  Proof.
    intros Hg. exists b, len, (e + 1). pose proof c1_p_val as [P3 P4]. pose proof c1_R_meta as (E1 & _).
    split; [apply c1_regions1_In; left; reflexivity|]. lia.
  Qed.
  Lemma c1_Hsh' : 0 <= c_shift cx /\ c_shift cx <= Z.of_nat (length (s_areas st)) + 2 /\ (ac - 1 = 0 -> c_shift cx <= Z.of_nat (length (s_areas st)) + 1).
  Proof. pose proof (wc_shift st (WF_ctx st L HWF)). lia. Qed.
  Lemma c1_Hbrk' : match s_brk st with
                | BrkUntried => c_brk cx = 0
                | BrkLive b0 b1 _ => c_brk cx = b1 /\ b0 mod 4096 = 0 /\ b1 mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b1 /\ b1 <= CEIL
                | BrkDead _ => c_brk cx = 2 ^ 64 - 1
                end.
  Proof. exact (wc_brk st (WF_ctx st L HWF)). Qed.

  Lemma c1_R'_notin : ~ In c1_R' (s_regions st).
  Proof.
    intros Hin. pose proof c1_R_rng as (R1 & R2 & R3 & R4 & R5).
    destruct (c1_other_apart c1_R' Hin ltac:(unfold c1_R', c1_R; intros E; injection E; lia)); cbn in *; lia.
  Qed.
  Lemma c1_regions_perm : Permutation (s_regions st) (c1_R :: rremove c1_R (s_regions st)).
  Proof. apply rremove_perm; [exact (wr_nodup st (WF_regions st L HWF)) | exact c1_R_in]. Qed.

  Lemma c1_t_wf_regions : wf_regions c1_st1.
  Proof.
    pose proof c1_R_rng as (R1 & R2 & R3 & R4 & R5). pose proof c1_R_meta as (E1 & E2 & E3). pose proof c1_p_val as [P3 P4].
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; cbn [s_regions s_brk s_ctx c1_st1 MhAMetaN.st' MhAMetaN.cx' c_shift s_areas].
    - intros r Hr. apply c1_regions1_In in Hr. destruct Hr as [->|[Hr _]]; [cbn; exact c1_R_rng | exact (RNG r Hr)].
    - intros r1 r2 H1 H2 Hne. apply c1_regions1_In in H1. apply c1_regions1_In in H2.
      destruct H1 as [->|[H1 N1]]; destruct H2 as [->|[H2 N2]].
      + exfalso; exact (Hne eq_refl).
      + destruct (c1_other_apart r2 H2 N2); cbn; lia.
      + destruct (c1_other_apart r1 H1 N1); cbn; lia.
      + exact (DISJ r1 r2 H1 H2 Hne).
    - apply NoDup_ListNoDup. constructor.
      + intros Hin. apply rremove_In in Hin. exact (c1_R'_notin (proj1 Hin)).
      + apply NoDup_ListNoDup. unfold rremove. apply NoDup_ListNoDup. apply List.NoDup_filter. apply NoDup_ListNoDup. exact ND.
    - intros r Hr. apply c1_regions1_In in Hr. destruct Hr as [->|[Hr _]]; [cbn; lia | exact (LEN r Hr)].
    - intros b0 l0 x Hin. apply c1_HRgrp in Hin. rewrite (MhAMetaN.e_gsc st L HWF c1_p c1_regions1 (s_brk st) (ac - 1) (c_shift cx) (c_brk cx) c1_Hp c1_Hp_areas) by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (GB b0 l0 x Hin).
    - intros b0 l0 x Hin H63. apply c1_HRgrp in Hin.
      rewrite (MhAMetaN.e_gsc st L HWF c1_p c1_regions1 (s_brk st) (ac - 1) (c_shift cx) (c_brk cx) c1_Hp c1_Hp_areas) in H63 by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (G63 b0 l0 x Hin H63).
    - intros b0 l0 e0 Hin. apply c1_regions1_In in Hin. destruct Hin as [E|[Hin _]]; [|exact (MT b0 l0 e0 Hin)].
      unfold c1_R' in E. injection E. intros -> -> ->. lia.
    - rewrite (count_perm _ _ _ _ c1_regions_perm) in MC. unfold c1_regions1.
      rewrite (count_kind_cons (fun k => match k with RMeta _ => true | _ => false end) c1_R') .
      rewrite (count_kind_cons (fun k => match k with RMeta _ => true | _ => false end) c1_R) in MC. cbn [rg_kind c1_R c1_R'] in *. exact MC.
    - unfold MhAMetaN.areas'. rewrite length_app. cbn [length].
      assert (CB : length (List.filter (fun x => match rg_kind x with RBrk => true | _ => false end) c1_regions1)
                   = length (List.filter (fun x => match rg_kind x with RBrk => true | _ => false end) (s_regions st))).
      { rewrite (count_perm _ _ _ _ c1_regions_perm). unfold c1_regions1.
        rewrite (count_kind_cons (fun k => match k with RBrk => true | _ => false end) c1_R').
        rewrite (count_kind_cons (fun k => match k with RBrk => true | _ => false end) c1_R). reflexivity. }
      destruct (s_brk st) as [|b0 b1 gk|g].
      + intros b2 l2 Hin. apply c1_regions1_In in Hin. destruct Hin as [E|[Hin _]]; [discriminate E | exact (BRK b2 l2 Hin)].
      + destruct BRK as (B1 & B2 & B3). split; [|split].
        * intros b2 l2 Hin. apply c1_regions1_In in Hin. destruct Hin as [E|[Hin _]]; [discriminate E | exact (B1 b2 l2 Hin)].
        * rewrite CB. lia.
        * apply c1_regions1_In. right. split; [exact B3 | destruct gk; intros E; discriminate E].
      + destruct BRK as [B1 B2]. split; [rewrite CB; lia|].
        destruct g as [[b0 gk]|]; [|exact I]. apply c1_regions1_In. right. split; [exact B2 | destruct gk; intros E; discriminate E].
    - intros bb ll Hin. apply c1_regions1_In in Hin. destruct Hin as [E|[Hin _]]; [unfold c1_R' in E; discriminate E | exact (BL bb ll Hin)].
  Qed.

  Hypothesis XOK : xok X.

  Lemma c1_nr_R' : maps_subtract (noacc_of_region c1_R) c1_p (c1_p + 4096) = noacc_of_region c1_R'.
  Proof.
    pose proof c1_R_rng as (R1 & R2 & R3 & R4 & R5). pose proof c1_R_meta as (E1 & E2 & E3). pose proof c1_p_val as [P3 P4].
    ceil; unfold HEAPLO in R1, R2.
    unfold c1_R, c1_R', noacc_of_region. cbn [rg_kind rg_base rg_len].
    replace (e + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (e =? 0) eqn:EX0.
    { (* [comment removed for export] *)
      apply Z.eqb_eq in EX0. rewrite EX0 in *. rewrite maps_subtract_cons, maps_subtract_nil, app_nil_r.
      unfold iv_subtract. rewrite !u64_lit by lia.
      rewrite (proj2 (Z.ltb_lt b c1_p)) by lia. rewrite Z.min_r by lia.
      replace (c1_p - b) with 4096 by lia. cbn [app]. f_equal.
      replace (4096 * (1 + (0 + 1))) with 8192 by lia.
      destruct (Z_lt_le_dec 8192 len) as [Hl|Hl].
      - rewrite !(proj2 (Z.ltb_lt _ _)) by lia. rewrite Z.max_r by lia. f_equal. f_equal; f_equal; lia.
      - rewrite !(proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    rewrite maps_subtract_cons.
    rewrite (iv_subtract_disjoint (Z_to_bv 64 b) (Z_to_bv 64 4096) c1_p (c1_p + 4096)); [| rewrite u64_lit; lia | lia | rewrite !u64_lit by lia; lia].
    cbn [app]. f_equal.
    rewrite (proj2 (Z.ltb_lt (4096 * (1 + e)) len)) by lia.
    rewrite maps_subtract_cons, maps_subtract_nil, app_nil_r.
    destruct (Z_lt_le_dec 1 ac) as [Hac2|Hac1].
    - rewrite (iv_subtract_prefix (Z_to_bv 64 (b + 4096 * (1 + e))) (Z_to_bv 64 (len - 4096 * (1 + e))) c1_p (c1_p + 4096)) by (rewrite !u64_lit by lia; lia).
      rewrite (proj2 (Z.ltb_lt (4096 * (1 + (e + 1))) len)) by lia. rewrite !u64_lit by lia.
      f_equal. f_equal; [f_equal; lia | f_equal; lia].
    - rewrite (iv_subtract_covered (Z_to_bv 64 (b + 4096 * (1 + e))) (Z_to_bv 64 (len - 4096 * (1 + e))) c1_p (c1_p + 4096)) by (rewrite !u64_lit by lia; lia).
      rewrite (proj2 (Z.ltb_ge (4096 * (1 + (e + 1))) len)) by lia. reflexivity.
  Qed.

  Lemma c1_Hp_img : img_free c1_p (c1_p + 4096).
  Proof.
    pose proof c1_p_in_R as [P1 P2]. pose proof (wi_regions st (WF_img st L HWF) c1_R c1_R_in) as RI. unfold c1_R in RI. cbn in RI.
    unfold img_free. destruct RI as [RI|RI]; [left | right]; lia.
  Qed.
  Lemma c1_t_wf_img : wf_img c1_st1.
  Proof.
    pose proof (WF_img st L HWF) as [WA WR].
    constructor; cbn [s_areas s_regions c1_st1 MhAMetaN.st'].
    - intros a Ha. unfold MhAMetaN.areas' in Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [exact (WA a Ha) | exact c1_Hp_img].
    - intros r Hr. apply c1_regions1_In in Hr. destruct Hr as [->|[Hr _]]; [| exact (WR r Hr)].
      pose proof (WR c1_R c1_R_in) as RI. unfold c1_R, c1_R' in *. cbn in *. exact RI.
  Qed.

  Lemma c1_t_ledger : LEDGERX c1_st1 X c1_vm1.
  Proof.
    pose proof c1_R_rng as (R1 & R2 & R3 & R4 & R5). pose proof c1_R_meta as (E1 & E2 & E3). pose proof c1_p_val as [P3 P4]. pose proof c1_p_in_R as [P1 P2].
    ceil; unfold HEAPLO in R1, R2.
    destruct HLG as [LM LN LB LR LMB]. constructor; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_mmap_base s_regions s_brk c1_st1 MhAMetaN.st' c1_vm1].
    - eapply Permutation_trans; [exact LM|]. apply Permutation_app_head.
      eapply Permutation_trans; [apply Permutation_map; exact c1_regions_perm|]. unfold c1_regions1. cbn [map]. apply Permutation_refl.
    - eapply Permutation_trans; [apply perm_maps_subtract; exact LN|].
      unfold noacc_of. cbn [s_brk s_regions c1_st1 MhAMetaN.st']. rewrite maps_subtract_app.
      rewrite (guard_subtract_apart st L HWF c1_p (c1_p + 4096) ltac:(lia)).
      2:{ intros b0 Hin. destruct (c1_other_apart _ Hin ltac:(intros E; discriminate E)); cbn in *; [right | left]; lia. }
      apply Permutation_app_head.
      eapply Permutation_trans; [apply perm_maps_subtract; apply perm_flat_map; exact c1_regions_perm|].
      unfold c1_regions1. cbn [flat_map]. rewrite maps_subtract_app, c1_nr_R'. apply Permutation_app_head.
      rewrite maps_subtract_flat_map.
      rewrite (flat_map_ext_In _ _ (fun x => maps_subtract (noacc_of_region x) c1_p (c1_p + 4096)) noacc_of_region (rremove c1_R (s_regions st))); [apply Permutation_refl|].
      intros r Hr. apply rremove_In in Hr. destruct Hr as [Hr NE]. apply (nr_subtract_apart st L HWF r c1_p (c1_p + 4096) Hr ltac:(lia)).
      destruct (c1_other_apart r Hr NE); [right | left]; lia.
    - destruct (s_brk st); exact LB.
    - exact LR.
    - exact LMB.
  Qed.

  Lemma c1_new_apart_X : forall r, In r c1_regions1 -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
    forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r).
  Proof.
    intros r Hr. left. apply c1_regions1_In in Hr. destruct Hr as [->|[Hr _]].
    - exists c1_R. split; [exact c1_R_in | split; reflexivity].
    - exists r. split; [exact Hr | split; reflexivity].
  Qed.
  Lemma c1_RSUM : RSUM c1_regions1 = RSUM (s_regions st).
  Proof. rewrite (RSUM_perm _ _ c1_regions_perm). unfold c1_regions1. rewrite !RSUM_cons. reflexivity. Qed.
  Lemma c1_len : length c1_regions1 = length (s_regions st).
  Proof. rewrite (Permutation_length c1_regions_perm). reflexivity. Qed.
End C1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section C2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  Hypothesis XOK : xok X.
  Hypothesis Hfl : s_flist st = [].
  Hypothesis Hac0 : c_avail_cnt (s_ctx st) = 0.
  Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  #[local] Notation cx := (s_ctx st).
  Hypothesis Hac : c_area_cnt cx = 0.
  Hypothesis HBU : s_brk st = BrkUntried.
  Variable B : Z.
  Hypothesis HB : bv_unsigned (vm_brk vm) = B.
  Hypothesis Hce : B + 8192 <= CEIL.
  Hypothesis HRF : region_free (vm_reserved vm ++ vm_maps vm) (Z_to_bv 64 B) (Z_to_bv 64 8192) = true.
  (* [comment removed for export] *)
  Variable gk : gkd.

  Definition c2_p : Z := B + 4096.
  Definition c2_Rn : region := first_brk_region B gk.
  Definition c2_regions2 : list region := c2_Rn :: s_regions st.
  Definition c2_brk2 : brk_state := BrkLive B (B + 8192) gk.
  Definition c2_st2 : mst := MhAMetaN.st' st c2_p c2_regions2 c2_brk2 0 (c_shift cx) (B + 8192).
  (* [comment removed for export] *)
  Definition c2_vm1 : VmMaps :=
    mkVmMapsFull (vm_reserved vm) ((vm_brk vm, Z_to_bv 64 8192) :: vm_maps vm) (vm_noaccess vm)
                 (vm_start_brk vm) (Z_to_bv 64 (B + 8192)) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm).
  (* [comment removed for export] *)
  Definition c2_vm2 : VmMaps :=
    match gk with
    | GPlain => c2_vm1
    | GNoAcc => mkVmMapsFull (vm_reserved vm) ((vm_brk vm, Z_to_bv 64 8192) :: vm_maps vm)
                  ((Z_to_bv 64 B, Z_to_bv 64 4096) :: maps_subtract (vm_noaccess vm) B (B + 4096))
                  (vm_start_brk vm) (Z_to_bv 64 (B + 8192)) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm)
    | GGone => mkVmMapsFull (vm_reserved vm) (maps_subtract ((vm_brk vm, Z_to_bv 64 8192) :: vm_maps vm) B (B + 4096))
                  (maps_subtract (vm_noaccess vm) B (B + 4096))
                  (vm_start_brk vm) (Z_to_bv 64 (B + 8192)) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm)
    end.

  Lemma c2_B_facts : B mod 4096 = 0 /\ IMG_HI <= B /\ vm_brk vm = vm_start_brk vm /\ bv_unsigned (vm_start_brk vm) = B.
  Proof.
    pose proof (lx_brk st X vm HLG) as LB. rewrite HBU in LB. destruct LB as (E1 & E2 & E3 & E4).
    rewrite <- E1 in E2, E3. rewrite HB in E2, E3. repeat split; try assumption. rewrite <- E1. exact HB.
  Qed.
  Lemma c2_Rn_shape : (rg_base c2_Rn = B /\ rg_len c2_Rn = 8192 /\ gk <> GGone) \/ (rg_base c2_Rn = B + 4096 /\ rg_len c2_Rn = 4096 /\ gk = GGone).
  Proof. unfold c2_Rn, first_brk_region. destruct gk; cbn; [left | left | right]; repeat split; try lia; discriminate. Qed.
  Lemma c2_Rn_kind : rg_kind c2_Rn = RBrk.
  Proof. unfold c2_Rn, first_brk_region. destruct gk; reflexivity. Qed.
  Lemma c2_Rn_eq : c2_Rn = RG (rg_base c2_Rn) (rg_len c2_Rn) RBrk.
  Proof. unfold c2_Rn, first_brk_region. destruct gk; reflexivity. Qed.
  Ltac shc H := let E1 := fresh "SE" in let E2 := fresh "SE" in destruct H as [(E1 & E2 & _)|(E1 & E2 & _)]; rewrite ?E1, ?E2 in *.
  Lemma c2_apart : (forall r, In r (s_regions st) -> B + 8192 <= rg_base r \/ rg_base r + rg_len r <= B) /\
                (forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en <= 2 ^ 35 /\ ea + en <= CEIL /\ ea mod 4096 = 0 /\
                         (B + 8192 <= ea \/ ea + en <= B)).
  Proof. pose proof c2_B_facts as (_ & B2 & _). exact (rf_apart st L X vm HWF HLG XOK B 8192 ltac:(lia) ltac:(lia) Hce HRF). Qed.

  Lemma c2_Hp : c2_p mod 4096 = 0 /\ HEAPLO <= c2_p /\ c2_p + 4096 <= CEIL.
  Proof. pose proof c2_B_facts as (B1 & B2 & _). unfold c2_p, HEAPLO in *. split; [rewrite Z.add_mod, B1 by lia; reflexivity | lia]. Qed.
  Lemma c2_Hp_img : img_free c2_p (c2_p + 4096).
  Proof. pose proof c2_B_facts as (_ & B2 & _). unfold img_free, c2_p. right. lia. Qed.
  Lemma c2_Hp_areas : forall a, In a (s_areas st) -> a + 4096 <= c2_p \/ c2_p + 4096 <= a.
  Proof.
    intros a Ha. destruct (area_in_region st L HWF a Ha) as (r & Hr & _ & R1 & R2). destruct (proj1 c2_apart r Hr); unfold c2_p; lia.
  Qed.
  Lemma c2_Hp_groups : forall x, is_group st x -> gspan st x <= c2_p \/ c2_p + 4096 <= g_mem st x.
  Proof.
    intros x Hx. destruct (group_in_top st L HWF x Hx) as (t & Ht & Kt & T1 & T2 & Hin).
    destruct (proj1 c2_apart _ Hin); cbn in *; unfold g_map_end, c2_p in *; lia.
  Qed.
  Lemma c2_HRgrp : forall b0 l0 x, In (RG b0 l0 (RGroup x)) c2_regions2 <-> In (RG b0 l0 (RGroup x)) (s_regions st).
  Proof.
    intros b0 l0 x. unfold c2_regions2. cbn. split; [intros [E|A]; [|exact A] | intros A; right; exact A].
    exfalso. pose proof (f_equal rg_kind E) as K. rewrite c2_Rn_kind in K. discriminate K.
  Qed.
  Lemma c2_HRsub : forall r, In r (s_regions st) -> exists r', In r' c2_regions2 /\ rg_base r' = rg_base r /\ rg_len r' = rg_len r.
  Proof. intros r Hr. exists r. split; [right; exact Hr | split; reflexivity]. Qed.
  Lemma c2_HRold : forall a, In a (s_areas st) -> INREG c2_regions2 c2_brk2 a.
  Proof.
    intros a Ha. destruct (wa_inreg st (WF_areas st L HWF) a Ha) as [(b2 & l2 & Hin & A1 & A2 & A3)|(b2 & l2 & e2 & Hin & A1 & A2)].
    - exfalso. pose proof (wr_brk st (WF_regions st L HWF)) as RB. rewrite HBU in RB. exact (RB b2 l2 Hin).
    - right. exists b2, l2, e2. split; [right; exact Hin | lia].
  Qed.
  Lemma c2_HRnew : INREG c2_regions2 c2_brk2 c2_p.
  Proof.
    left. exists (rg_base c2_Rn), (rg_len c2_Rn). split; [left; exact c2_Rn_eq|]. cbn. unfold c2_p.
    destruct c2_Rn_shape as [(-> & -> & _)|(-> & -> & _)]; lia.
  Qed.

  Lemma c2_Hsh' : 0 <= c_shift cx /\ c_shift cx <= Z.of_nat (length (s_areas st)) + 2 /\ (0 = 0 -> c_shift cx <= Z.of_nat (length (s_areas st)) + 1).
  Proof. pose proof (wc_shift st (WF_ctx st L HWF)). lia. Qed.
  Lemma c2_Hbrk' : match c2_brk2 with
                | BrkUntried => B + 8192 = 0
                | BrkLive b0 b1 _ => B + 8192 = b1 /\ b0 mod 4096 = 0 /\ b1 mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b1 /\ b1 <= CEIL
                | BrkDead _ => B + 8192 = 2 ^ 64 - 1
                end.
  Proof. cbn. pose proof c2_B_facts as (B1 & B2 & _). repeat split; try lia. rewrite Z.add_mod, B1 by lia. reflexivity. Qed.

  Lemma c2_Rn_notin : ~ In c2_Rn (s_regions st).
  Proof.
    intros Hin. pose proof (wr_brk st (WF_regions st L HWF)) as RB. rewrite HBU in RB. rewrite c2_Rn_eq in Hin. exact (RB _ _ Hin).
  Qed.

  Lemma c2_t_wf_regions : wf_regions c2_st2.
  Proof.
    pose proof c2_B_facts as (B1 & B2 & _). pose proof c2_Hp as HP. pose proof c2_Hp_areas as HPA. pose proof c2_Rn_shape as SH. pose proof c2_Rn_kind as RK.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; cbn [s_regions s_brk s_ctx c2_st2 MhAMetaN.st' MhAMetaN.cx' c_shift s_areas].
    - intros r [<-|Hr]; [| exact (RNG r Hr)]. unfold HEAPLO. shc SH; (repeat split; try lia).
      all: rewrite Z.add_mod, B1 by lia; reflexivity.
    - intros r1 r2 [<-|H1] [<-|H2] Hne.
      + exfalso; exact (Hne eq_refl).
      + destruct (proj1 c2_apart r2 H2); shc SH; lia.
      + destruct (proj1 c2_apart r1 H1); shc SH; lia.
      + exact (DISJ r1 r2 H1 H2 Hne).
    - apply NoDup_ListNoDup. constructor; [exact c2_Rn_notin | apply NoDup_ListNoDup; exact ND].
    - intros r [<-|Hr]; [shc SH; lia | exact (LEN r Hr)].
    - intros b0 l0 x Hin. apply c2_HRgrp in Hin. rewrite (MhAMetaN.e_gsc st L HWF c2_p c2_regions2 c2_brk2 0 (c_shift cx) (B + 8192) HP HPA) by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (GB b0 l0 x Hin).
    - intros b0 l0 x Hin H63. apply c2_HRgrp in Hin.
      rewrite (MhAMetaN.e_gsc st L HWF c2_p c2_regions2 c2_brk2 0 (c_shift cx) (B + 8192) HP HPA) in H63 by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (G63 b0 l0 x Hin H63).
    - intros b0 l0 e0 [E|Hin]; [| exact (MT b0 l0 e0 Hin)]. exfalso. pose proof (f_equal rg_kind E) as K. rewrite RK in K. discriminate K.
    - unfold c2_regions2. rewrite (count_kind_cons (fun k => match k with RMeta _ => true | _ => false end) c2_Rn). rewrite RK. exact MC.
    - unfold MhAMetaN.areas'. rewrite length_app. cbn [length]. rewrite HBU in BRK. split; [|split].
      + intros b2 l2 [E|Hin]; [| exfalso; exact (BRK b2 l2 Hin)].
        pose proof (f_equal rg_base E) as E1. pose proof (f_equal rg_len E) as E2. cbn in E1, E2. destruct SH as [(X1 & X2 & _)|(X1 & X2 & _)]; lia.
      + unfold c2_regions2. rewrite (count_kind_cons (fun k => match k with RBrk => true | _ => false end) c2_Rn). rewrite RK.
        rewrite filter_all_false; [cbn; lia|]. intros r Hr. destruct r as [rb rl [|ex|y]]; [exfalso; exact (BRK rb rl Hr) | reflexivity | reflexivity].
      + left. reflexivity.
    - intros bb ll [E|Hin]; [| exact (BL bb ll Hin)]. pose proof (f_equal rg_len E) as E2. cbn in E2. destruct SH as [(_ & X2 & _)|(_ & X2 & _)]; lia.
  Qed.

  Lemma c2_t_wf_img : wf_img c2_st2.
  Proof.
    pose proof c2_B_facts as (_ & B2 & _). pose proof (WF_img st L HWF) as [WA WR]. pose proof c2_Rn_shape as SH.
    constructor; cbn [s_areas s_regions c2_st2 MhAMetaN.st'].
    - intros a Ha. unfold MhAMetaN.areas' in Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [exact (WA a Ha) | exact c2_Hp_img].
    - intros r [<-|Hr]; [| exact (WR r Hr)]. unfold img_free. right. destruct SH as [(-> & _)|(-> & _)]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_maps_apart : forall en, In en (vm_maps vm) ->
    exists x y, en = (Z_to_bv 64 x, Z_to_bv 64 y) /\ 0 <= x /\ 0 < y /\ x + y < 2 ^ 64 /\ (x + y <= B \/ B + 4096 <= x).
  Proof.
    intros en Hen. pose proof c2_B_facts as (_ & B2 & _). ceil. unfold HEAPLO in XOK.
    rewrite region_free_app in HRF. apply andb_true_iff in HRF. destruct HRF as [_ RF].
    destruct en as [eb es]. pose proof (region_free_In _ _ _ _ _ RF Hen) as D. rewrite !u64_lit in D by lia.
    pose proof (u64_range eb). pose proof (u64_range es).
    (* [comment removed for export] *)
    assert (IN : In (eb, es) (X ++ map region_entry (s_regions st))) by exact (Permutation_in _ (lx_maps st X vm HLG) Hen).
    apply in_app_iff in IN. destruct IN as [IX|IR].
    - destruct (XOK _ IX) as (ea & en & E & E1 & E2 & E3 & E4). injection E. intros -> ->. unfold HEAPLO in E1. rewrite ?u64_lit in D by lia.
      exists ea, en. split; [reflexivity|]. lia.
    - apply in_map_iff in IR. destruct IR as (r & E & Hr). unfold region_entry in E. injection E. intros <- <-.
      destruct (regions_rng st L HWF r Hr) as (R1 & R2 & R3 & R4 & R5). unfold HEAPLO in R1. rewrite ?u64_lit in D by lia.
      exists (rg_base r), (rg_len r). split; [reflexivity|]. lia.
  Qed.

  Lemma c2_t_ledger : LEDGERX c2_st2 X c2_vm2.
  Proof.
    pose proof c2_B_facts as (B1 & B2 & B3 & B4). ceil. pose proof c2_Rn_shape as SH.
    assert (NSUB : maps_subtract (vm_noaccess vm) B (B + 4096) = vm_noaccess vm).
    { destruct HLG as [LM LN LB LR LT].
      assert (P : Permutation (maps_subtract (vm_noaccess vm) B (B + 4096)) (maps_subtract (noacc_of st) B (B + 4096))) by (apply perm_maps_subtract; exact LN).
      apply maps_subtract_apart; [lia|]. intros en Hen.
      assert (Hen' : In en (noacc_of st)) by exact (Permutation_in _ LN Hen).
      unfold noacc_of in Hen'. rewrite HBU in Hen'. cbn [guard_noacc guard_kind app] in Hen'.
      apply in_flat_map in Hen'. destruct Hen' as (r & Hr & Hin).
      destruct (nr_inside st L HWF r en Hr Hin) as (x & y & -> & A1 & A2 & A3 & A4 & A5). exists x, y. split; [reflexivity|].
      destruct (proj1 c2_apart r Hr); repeat split; lia. }
    destruct HLG as [LM LN LB LR LT]. constructor.
    - (* [comment removed for export] *) cbn [s_regions c2_st2 MhAMetaN.st']. unfold c2_vm2, c2_vm1, c2_regions2. destruct gk; cbn [vm_maps map].
      + replace (region_entry c2_Rn) with (vm_brk vm, Z_to_bv 64 8192).
        2:{ rewrite c2_Rn_eq. destruct SH as [(-> & -> & _)|(_ & _ & E)]; [|discriminate E]. unfold region_entry. cbn. f_equal. symmetry. apply Z_to_bv_u_eq'. symmetry. exact HB. }
        eapply Permutation_trans; [apply perm_skip; exact LM|]. apply Permutation_middle.
      + replace (region_entry c2_Rn) with (vm_brk vm, Z_to_bv 64 8192).
        2:{ rewrite c2_Rn_eq. destruct SH as [(-> & -> & _)|(_ & _ & E)]; [|discriminate E]. unfold region_entry. cbn. f_equal. symmetry. apply Z_to_bv_u_eq'. symmetry. exact HB. }
        eapply Permutation_trans; [apply perm_skip; exact LM|]. apply Permutation_middle.
      + rewrite maps_subtract_cons.
        replace (iv_subtract (vm_brk vm) (Z_to_bv 64 8192) B (B + 4096)) with [region_entry c2_Rn].
        2:{ rewrite c2_Rn_eq. destruct SH as [(_ & _ & E)|(-> & -> & _)]; [exfalso; exact (E eq_refl)|]. unfold region_entry. cbn [rg_base rg_len].
            rewrite <- (Z_to_bv_u_eq' (vm_brk vm) B (eq_sym HB)). symmetry. rewrite (iv_subtract_prefix (Z_to_bv 64 B) (Z_to_bv 64 8192) B (B + 4096)); rewrite ?u64_lit by lia; try lia.
            repeat f_equal; lia. }
        rewrite (maps_subtract_apart (vm_maps vm) B (B + 4096) ltac:(lia) c2_maps_apart).
        cbn [app]. eapply Permutation_trans; [apply perm_skip; exact LM|]. apply Permutation_middle.
    - (* [comment removed for export] *) unfold c2_vm2, c2_vm1, noacc_of, guard_noacc, guard_kind. cbn [s_brk s_regions c2_st2 MhAMetaN.st'].
      unfold c2_brk2, c2_regions2. cbn [flat_map]. rewrite (c2_Rn_eq). cbn [noacc_of_region rg_kind app].
      unfold noacc_of in LN. rewrite HBU in LN. cbn [guard_noacc guard_kind app] in LN.
      destruct gk; cbn [vm_noaccess app]; [exact LN | apply perm_skip; rewrite NSUB; exact LN | rewrite NSUB; exact LN].
    - (* [comment removed for export] *) cbn [s_brk c2_st2 MhAMetaN.st' c2_brk2]. unfold c2_vm2, c2_vm1. destruct gk; cbn [vm_brk vm_start_brk]; rewrite u64_lit by lia; (split; [reflexivity | exact B4]).
    - unfold c2_vm2, c2_vm1. destruct gk; cbn [vm_reserved]; exact LR.
    - unfold c2_vm2, c2_vm1. destruct gk; exact LT.
  Qed.

  Lemma c2_new_apart_X : forall r, In r c2_regions2 -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
    forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r).
  Proof.
    intros r [<-|Hr]; [right | left; exists r; split; [exact Hr | split; reflexivity]]. intros e He. destruct (proj2 c2_apart e He) as (ea & en & -> & X1 & X2 & X3 & X4 & D).
    exists ea, en. split; [reflexivity|]. pose proof c2_Rn_shape as SH. shc SH; repeat split; lia.
  Qed.
  Lemma c2_RSUM : RSUM c2_regions2 <= RSUM (s_regions st) + 8192.
  Proof. unfold c2_regions2. rewrite RSUM_cons. destruct c2_Rn_shape as [(_ & -> & _)|(_ & -> & _)]; lia. Qed.
  Lemma c2_len : length c2_regions2 = S (length (s_regions st)).
  Proof. reflexivity. Qed.
End C2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section C3.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  Hypothesis XOK : xok X.
  Hypothesis Hfl : s_flist st = [].
  Hypothesis Hac0 : c_avail_cnt (s_ctx st) = 0.
  Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  #[local] Notation cx := (s_ctx st).
  Hypothesis Hac : c_area_cnt cx = 0.
  Variables (b0 b : Z) (gk : gkd).
  Hypothesis HBL : s_brk st = BrkLive b0 b gk.
  Hypothesis Hce : b + 4096 <= CEIL.
  Hypothesis HRF : region_free (vm_reserved vm ++ vm_maps vm) (Z_to_bv 64 b) (Z_to_bv 64 4096) = true.

  Definition c3_p : Z := b.
  Definition c3_Rn : region := RG b 4096 RBrk.
  Definition c3_regions : list region := c3_Rn :: s_regions st.
  Definition c3_brk : brk_state := BrkLive b0 (b + 4096) gk.
  Definition c3_st : mst := MhAMetaN.st' st c3_p c3_regions c3_brk 0 (c_shift cx) (b + 4096).
  Definition c3_vm : VmMaps :=
    mkVmMapsFull (vm_reserved vm) ((vm_brk vm, Z_to_bv 64 4096) :: vm_maps vm) (vm_noaccess vm)
                 (vm_start_brk vm) (Z_to_bv 64 (b + 4096)) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm).

  Lemma c3_b_facts : c_brk cx = b /\ b0 mod 4096 = 0 /\ b mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b /\ b <= CEIL /\
                     bv_unsigned (vm_brk vm) = b /\ bv_unsigned (vm_start_brk vm) = b0.
  Proof.
    pose proof (wc_brk st (WF_ctx st L HWF)) as WB. rewrite HBL in WB. pose proof (lx_brk st X vm HLG) as LB. rewrite HBL in LB. tauto.
  Qed.
  Lemma c3_apart : (forall r, In r (s_regions st) -> b + 4096 <= rg_base r \/ rg_base r + rg_len r <= b) /\
                (forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en <= 2 ^ 35 /\ ea + en <= CEIL /\ ea mod 4096 = 0 /\
                         (b + 4096 <= ea \/ ea + en <= b)).
  Proof. pose proof c3_b_facts as (_ & _ & _ & B2 & B3 & _). exact (rf_apart st L X vm HWF HLG XOK b 4096 ltac:(lia) ltac:(lia) Hce HRF). Qed.

  Lemma c3_Hp : c3_p mod 4096 = 0 /\ HEAPLO <= c3_p /\ c3_p + 4096 <= CEIL.
  Proof. pose proof c3_b_facts as (_ & _ & B1 & B2 & B3 & _). unfold c3_p, HEAPLO. repeat split; try assumption; lia. Qed.
  Lemma c3_Hp_img : img_free c3_p (c3_p + 4096).
  Proof. pose proof c3_b_facts as (_ & _ & _ & B2 & B3 & _). unfold img_free, c3_p. right. lia. Qed.
  Lemma c3_Hp_areas : forall a, In a (s_areas st) -> a + 4096 <= c3_p \/ c3_p + 4096 <= a.
  Proof.
    intros a Ha. destruct (area_in_region st L HWF a Ha) as (r & Hr & _ & R1 & R2). destruct (proj1 c3_apart r Hr); unfold c3_p; lia.
  Qed.
  Lemma c3_Hp_groups : forall x, is_group st x -> gspan st x <= c3_p \/ c3_p + 4096 <= g_mem st x.
  Proof.
    intros x Hx. destruct (group_in_top st L HWF x Hx) as (t & Ht & Kt & T1 & T2 & Hin).
    destruct (proj1 c3_apart _ Hin); cbn in *; unfold g_map_end, c3_p in *; lia.
  Qed.
  Lemma c3_HRgrp : forall b2 l2 x, In (RG b2 l2 (RGroup x)) c3_regions <-> In (RG b2 l2 (RGroup x)) (s_regions st).
  Proof. intros b2 l2 x. unfold c3_regions. cbn. split; [intros [E|A]; [discriminate E | exact A] | intros A; right; exact A]. Qed.
  Lemma c3_HRsub : forall r, In r (s_regions st) -> exists r', In r' c3_regions /\ rg_base r' = rg_base r /\ rg_len r' = rg_len r.
  Proof. intros r Hr. exists r. split; [right; exact Hr | split; reflexivity]. Qed.
  Lemma c3_HRold : forall a, In a (s_areas st) -> INREG c3_regions c3_brk a.
  Proof.
    intros a Ha. destruct (wa_inreg st (WF_areas st L HWF) a Ha) as [(b2 & l2 & Hin & A1 & A2 & A3)|(b2 & l2 & e2 & Hin & A1 & A2)].
    - left. exists b2, l2. split; [right; exact Hin|]. rewrite HBL in A3. cbn in A3 |- *. repeat split; assumption.
    - right. exists b2, l2, e2. split; [right; exact Hin | lia].
  Qed.
  Lemma c3_HRnew : INREG c3_regions c3_brk c3_p.
  Proof. left. exists b, 4096. pose proof c3_b_facts as (_ & _ & _ & _ & B3 & _). split; [left; reflexivity|]. cbn. unfold c3_p. lia. Qed.

  Lemma c3_Hsh' : 0 <= c_shift cx /\ c_shift cx <= Z.of_nat (length (s_areas st)) + 2 /\ (0 = 0 -> c_shift cx <= Z.of_nat (length (s_areas st)) + 1).
  Proof. pose proof (wc_shift st (WF_ctx st L HWF)). lia. Qed.
  Lemma c3_Hbrk' : match c3_brk with
                | BrkUntried => b + 4096 = 0
                | BrkLive x0 x1 _ => b + 4096 = x1 /\ x0 mod 4096 = 0 /\ x1 mod 4096 = 0 /\ IMG_HI <= x0 /\ x0 + 8192 <= x1 /\ x1 <= CEIL
                | BrkDead _ => b + 4096 = 2 ^ 64 - 1
                end.
  Proof. cbn. pose proof c3_b_facts as (_ & B0 & B1 & B2 & B3 & _). repeat split; try lia; try assumption. rewrite Z.add_mod, B1 by lia. reflexivity. Qed.

  Lemma c3_Rn_notin : ~ In c3_Rn (s_regions st).
  Proof.
    intros Hin. pose proof (wr_brk st (WF_regions st L HWF)) as RB. rewrite HBL in RB. destruct RB as (RB & _).
    destruct (RB b 4096 Hin). lia.
  Qed.

  Lemma c3_t_wf_regions : wf_regions c3_st.
  Proof.
    pose proof c3_b_facts as (_ & B0 & B1 & B2 & B3 & B4 & _). pose proof c3_Hp as HP. pose proof c3_Hp_areas as HPA.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; cbn [s_regions s_brk s_ctx c3_st MhAMetaN.st' MhAMetaN.cx' c_shift s_areas].
    - intros r [<-|Hr]; [cbn; unfold HEAPLO in *; repeat split; try lia; exact B1 | exact (RNG r Hr)].
    - intros r1 r2 [<-|H1] [<-|H2] Hne.
      + exfalso; exact (Hne eq_refl).
      + destruct (proj1 c3_apart r2 H2); cbn; lia.
      + destruct (proj1 c3_apart r1 H1); cbn; lia.
      + exact (DISJ r1 r2 H1 H2 Hne).
    - apply NoDup_ListNoDup. constructor; [exact c3_Rn_notin | apply NoDup_ListNoDup; exact ND].
    - intros r [<-|Hr]; [cbn; lia | exact (LEN r Hr)].
    - intros b2 l2 x Hin. apply c3_HRgrp in Hin. rewrite (MhAMetaN.e_gsc st L HWF c3_p c3_regions c3_brk 0 (c_shift cx) (b + 4096) HP HPA) by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (GB b2 l2 x Hin).
    - intros b2 l2 x Hin H63. apply c3_HRgrp in Hin.
      rewrite (MhAMetaN.e_gsc st L HWF c3_p c3_regions c3_brk 0 (c_shift cx) (b + 4096) HP HPA) in H63 by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (G63 b2 l2 x Hin H63).
    - intros b2 l2 e2 [E|Hin]; [discriminate E | exact (MT b2 l2 e2 Hin)].
    - unfold c3_regions. rewrite (count_kind_cons (fun k => match k with RMeta _ => true | _ => false end) c3_Rn). cbn [rg_kind c3_Rn]. exact MC.
    - unfold MhAMetaN.areas'. rewrite length_app. cbn [length]. rewrite HBL in BRK. destruct BRK as (BR1 & BR2 & BR3). split; [|split].
      + intros b2 l2 [E|Hin]; [unfold c3_Rn in E; injection E; intros -> ->; lia | destruct (BR1 b2 l2 Hin); lia].
      + unfold c3_regions. rewrite (count_kind_cons (fun k => match k with RBrk => true | _ => false end) c3_Rn). cbn [rg_kind c3_Rn]. lia.
      + right. exact BR3.
    - intros bb ll [E|Hin]; [unfold c3_Rn in E; injection E; intros; subst; lia | exact (BL bb ll Hin)].
  Qed.

  Lemma c3_t_wf_img : wf_img c3_st.
  Proof.
    pose proof (WF_img st L HWF) as [WA WR]. pose proof c3_b_facts as (_ & _ & _ & B2 & B3 & _).
    constructor; cbn [s_areas s_regions c3_st MhAMetaN.st'].
    - intros a Ha. unfold MhAMetaN.areas' in Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [exact (WA a Ha) | exact c3_Hp_img].
    - intros r [<-|Hr]; [| exact (WR r Hr)]. unfold img_free. cbn. right. lia.
  Qed.
  Lemma c3_RSUM : RSUM c3_regions = RSUM (s_regions st) + 4096.
  Proof. unfold c3_regions. rewrite RSUM_cons. cbn. lia. Qed.
  Lemma c3_len : length c3_regions = S (length (s_regions st)).
  Proof. reflexivity. Qed.

  Lemma c3_t_ledger : LEDGERX c3_st X c3_vm.
  Proof.
    pose proof c3_b_facts as (_ & B0 & B1 & B2 & B3 & B4 & B5 & B6). unfold HEAPLO in B2. ceil.
    destruct HLG as [LM LN LB LR LT]. constructor; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_mmap_base vm_init_sp s_regions s_brk c3_st MhAMetaN.st' c3_vm].
    - unfold c3_regions. cbn [map]. replace (region_entry c3_Rn) with (vm_brk vm, Z_to_bv 64 4096).
      2:{ unfold region_entry, c3_Rn. cbn. f_equal. symmetry. apply Z_to_bv_u_eq'. symmetry. exact B5. }
      eapply Permutation_trans; [apply perm_skip; exact LM|]. apply Permutation_middle.
    - eapply Permutation_trans; [exact LN|]. unfold noacc_of. rewrite HBL. cbn [s_brk s_regions c3_st MhAMetaN.st' guard_noacc guard_kind c3_brk c3_regions flat_map noacc_of_region c3_Rn rg_kind app].
      apply Permutation_refl.
    - rewrite u64_lit by lia. split; [reflexivity | exact B6].
    - exact LR.
    - exact LT.
  Qed.

  Lemma c3_new_apart_X : forall r, In r c3_regions -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
    forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r).
  Proof.
    intros r [<-|Hr]; [right | left; exists r; split; [exact Hr | split; reflexivity]]. intros e He. destruct (proj2 c3_apart e He) as (ea & en & -> & X1 & X2 & X3 & X4 & D).
    exists ea, en. split; [reflexivity|]. cbn. repeat split; lia.
  Qed.
End C3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section C4.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  Hypothesis XOK : xok X.
  Hypothesis Hfl : s_flist st = [].
  Hypothesis Hac0 : c_avail_cnt (s_ctx st) = 0.
  Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  #[local] Notation cx := (s_ctx st).
  #[local] Notation sh := (c_shift (s_ctx st)).
  Hypothesis Hac : c_area_cnt cx = 0.
  Definition c4_N : Z := 2 * 2 ^ sh * 4096.
  Variable p0 : Z.
  Hypothesis Hp0 : p0 mod 4096 = 0 /\ HEAPLO <= p0 /\ p0 + c4_N <= CEIL.
  Hypothesis HRF : region_free (vm_reserved vm ++ vm_maps vm) (Z_to_bv 64 p0) (Z_to_bv 64 c4_N) = true.

  (* [comment removed for export] *)
  Hypothesis Hp0img : p0 + c4_N <= IMG_LO \/ IMG_HI <= p0.
  Definition c4_p : Z := p0 + 4096.
  Definition c4_Rn : region := RG p0 c4_N (RMeta 1).
  Definition c4_regions : list region := c4_Rn :: s_regions st.
  Definition c4_brk : brk_state := BrkDead (guard_kind (s_brk st)).
  Definition c4_ac : Z := 2 * 2 ^ sh - 2.
  Definition c4_st : mst := MhAMetaN.st' st c4_p c4_regions c4_brk c4_ac (sh + 1) (2 ^ 64 - 1).
  Definition c4_vm : VmMaps :=
    mkVmMapsFull (vm_reserved vm) ((Z_to_bv 64 p0, Z_to_bv 64 c4_N) :: vm_maps vm)
                 (maps_subtract ((Z_to_bv 64 p0, Z_to_bv 64 c4_N) :: vm_noaccess vm) (p0 + 4096) (p0 + 8192))
                 (vm_start_brk vm) (vm_brk vm) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm).

  Lemma c4_sh_rng : 0 <= sh <= 11.
  Proof.
    pose proof (wc_shift st (WF_ctx st L HWF)). pose proof (wc_shacc st (WF_ctx st L HWF)) as SA. rewrite Hac in SA. unfold AREAMAX in Hcnt.
    split; [lia|]. destruct (Z_lt_le_dec 11 sh) as [LT|GE]; [|exact GE]. exfalso.
    assert (2 ^ 13 <= 2 ^ (sh + 1)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in *. lia.
  Qed.
  Lemma c4_N_rng : 8192 <= c4_N <= 2 ^ 24 /\ c4_N mod 4096 = 0 /\ c4_N = 4096 * (2 * 2 ^ sh).
  Proof.
    pose proof c4_sh_rng as [S1 S2]. unfold c4_N.
    assert (1 <= 2 ^ sh) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
    assert (2 ^ sh <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia).
    split; [cbn in *; lia|]. split; [rewrite Z.mod_mul; lia | lia].
  Qed.
  Lemma c4_apart : (forall r, In r (s_regions st) -> p0 + c4_N <= rg_base r \/ rg_base r + rg_len r <= p0) /\
                (forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en <= 2 ^ 35 /\ ea + en <= CEIL /\ ea mod 4096 = 0 /\
                         (p0 + c4_N <= ea \/ ea + en <= p0)).
  Proof.
    pose proof c4_N_rng as (N1 & _). destruct Hp0 as (P1 & P2 & P3). unfold HEAPLO in P2.
    exact (rf_apart st L X vm HWF HLG XOK p0 c4_N ltac:(lia) ltac:(lia) P3 HRF).
  Qed.

  Lemma c4_guard_of : guard_of c4_brk = guard_of (s_brk st).
  Proof. unfold c4_brk, guard_of, guard_kind. destruct (s_brk st) as [|x0 x1 g|[[x0 g]|]]; reflexivity. Qed.

  Lemma c4_Hp : c4_p mod 4096 = 0 /\ HEAPLO <= c4_p /\ c4_p + 4096 <= CEIL.
  Proof. pose proof c4_N_rng as (N1 & _). destruct Hp0 as (P1 & P2 & P3). unfold c4_p. split; [rewrite Z.add_mod, P1 by lia; reflexivity | lia]. Qed.
  Lemma c4_Hp_areas : forall a, In a (s_areas st) -> a + 4096 <= c4_p \/ c4_p + 4096 <= a.
  Proof.
    intros a Ha. pose proof c4_N_rng as (N1 & _). destruct (area_in_region st L HWF a Ha) as (r & Hr & _ & R1 & R2). destruct (proj1 c4_apart r Hr); unfold c4_p; lia.
  Qed.
  Lemma c4_Hp_groups : forall x, is_group st x -> gspan st x <= c4_p \/ c4_p + 4096 <= g_mem st x.
  Proof.
    intros x Hx. pose proof c4_N_rng as (N1 & _). destruct (group_in_top st L HWF x Hx) as (t & Ht & Kt & T1 & T2 & Hin).
    destruct (proj1 c4_apart _ Hin); cbn in *; unfold g_map_end, c4_p in *; lia.
  Qed.
  Lemma c4_HRgrp : forall b2 l2 x, In (RG b2 l2 (RGroup x)) c4_regions <-> In (RG b2 l2 (RGroup x)) (s_regions st).
  Proof. intros b2 l2 x. unfold c4_regions. cbn. split; [intros [E|A]; [discriminate E | exact A] | intros A; right; exact A]. Qed.
  Lemma c4_HRsub : forall r, In r (s_regions st) -> exists r', In r' c4_regions /\ rg_base r' = rg_base r /\ rg_len r' = rg_len r.
  Proof. intros r Hr. exists r. split; [right; exact Hr | split; reflexivity]. Qed.
  Lemma c4_HRold : forall a, In a (s_areas st) -> INREG c4_regions c4_brk a.
  Proof.
    intros a Ha. destruct (wa_inreg st (WF_areas st L HWF) a Ha) as [(b2 & l2 & Hin & A1 & A2 & A3)|(b2 & l2 & e2 & Hin & A1 & A2)].
    - left. exists b2, l2. split; [right; exact Hin|]. rewrite c4_guard_of. repeat split; assumption.
    - right. exists b2, l2, e2. split; [right; exact Hin | lia].
  Qed.
  Lemma c4_HRnew : INREG c4_regions c4_brk c4_p.
  Proof. right. exists p0, c4_N, 1. pose proof c4_N_rng as (N1 & _). split; [left; reflexivity|]. unfold c4_p. lia. Qed.
  Lemma c4_Hcur' : c4_ac > 0 -> exists b2 l2 e2, In (RG b2 l2 (RMeta e2)) c4_regions /\ 0 <= e2 /\ c4_p + 4096 = b2 + 4096 * (1 + e2) /\ c4_p + 4096 + 4096 * c4_ac = b2 + l2.
  Proof. intros H. exists p0, c4_N, 1. pose proof c4_N_rng as (N1 & N2 & N3). split; [left; reflexivity|]. unfold c4_p, c4_ac. lia. Qed.

  Lemma c4_Hsh' : 0 <= sh + 1 /\ sh + 1 <= Z.of_nat (length (s_areas st)) + 2 /\ (c4_ac = 0 -> sh + 1 <= Z.of_nat (length (s_areas st)) + 1).
  Proof. pose proof (wc_shift st (WF_ctx st L HWF)). pose proof c4_sh_rng. unfold c4_ac. lia. Qed.
  Lemma c4_Hbrk' : match c4_brk with
                | BrkUntried => 2 ^ 64 - 1 = 0
                | BrkLive x0 x1 _ => 2 ^ 64 - 1 = x1 /\ x0 mod 4096 = 0 /\ x1 mod 4096 = 0 /\ IMG_HI <= x0 /\ x0 + 8192 <= x1 /\ x1 <= CEIL
                | BrkDead _ => 2 ^ 64 - 1 = 2 ^ 64 - 1
                end.
  Proof. reflexivity. Qed.

  Lemma c4_Rn_notin : ~ In c4_Rn (s_regions st).
  Proof. intros Hin. pose proof c4_N_rng as (N1 & _). destruct (proj1 c4_apart _ Hin); cbn in *; lia. Qed.

  Lemma c4_t_wf_regions : wf_regions c4_st.
  Proof.
    pose proof c4_N_rng as (N1 & N2 & N3). destruct Hp0 as (P1 & P2 & P3). pose proof c4_Hp as HP. pose proof c4_Hp_areas as HPA.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; cbn [s_regions s_brk s_ctx c4_st MhAMetaN.st' MhAMetaN.cx' c_shift s_areas].
    - intros r [<-|Hr]; [cbn; repeat split; try lia; assumption | exact (RNG r Hr)].
    - intros r1 r2 [<-|H1] [<-|H2] Hne.
      + exfalso; exact (Hne eq_refl).
      + destruct (proj1 c4_apart r2 H2); cbn; lia.
      + destruct (proj1 c4_apart r1 H1); cbn; lia.
      + exact (DISJ r1 r2 H1 H2 Hne).
    - apply NoDup_ListNoDup. constructor; [exact c4_Rn_notin | apply NoDup_ListNoDup; exact ND].
    - intros r [<-|Hr]; [cbn; lia | exact (LEN r Hr)].
    - intros b2 l2 x Hin. apply c4_HRgrp in Hin. rewrite (MhAMetaN.e_gsc st L HWF c4_p c4_regions c4_brk c4_ac (sh + 1) (2 ^ 64 - 1) HP HPA) by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (GB b2 l2 x Hin).
    - intros b2 l2 x Hin H63. apply c4_HRgrp in Hin.
      rewrite (MhAMetaN.e_gsc st L HWF c4_p c4_regions c4_brk c4_ac (sh + 1) (2 ^ 64 - 1) HP HPA) in H63 by exact (proj1 (wG_regions st L (WF_groups st L HWF) _ _ _ Hin)).
      exact (G63 b2 l2 x Hin H63).
    - intros b2 l2 e2 [E|Hin]; [unfold c4_Rn in E; injection E; intros <- <- <-; lia | exact (MT b2 l2 e2 Hin)].
    - unfold c4_regions. rewrite (count_kind_cons (fun k => match k with RMeta _ => true | _ => false end) c4_Rn). cbn [rg_kind c4_Rn]. lia.
    - unfold MhAMetaN.areas'. rewrite length_app. cbn [length]. unfold c4_brk.
      assert (CB : length (List.filter (fun x => match rg_kind x with RBrk => true | _ => false end) c4_regions)
                   = length (List.filter (fun x => match rg_kind x with RBrk => true | _ => false end) (s_regions st))).
      { unfold c4_regions. rewrite (count_kind_cons (fun k => match k with RBrk => true | _ => false end) c4_Rn). reflexivity. }
      rewrite CB. destruct (s_brk st) as [|x0 x1 g|g]; cbn [guard_kind].
      + split; [|exact I]. rewrite filter_all_false; [cbn; lia|]. intros r Hr. destruct r as [rb rl [|ex|y]]; [exfalso; exact (BRK rb rl Hr) | reflexivity | reflexivity].
      + destruct BRK as (BR1 & BR2 & BR3). split; [lia | right; exact BR3].
      + destruct BRK as [BR1 BR2]. split; [lia|]. destruct g as [[g0 gg]|]; [right; exact BR2 | exact I].
    - intros bb ll [E|Hin]; [unfold c4_Rn in E; discriminate E | exact (BL bb ll Hin)].
  Qed.

  Lemma c4_nr : iv_subtract (Z_to_bv 64 p0) (Z_to_bv 64 c4_N) (p0 + 4096) (p0 + 8192) = noacc_of_region c4_Rn.
  Proof.
    pose proof c4_N_rng as (N1 & N2 & N3). destruct Hp0 as (P1 & P2 & P3). ceil; unfold HEAPLO in P2, P3.
    unfold noacc_of_region, c4_Rn. cbn [rg_kind rg_base rg_len Z.eqb].
    unfold iv_subtract. rewrite !u64_lit by lia.
    rewrite (proj2 (Z.ltb_lt p0 (p0 + 4096))) by lia. rewrite Z.min_r by lia.
    replace (p0 + 4096 - p0) with 4096 by lia. cbn [app]. f_equal.
    replace (4096 * (1 + 1)) with 8192 by lia.
    destruct (Z_lt_le_dec 8192 c4_N) as [Hl|Hl].
    - rewrite !(proj2 (Z.ltb_lt _ _)) by lia. rewrite Z.max_r by lia. f_equal. f_equal; f_equal; lia.
    - rewrite !(proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
  Qed.

  Lemma c4_Hp_img : img_free c4_p (c4_p + 4096).
  Proof. pose proof c4_N_rng as (N1 & _). unfold img_free, c4_p. destruct Hp0img as [A|A]; [left | right]; lia. Qed.
  Lemma c4_t_wf_img : wf_img c4_st.
  Proof.
    pose proof (WF_img st L HWF) as [WA WR]. pose proof c4_N_rng as (N1 & _).
    constructor; cbn [s_areas s_regions c4_st MhAMetaN.st'].
    - intros a Ha. unfold MhAMetaN.areas' in Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [exact (WA a Ha) | exact c4_Hp_img].
    - intros r [<-|Hr]; [| exact (WR r Hr)]. unfold img_free, c4_Rn. cbn. destruct Hp0img as [A|A]; [left | right]; lia.
  Qed.



  Lemma c4_t_ledger : LEDGERX c4_st X c4_vm.
  Proof.
    pose proof c4_N_rng as (N1 & N2 & N3). destruct Hp0 as (P1 & P2 & P3). ceil; unfold HEAPLO in P2, P3.
    destruct HLG as [LM LN LB LR LMB]. constructor; cbn [vm_maps vm_noaccess vm_brk vm_start_brk vm_reserved vm_mmap_base s_regions s_brk c4_st MhAMetaN.st' c4_vm].
    - unfold c4_regions. cbn [map]. replace (region_entry c4_Rn) with (Z_to_bv 64 p0, Z_to_bv 64 c4_N) by reflexivity.
      eapply Permutation_trans; [apply perm_skip; exact LM|]. apply Permutation_middle.
    - rewrite maps_subtract_cons, c4_nr.
      unfold noacc_of. cbn [s_brk s_regions c4_st MhAMetaN.st'].
      change (guard_of c4_brk) with (guard_of (s_brk st)).
      change (flat_map noacc_of_region c4_regions) with (noacc_of_region c4_Rn ++ flat_map noacc_of_region (s_regions st)).
      eapply Permutation_trans; [|apply Permutation_app_swap_app]. apply Permutation_app_head.
      eapply Permutation_trans; [apply perm_maps_subtract; exact LN|]. unfold noacc_of. rewrite maps_subtract_app.
      rewrite (guard_subtract_apart st L HWF (p0 + 4096) (p0 + 8192) ltac:(lia)).
      2:{ intros b1 Hin. destruct (proj1 c4_apart _ Hin); cbn in *; lia. }
      apply Permutation_app_head. rewrite maps_subtract_flat_map.
      rewrite (flat_map_ext_In _ _ (fun x => maps_subtract (noacc_of_region x) (p0 + 4096) (p0 + 8192)) noacc_of_region (s_regions st)); [apply Permutation_refl|].
      intros r Hr. apply (nr_subtract_apart st L HWF r (p0 + 4096) (p0 + 8192) Hr ltac:(lia)). destruct (proj1 c4_apart r Hr); lia.
    - exact I.
    - exact LR.
    - exact LMB.
  Qed.

  Lemma c4_new_apart_X : forall r, In r c4_regions -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
    forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r).
  Proof.
    intros r [<-|Hr]; [right | left; exists r; split; [exact Hr | split; reflexivity]]. intros e He. destruct (proj2 c4_apart e He) as (ea & en & -> & X1 & X2 & X3 & X4 & D).
    exists ea, en. split; [reflexivity|]. cbn. repeat split; lia.
  Qed.
End C4.
