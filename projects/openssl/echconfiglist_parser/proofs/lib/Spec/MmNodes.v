(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mminv carries the channel reader; hint-0 mmap is placed by linux_place_is under place_declined_b; mmsafe gains munmap ledger-exactness and a vDSO/vvar-free mprotect range, with munmap re-proved via maps_subtract; mm_node_sound takes nret and proves RomBase.sys_rob); internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import AllocTop VmKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg RelSpec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require MmapSim.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Lemma w_is0_wz : forall z, 0 <= z < 2^64 -> w_is0 (Z_to_bv 64 z) = (z =? 0).
Proof.
  intros z Hz. unfold w_is0. destruct (Z.eqb_spec z 0) as [->|NE].
  - apply bv_eqb_eq. reflexivity.
  - destruct (bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0)) eqn:E; [|reflexivity]. exfalso.
    apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_wz in E by lia. lia.
Qed.

Lemma bv_eqb_unsigned : forall (a b : word), bv_eqb a b = (bv_unsigned a =? bv_unsigned b).
Proof.
  intros a b. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
  - apply bv_eqb_eq. apply bv_eq. exact E.
  - destruct (bv_eqb a b) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E. subst. apply NE. reflexivity.
Qed.

Lemma errno_ret_ENOMEM : bv_unsigned (errno_ret ENOMEM) = 2^64 - 12.
Proof. reflexivity. Qed.

(* 727298f3: write/writev to a channel read [m_channel_reader]; [init_model] seeds it from the
   launch's [in_channel_reader] and no mm step writes it, so the mm-node invariant carries it
   (as boost-beast/http_request's Spec/MmNodes.v). *)
Definition mminv (mo : Model) : Prop :=
  m_vm_lazy mo = [] /\ m_vm_materialized mo = [] /\ m_channel_reader mo = true.

Lemma mminv_reader : forall mo, mminv mo -> m_channel_reader mo = true.
Proof. intros mo (_ & _ & H). exact H. Qed.

Lemma mminv_lazy : forall mo, mminv mo -> m_vm_lazy mo = [].
Proof. intros mo [H _]. exact H. Qed.

Lemma vm_forget_range_id : forall lo hi m, mminv m -> vm_forget_range lo hi m = m.
Proof.
  intros lo hi [fd [maps lazy mat] io fs proc lim tm] [Hl [Hm _]]. cbn in Hl, Hm. subst.
  unfold vm_forget_range. cbn. reflexivity.
Qed.

Lemma forget_vm_ranges_id : forall us m, mminv m -> forget_vm_ranges us m = m.
Proof.
  intros us. induction us as [|[a n] us IH]; intros m Hm; [reflexivity|].
  cbn. rewrite vm_forget_range_id by exact Hm. apply IH. exact Hm.
Qed.

Lemma mminv_with_vmmaps : forall h m, mminv m -> mminv (with_vmmaps h m).
Proof.
  intros h [fd [maps lazy mat] io fs proc lim tm] [Hl [Hm Hr]]. cbn in Hl, Hm. subst.
  split; [reflexivity | split; [reflexivity | exact Hr]].
Qed.

Lemma m_halted_with_vmmaps : forall hh m, m_halted (with_vmmaps hh m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_brk_next_eq : forall mo req r, mminv mo ->
  with_brk_next mo req r = with_vmmaps (brk_model_next (m_vmmaps mo) req r) mo.
Proof. intros mo req r MI. unfold with_brk_next. apply forget_vm_ranges_id. apply mminv_with_vmmaps. exact MI. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live' : forall mo, mminv mo -> vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof. intros mo [Hl [Hm _]]. apply vm_backing_used_le_live; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition pgup (len : Z) : Z := page_round_up_Z len.

(* [comment removed for export] *)
Definition mmsafe (n : node) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  match n with
  | NBrk req => 0 <= req < 2^64
  | NMmap addr len prot flags =>
      (addr = 0 /\ flags = 34 /\ (prot = 3 \/ prot = 0) /\ 0 < len < 2^62)
      \/ (flags = 50 /\ prot = 0 /\ 0 < len < 2^62 /\ addr mod 4096 = 0 /\ 0 < addr
          /\ addr + pgup len <= alloc_top h
          /\ region_free (vm_reserved h) (wz addr) (wz (pgup len)) = true
          /\ map_contains (vm_maps h) (wz addr) (wz (pgup len)) = true)
  | NMunmap addr len =>
      addr mod 4096 = 0 /\ 0 <= addr /\ 0 < len /\ addr + pgup len <= TASK_SIZE
      /\ map_has (vm_maps h) (wz addr) (wz (pgup len)) = true
      (* 08b1429 cuts the range out of the ledger ([mmap_fixed_destroyed_next]); on a
         ledger whose entries are nonempty and miss the range unless they are the one
         entry, that is removing the entry ([MmapSim.maps_subtract_exact]) *)
      /\ (forall b s, In (b, s) (vm_maps h) -> 0 < bv_unsigned s)
      /\ (forall b s, In (b, s) (vm_maps h) -> b = wz addr -> s = wz (pgup len))
      /\ (forall b s, In (b, s) (vm_maps h) -> b <> wz addr ->
            bv_unsigned b + bv_unsigned s <= addr \/ addr + pgup len <= bv_unsigned b)
  | NMprotect addr len prot =>
      prot = 3 /\ addr mod 4096 = 0 /\ 0 <= addr /\ 0 < len /\ addr + pgup len < 2^64
      /\ map_contains (vm_noaccess h) (wz addr) (wz (pgup len)) = true
      /\ map_contains (vm_maps h) (wz addr) (wz (pgup len)) = true
      (* the revision's vDSO/vvar gate: a range meeting the pair is unmodeled,
         so the node only speaks about ranges that miss it (the MAP_FIXED mmap
         case above carries its reserved-freeness the same way) *)
      /\ region_free (vdso_reserved (m_kernel mo) (vdso_top h))
                     (wz addr) (wz (pgup len)) = true
  | _ => False
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pgup_range : forall len, 0 < len < 2^62 -> len <= pgup len < 2^63 /\ pgup len mod 4096 = 0.
Proof.
  intros len H. unfold pgup, page_round_up_Z, page_size.
  split; [| apply Z_mod_mult]. Z.div_mod_to_equations. lia.
Qed.

Lemma TASK_SIZE_val : TASK_SIZE = 2^47.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition brk_result (m : Model) (req : word) : word :=
  let h := m_vmmaps m in
  let b := vm_brk h in
  if w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk h)) then b
  else if Z.ltb (bv_unsigned req) (bv_unsigned b) then req
  else if brk_grow_ok m req req then req else b.

Lemma brk_grow_ok_same : forall m req, brk_grow_ok m req (vm_brk (m_vmmaps m)) = true.
Proof. intros m req. unfold brk_grow_ok. cbn zeta. rewrite Z.ltb_irrefl, Bool.andb_false_r. reflexivity. Qed.

Lemma brk_result_ok : forall m req, brk_r_ok m req (brk_result m req) = true.
Proof.
  intros m req. unfold brk_r_ok, brk_result. cbn zeta.
  destruct (w_is0 req || _) eqn:E1; [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))) eqn:E2; [rewrite bv_eqb_refl; reflexivity|].
  destruct (brk_grow_ok m req req) eqn:G.
  - rewrite bv_eqb_refl, G. reflexivity.
  - rewrite bv_eqb_refl, Bool.orb_true_r, brk_grow_ok_same. reflexivity.
Qed.

Lemma brk_result_cases : forall m req, brk_result m req = req \/ brk_result m req = vm_brk (m_vmmaps m).
Proof.
  intros m req. unfold brk_result. cbn zeta.
  destruct (w_is0 req || _); [right; reflexivity|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))); [left; reflexivity|].
  destruct (brk_grow_ok m req req); [left|right]; reflexivity.
Qed.

Lemma brk_result_query : forall m, brk_result m (wz 0) = vm_brk (m_vmmaps m).
Proof. intros m. unfold brk_result. cbn zeta. replace (w_is0 (wz 0)) with true by reflexivity. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_result_grow : forall m req,
  bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned (vm_brk (m_vmmaps m)) ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req ->
  brk_result m req = if brk_grow_ok m req req then req else vm_brk (m_vmmaps m).
Proof.
  intros m req Hsb Hlt. unfold brk_result, min_brk. cbn zeta.
  pose proof (bv_unsigned_in_range 64 req).
  replace (w_is0 req) with false.
  2:{ symmetry. unfold w_is0. rewrite bv_eqb_unsigned. apply Z.eqb_neq. rewrite unsigned_wz by lia.
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps m))). lia. }
  replace (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m))) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_not_enomem : forall hh (a : word) nZ, 0 < nZ -> bv_unsigned a + nZ <= alloc_top hh ->
  bv_eqb a (errno_ret ENOMEM) = false.
Proof.
  intros hh a nZ Hn Ha. rewrite bv_eqb_unsigned, errno_ret_ENOMEM. apply Z.eqb_neq.
  pose proof (alloc_top_room hh). unfold two_pow_64, stack_max_size in *. lia.
Qed.

Section Shapes.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variable mo : Model.
Let h := m_vmmaps mo.

(* [comment removed for export] *)

Lemma brk_refusal_result : forall req r,
  brk_r_ok mo req r = true ->
  (Run.brk_refusal_b mo req r = true /\
   exists r2, brk_r_ok mo req r2 = true /\ Run.brk_refusal_b mo req r2 = false) <->
  r <> brk_result mo req.
Proof.
  intros req r Hok. unfold Run.brk_refusal_b, brk_result. unfold brk_r_ok in Hok. cbn zeta in *.
  set (b := vm_brk (m_vmmaps mo)) in *.
  destruct (w_is0 req || _) eqn:E1.
  { (* [comment removed for export] *)
    apply bv_eqb_eq in Hok. subst r.
    assert (RF : negb (w_is0 req) && negb (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo))) = false).
    { apply Bool.orb_prop in E1. destruct E1 as [E1|E1]; rewrite E1; cbn; [reflexivity| apply Bool.andb_false_r]. }
    rewrite RF. cbn [andb]. split; [intros [F _]; discriminate F| intros NE; exfalso; apply NE; reflexivity]. }
  apply Bool.orb_false_iff in E1 as [E1a E1b]. rewrite E1a, E1b. cbn [negb andb].
  assert (OKEQ : forall r2, brk_r_ok mo req r2 = (if bv_unsigned req <? bv_unsigned b then bv_eqb r2 req || bv_eqb r2 b else (bv_eqb r2 req || bv_eqb r2 b) && brk_grow_ok mo req r2)).
  { intros r2. unfold brk_r_ok. cbn zeta. fold b. rewrite E1a, E1b. reflexivity. }
  destruct (bv_unsigned req <? bv_unsigned b) eqn:E2.
  { (* [comment removed for export] *)
    assert (NE : bv_eqb req b = false).
    { rewrite bv_eqb_unsigned. apply Z.eqb_neq. apply Z.ltb_lt in E2. lia. }
    rewrite NE. cbn [negb andb].
    apply Bool.orb_prop in Hok. destruct Hok as [Hr|Hr]; apply bv_eqb_eq in Hr; subst r.
    - rewrite NE. split; [intros [F _]; discriminate F| intros F; exfalso; apply F; reflexivity].
    - rewrite bv_eqb_refl. split.
      + intros _ E. apply (f_equal bv_unsigned) in E. apply Z.ltb_lt in E2. lia.
      + intros _. split; [reflexivity|]. exists req. rewrite OKEQ, bv_eqb_refl, NE. split; reflexivity. }
  (* [comment removed for export] *)
  apply andb_prop in Hok as [Hr G].
  destruct (bv_eqb req b) eqn:E3.
  { (* [comment removed for export] *)
    cbn [negb andb].
    assert (r = req) as ->.
    { apply bv_eqb_eq in E3. apply Bool.orb_prop in Hr. destruct Hr as [Hr|Hr]; apply bv_eqb_eq in Hr; congruence. }
    apply bv_eqb_eq in E3. rewrite <- E3.
    destruct (brk_grow_ok mo req req); (split; [intros [F _]; discriminate F| intros F; exfalso; apply F; reflexivity]). }
  cbn [negb andb].
  apply Bool.orb_prop in Hr. destruct Hr as [Hr|Hr]; apply bv_eqb_eq in Hr; subst r.
  - (* [comment removed for export] *) rewrite G, E3. split; [intros [F _]; discriminate F| intros F; exfalso; apply F; reflexivity].
  - (* [comment removed for export] *) rewrite bv_eqb_refl. destruct (brk_grow_ok mo req req) eqn:G2.
    + split.
      * intros _ E. rewrite <- E in E3. rewrite bv_eqb_refl in E3. discriminate.
      * intros _. split; [reflexivity|]. exists req. rewrite OKEQ, bv_eqb_refl, G2, E3. split; reflexivity.
    + split; [| intros F; exfalso; apply F; reflexivity].
      intros [_ (r2 & Hok2 & NR)]. rewrite OKEQ in Hok2.
      apply andb_prop in Hok2 as [Hr2 G3]. apply Bool.orb_prop in Hr2.
      destruct Hr2 as [Hr2|Hr2]; apply bv_eqb_eq in Hr2; subst r2.
      * rewrite G2 in G3. discriminate.
      * rewrite bv_eqb_refl in NR. discriminate.
Qed.

Lemma nstep_brk_iff : forall req eff mo' evs, 0 <= req < 2^64 ->
  nstep (NBrk req) mo eff mo' evs <->
  evs = [] /\ let r := brk_result mo (wz req) in
        eff = mkEffectU r [] (brk_zeros (wz req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] []
        /\ mo' = with_brk_next mo (wz req) r.
Proof.
  intros req eff mo' evs Hr. cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 214 [Z_to_bv 64 req])) = 214) by reflexivity.
  rewrite (syscall_spec_214 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  rewrite (brk_outcome _ _ mo _). fold (wz req). subst h.
  assert (SPUR : forall r, brk_r_ok mo (wz req) r = true ->
    Run.spurious_refusal_cfg the_scfg (pure_input 214 [wz req]) mo
       (mkEffectU r [] (brk_zeros (wz req) r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
    <-> r <> brk_result mo (wz req)).
  { intros r Hok. rewrite <- (brk_refusal_result (wz req) r Hok). unfold Run.spurious_refusal_cfg.
    rewrite !(refusal_b_brk _ _ _ SN). cbn [in_arg in_args nth pure_input eff_ret]. split.
    - intros (_ & RB & (eff' & m' & evs' & SP & NR)). split; [exact RB|].
      apply (proj1 (syscall_spec_214 _ mo _ SN)) in SP. cbn [in_arg in_args nth pure_input] in SP. apply brk_outcome in SP as (r' & Hok' & E).
      apply Ok_inj in E as (-> & _ & _). rewrite (refusal_b_brk _ _ _ SN) in NR. cbn [in_arg in_args nth pure_input eff_ret] in NR.
      exists r'. auto.
    - intros (RB & (r2 & Hok2 & NR)). split; [apply family_off_brk_true; exact SN|]. split; [exact RB|].
      eexists (mkEffectU r2 [] (brk_zeros (wz req) r2 (vm_brk (m_vmmaps mo))) (brk_unmaps r2 (vm_brk (m_vmmaps mo))) [] []), _, [].
      split; [| rewrite (refusal_b_brk _ _ _ SN); cbn [in_arg in_args nth pure_input eff_ret]; exact NR].
      apply (syscall_spec_214 _ mo _ SN). cbn [in_arg in_args nth pure_input]. apply brk_outcome. exists r2. auto. }
  split.
  - intros [-> ((r & Hok & E) & NS)]. apply Ok_inj in E as (-> & -> & _). split; [reflexivity|].
    enough (r = brk_result mo (wz req)) as <- by (split; reflexivity).
    destruct (bv_eq_dec _ r (brk_result mo (wz req))) as [E|NE]; [exact E|]. exfalso. apply NS.
    apply (SPUR r Hok). exact NE.
  - intros (-> & -> & ->). split; [reflexivity|]. split.
    + exists (brk_result mo (wz req)). split; [apply brk_result_ok| reflexivity].
    + intros SP. apply (SPUR _ (brk_result_ok mo (wz req))) in SP. apply SP. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_off0 : mmap_off_aligned_b (wz 0) = true. Proof. reflexivity. Qed.
Lemma mmap_anon_34 : mmap_anon_b (wz 34) = true. Proof. reflexivity. Qed.
Lemma mmap_anon_50 : mmap_anon_b (wz 50) = true. Proof. reflexivity. Qed.
Lemma mmap_modeled_rw : mmap_modeled_b (wz 3) (wz 34) (wz 0) = true. Proof. reflexivity. Qed.
Lemma mmap_modeled_na : mmap_modeled_b (wz 0) (wz 34) (wz 0) = false. Proof. reflexivity. Qed.
Lemma mmap_noaccess_na : mmap_noaccess_b (wz 0) (wz 34) (wz 0) = true. Proof. reflexivity. Qed.
Lemma mmap_modeled_fx : mmap_modeled_b (wz 0) (wz 50) (wz 0) = false. Proof. reflexivity. Qed.
Lemma mmap_noaccess_fx : mmap_noaccess_b (wz 0) (wz 50) (wz 0) = false. Proof. reflexivity. Qed.
Lemma mmap_fixedna_fx : mmap_fixed_noaccess_b (wz 0) (wz 50) (wz 0) = true. Proof. reflexivity. Qed.
Lemma with_mmap_backing_34 : forall a n m, with_mmap_backing (wz 34) a n m = m. Proof. reflexivity. Qed.
Lemma with_mmap_backing_50 : forall a n m, with_mmap_backing (wz 50) a n m = m. Proof. reflexivity. Qed.

(* The model places a hint-0 grant by Linux's rule ([Placement.linux_place_is]); the four
   admissibility facts are kept beside it because every consumer reads them. *)
Definition mmap_grant_conds (a : word) (nZ : Z) : Prop :=
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h
  /\ region_free (vm_reserved h ++ vm_maps h) a (wz nZ) = true
  /\ linux_place_is h (kb_thp (m_kernel mo)) (wz 0) nZ a = true.

Lemma mmap_grant_conds_of_place : forall a nZ, 0 < nZ -> nZ mod page_size = 0 ->
  linux_place_is h (kb_thp (m_kernel mo)) (wz 0) nZ a = true -> mmap_grant_conds a nZ.
Proof.
  intros a nZ Hn Hal Hp. pose proof (linux_place_is_admissible _ _ _ _ _ Hn Hal Hp) as (C1 & C2 & C3 & C4).
  unfold mmap_grant_conds, wz. auto.
Qed.

Definition mmap_rw_model (a : word) (nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, wz nZ) :: vm_maps h) (vm_noaccess h)
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.
Definition mmap_na_model (a : word) (nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, wz nZ) :: vm_maps h) ((a, wz nZ) :: vm_noaccess h)
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma nstep_mmap_rw_iff : forall len eff mo' evs, 0 < len < 2^62 ->
  let nZ := pgup len in
  nstep (NMmap 0 len 3 34) mo eff mo' evs <->
  evs = [] /\
  ((eff = efferr ENOMEM /\ mo' = mo
    /\ ~ (exists a, mmap_grant_conds a nZ /\ vm_backing_used mo + nZ <= vm_limit h))
   \/ (exists a, mmap_grant_conds a nZ /\ (vm_backing_used mo + nZ <= vm_limit h)
                 /\ eff = mkEffect a [] [(a, wz nZ)] /\ mo' = mmap_rw_model a nZ)).
Proof.
  intros len eff mo' evs Hl nZ. pose proof (pgup_range len Hl) as [PG1 PG2]. fold nZ in PG1, PG2.
  assert (HnP : 0 < nZ) by lia.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 3; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  rewrite (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mmap_spec _ _ _ _ _ _ ?i mo _] =>
  pose proof (fun o => mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) i mo o
                mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw
                ltac:(apply place_declined_b_null)) as R end.
  cbv zeta in R. unfold wz at 2 in R. rewrite unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  setoid_rewrite mmap_err_out_enomem in R.
  assert (BK : forall m, mmap_noreserve_backed_ok (wz 34) m nZ = (vm_backing_used m + nZ <=? vm_limit (m_vmmaps m))) by reflexivity.
  unfold wz in R, BK |- *. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 3; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mmap. exact SN. }
  unfold mmap_grant_conds, mmap_rw_model. subst h.
  change (with_mmap_backing (Z_to_bv 64 34)) with (with_mmap_backing (wz 34)) in R |- *. rewrite ?with_mmap_backing_34 in R; rewrite ?with_mmap_backing_34.
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|(a & (Hpl & C5) & E)].
    + apply Ok_inj in E as (-> & -> & _). left. split; [reflexivity|]. split; [reflexivity|].
      intros (a & (C1 & C2 & C3 & C4 & Hpl) & C5). apply NS. split; [apply family_off_mmap_true; exact SN|].
      rewrite !RB. cbn [eff_ret]. split; [apply bv_eqb_refl|].
      eexists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), _, []. split.
      * apply (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input]. apply R. right. exists a.
        split; [| reflexivity]. rewrite BK. split; [exact Hpl|]. apply Z.leb_le. exact C5.
      * cbn [eff_ret]. rewrite RB. eapply grant_not_enomem; [| exact C3]. lia.
    + apply Ok_inj in E as (-> & -> & _). right. exists a. rewrite BK in C5. apply Z.leb_le in C5.
      destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
      repeat split; auto.
  - intros (-> & HO). split; [reflexivity|].
    destruct HO as [(-> & -> & NG)|(a & (C1 & C2 & C3 & C4 & Hpl) & C5 & -> & ->)].
    + split; [left; reflexivity|].
      intros (_ & _ & (eff2 & m2 & evs2 & SP & NR)). apply NG.
      apply (syscall_spec_222 _ mo _ SN) in SP. cbn [in_arg in_args nth pure_input] in SP. apply (proj1 (R _)) in SP.
      destruct SP as [E|(a & (Hpl & C5) & E)]; apply Ok_inj in E as (-> & _ & _); cbn [eff_ret] in NR.
      * rewrite RB, bv_eqb_refl in NR. discriminate.
      * exists a. rewrite BK in C5. apply Z.leb_le in C5.
        destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
        repeat split; auto.
    + split.
      * right. exists a. split; [| reflexivity]. rewrite BK. split; [exact Hpl|]. apply Z.leb_le. exact C5.
      * intros (_ & RF & _). rewrite RB in RF. cbn [eff_ret] in RF. rewrite (grant_not_enomem (m_vmmaps mo) a nZ) in RF by lia. discriminate.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_na_iff : forall len eff mo' evs, 0 < len < 2^62 ->
  let nZ := pgup len in
  nstep (NMmap 0 len 0 34) mo eff mo' evs <->
  evs = [] /\
  ((eff = efferr ENOMEM /\ mo' = mo /\ ~ (exists a, mmap_grant_conds a nZ))
   \/ (exists a, mmap_grant_conds a nZ
                 /\ eff = mkEffectU a [] [] [(a, wz nZ)] [] [] /\ mo' = mmap_na_model a nZ)).
Proof.
  intros len eff mo' evs Hl nZ. pose proof (pgup_range len Hl) as [PG1 PG2]. fold nZ in PG1, PG2.
  assert (HnP : 0 < nZ) by lia.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  rewrite (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mmap_spec _ _ _ _ _ _ ?i mo _] =>
  pose proof (fun o => mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) i mo o
                mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na
                ltac:(apply place_declined_b_null)) as R end.
  cbv zeta in R. unfold wz at 2 in R. rewrite unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  setoid_rewrite mmap_err_out_enomem in R.
  unfold wz in R |- *. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mmap. exact SN. }
  unfold mmap_grant_conds, mmap_na_model. subst h.
  change (with_mmap_backing (Z_to_bv 64 34)) with (with_mmap_backing (wz 34)) in R |- *. rewrite ?with_mmap_backing_34 in R; rewrite ?with_mmap_backing_34.
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|(a & Hpl & E)].
    + apply Ok_inj in E as (-> & -> & _). left. split; [reflexivity|]. split; [reflexivity|].
      intros (a & (C1 & C2 & C3 & C4 & Hpl)). apply NS. split; [apply family_off_mmap_true; exact SN|].
      rewrite !RB. cbn [eff_ret]. split; [apply bv_eqb_refl|].
      eexists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []), _, []. split.
      * apply (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input]. apply R. right. exists a.
        split; [exact Hpl| reflexivity].
      * cbn [eff_ret]. rewrite RB. eapply grant_not_enomem; [| exact C3]. lia.
    + apply Ok_inj in E as (-> & -> & _). right. exists a.
      destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
      repeat split; auto.
  - intros (-> & HO). split; [reflexivity|].
    destruct HO as [(-> & -> & NG)|(a & (C1 & C2 & C3 & C4 & Hpl) & -> & ->)].
    + split; [left; reflexivity|].
      intros (_ & _ & (eff2 & m2 & evs2 & SP & NR)). apply NG.
      apply (syscall_spec_222 _ mo _ SN) in SP. cbn [in_arg in_args nth pure_input] in SP. apply (proj1 (R _)) in SP.
      destruct SP as [E|(a & Hpl & E)]; apply Ok_inj in E as (-> & _ & _); cbn [eff_ret] in NR.
      * rewrite RB, bv_eqb_refl in NR. discriminate.
      * exists a. destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
        repeat split; auto.
    + split.
      * right. exists a. split; [exact Hpl| reflexivity].
      * intros (_ & RF & _). rewrite RB in RF. cbn [eff_ret] in RF. rewrite (grant_not_enomem (m_vmmaps mo) a nZ) in RF by lia. discriminate.
Qed.

(* [comment removed for export] *)
Definition mmap_fx_model (addr nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                 ((wz addr, wz nZ) :: maps_subtract (vm_noaccess h) addr (addr + nZ))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma nstep_mmap_fixed_iff : forall addr len eff mo' evs,
  mminv mo -> mmsafe (NMmap addr len 0 50) mo ->
  let nZ := pgup len in
  nstep (NMmap addr len 0 50) mo eff mo' evs <->
  evs = [] /\ eff = mkEffectU (wz addr) [] [] [(wz addr, wz nZ)] [] [] /\ mo' = mmap_fx_model addr nZ.
Proof.
  intros addr len eff mo' evs MI SF nZ.
  destruct SF as [(_ & F & _)|(_ & _ & Hl & AL & A0 & AC & RF & MC)]; [discriminate F|].
  pose proof (pgup_range len Hl) as [PG1 PG2]. fold nZ in PG1, PG2, AC, RF, MC.
  pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  rewrite (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mmap_spec _ _ _ _ _ _ ?i mo _] =>
  pose proof (fun o => mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) i mo o
                mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx) as R end.
  cbv zeta in R. unfold wz in R. rewrite !unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  pose proof (fun o => R o AC ltac:(unfold page_size; exact AL) A0 RF MC) as R2. clear R. rename R2 into R.
  setoid_rewrite mmap_err_out_enomem in R.
  unfold wz. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mmap. exact SN. }
  unfold mmap_fx_model. subst h. unfold with_mmap_replacement in R |- *.
  change (with_mmap_backing (Z_to_bv 64 50)) with (with_mmap_backing (wz 50)) in R |- *.
  rewrite ?with_mmap_backing_50 in R. rewrite ?with_mmap_backing_50.
  rewrite vm_forget_range_id in R by exact MI. rewrite vm_forget_range_id by exact MI.
  rewrite !unsigned_wz in R by lia. rewrite !unsigned_wz by lia.
  assert (OKNR : Run.refusal_b (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo (Z_to_bv 64 addr) = false).
  { rewrite RB. rewrite bv_eqb_unsigned, errno_ret_ENOMEM, unsigned_wz by lia. apply Z.eqb_neq. lia. }
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|[E|(e & He & E)]].
    + exfalso. apply Ok_inj in E as (-> & -> & _). apply NS. split; [apply family_off_mmap_true; exact SN|].
      split; [rewrite RB; apply bv_eqb_refl|]. eexists _, _, [].
      split; [apply (syscall_spec_222 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; left; reflexivity | exact OKNR].
    + apply Ok_inj in E as (-> & -> & _). auto.
    + exfalso. apply Ok_inj in E as (-> & -> & _). apply NS. split; [apply family_off_mmap_true; exact SN|].
      unfold mmap_errnos in He. destruct He as [<-|[]].
      split; [rewrite RB; apply bv_eqb_refl|]. eexists _, _, [].
      split; [apply (syscall_spec_222 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; left; reflexivity | exact OKNR].
  - intros (-> & -> & ->). split; [reflexivity|]. split; [right; left; reflexivity|].
    intros (_ & RF2 & _). cbn [eff_ret] in RF2. rewrite OKNR in RF2. discriminate.
Qed.

(* [comment removed for export] *)
Definition munmap_model (addr nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (wz addr))
                 (maps_subtract (vm_noaccess h) addr (addr + nZ))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma nstep_munmap_iff : forall addr len eff mo' evs,
  mminv mo -> mmsafe (NMunmap addr len) mo ->
  let nZ := pgup len in
  nstep (NMunmap addr len) mo eff mo' evs <->
  evs = [] /\ eff = mkEffectU (wz 0) [] [] [(wz addr, wz nZ)] [] [] /\ mo' = munmap_model addr nZ.
Proof.
  intros addr len eff mo' evs MI (AL & A0 & Hl & AH & MH & Mpos & Muniq & Mdisj) nZ.
  assert (PG : len <= nZ /\ nZ mod 4096 = 0) by (unfold nZ, pgup, page_round_up_Z, page_size; split; [Z.div_mod_to_equations; lia| apply Z_mod_mult]).
  fold nZ in AH, MH. rewrite TASK_SIZE_val in AH.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])) = 215) by reflexivity.
  rewrite (syscall_spec_215 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [munmap_spec _ _ ?i mo _] =>
  pose proof (fun o => munmap_exact_outcome (wz addr) (wz len) i mo o
                ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)) as R end.
  cbv zeta in R. unfold wz at 1 2 4 6 7 9 10 in R. rewrite !unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  specialize (fun o => R o ltac:(rewrite TASK_SIZE_val; lia) MH) as R'. clear R. rename R' into R.
  assert (MSX : maps_subtract (vm_maps (m_vmmaps mo)) addr (addr + nZ) = map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)).
  { pose proof (MmapSim.maps_subtract_exact (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) as E.
    rewrite !unsigned_wz in E by lia. apply E.
    - lia.
    - exact Mpos.
    - exact Muniq.
    - intros b s Hin Hne. pose proof (Mdisj b s Hin Hne) as Hd. exact Hd. }
  unfold wz in R |- *. rewrite R. unfold munmap_model, with_mmap_destroyed. subst h.
  (* The MUNMAP_AFTER_UNFOLD probe stood here and is deleted: Main's gate is a delta
     against origin/main for print-only lines that run on EVERY GREEN BUILD, and this one
     had no enclosing combinator, so it ran on green and was owed.  It earned its keep
     first -- a farm round printed the goal at exactly this point and
     REFUTED the hypothesis the comment here used to carry (that some name resolved
     somewhere untraced): munmap_model had unfolded correctly all along, and the real
     defect was two bullets below, in a bridge that was never crossed.  A probe that
     refutes its author is worth the round it costs.
     The three guarded printers at the end of this proof STAY: each is the last arm of a
     `solve [...] || solve [...] || … || idtac` chain with no outer recovery, so on a green
     build a solve closes the goal and none of them is reachable.  Main, on exactly this:
     "a guarded printer that runs only on the failure path prints nothing on green and is
     NOT a probe". *)
  (* [rewrite !unsigned_wz] asserted at least one occurrence of
     [bv_unsigned (Z_to_bv 64 ?z)] in the goal and the build reports none.  The
     discriminator for the three causes of "Found no subterm" says to read what the GOAL
     carries: the SAME lemma, this file's own :24 keyed to the unfolded [Z_to_bv 64 z],
     rewrites cleanly in E four lines above, so the name is right and the cone is right -
     the occurrence moved out of the goal, between [unfold wz in R |- *] at :496 and here.
     Note this tree vendors FOUR [wz] (Agent/MallocRep.v:48, Lib/TacX.v:14, Spec/KInv.v:166,
     Spec/MmNodes.v:80) and TWO [unsigned_wz] - :24 keyed to [Z_to_bv 64 z] and
     Spec/KStep.v:50 keyed to the FOLDED [wz z] - so the two are convertible and only one
     matches syntactically.
     [?] states the weaker thing that is true.  It is not a suppression: the [split],
     [Ok_inj] and [MSX] steps immediately below consume the normalised shape, so if the
     rewrite were load-bearing they fail here, in this file, rather than silently. *)
  rewrite vm_forget_range_id by (apply mminv_with_vmmaps; exact MI). rewrite ?unsigned_wz by lia.
  rewrite ?MSX.
  (* LPS revision repair.  At 75d69e00 `munmap_spec`'s outcome is a DISJUNCTION - the
     injected-errno arm beside the success arm - and `munmap_exact_outcome`
     (RelSpec.v:391-401) states it that way, so after `rewrite R` the forward hypothesis is
       (exists e, In e munmap_errnos /\ Ok eff mo' [] = Ok (mkEffect (errno_ret e) [] []) mo [])
       \/ Ok eff mo' [] = Ok (mkEffectU ...) (...) []
     and `Ok_inj` was being applied to a `\/`.  The errno arm is RULED OUT, not assumed
     away: the third conjunct of `nstep` is the not-spurious premise, which the old
     `intros [-> [E _]]` discarded, and an injected ENOMEM on a syscall whose family is
     forced off IS spurious.  Structure taken from the mmap sibling of this same file at
     :450-462, which is already on this shape; only the arm count (two, not three), the
     syscall number and the success return differ.  `munmap_errnos` is `[ENOMEM]`
     (75d69e00 Sys/Mm/Mmap.v:2735), the same singleton as `mmap_errnos`. *)
  assert (RBu : forall ret, Run.refusal_b (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo ret
                            = bv_eqb ret (errno_ret ENOMEM))
    by (intros ret; apply refusal_b_munmap; exact SN).
  assert (OKNRu : Run.refusal_b (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo (Z_to_bv 64 0) = false).
  { rewrite RBu. rewrite bv_eqb_unsigned, errno_ret_ENOMEM, unsigned_wz by lia. apply Z.eqb_neq. lia. }
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [(e & He & E)|E].
    + exfalso. apply Ok_inj in E as (-> & -> & _). apply NS.
      split; [apply family_off_munmap_true; exact SN|].
      unfold munmap_errnos in He. destruct He as [<-|[]].
      split; [rewrite RBu; apply bv_eqb_refl|]. eexists _, _, [].
      split; [apply (syscall_spec_215 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; reflexivity
             | exact OKNRu].
    + (* The SUCCESS arm.  The mmap sibling closes the matching goal with [auto] at :456,
         and here [auto] does not: this bullet is what a farm round
         reported, as "[Focus] Wrong bullet -: Current bullet + is not finished" at :539,
         the line AFTER it.  The cause is upstream of this line and is recorded at
         :497-509: [rewrite !unsigned_wz] was weakened to [rewrite ?unsigned_wz] when an
         occurrence moved, so the goal is no longer normalised the way the mmap path's is
         -- and unlike :446, :510 rewrites [vm_forget_range_id] only in the GOAL and not
         in [R].  So the two sides are convertible but may not be in the shape [auto]'s
         [eq_refl] hint reaches.
         The three attempts below are ordered cheapest-first, and the LAST one does not
         close the goal: it PRINTS it.  That is deliberate.  A wrong guess here costs a
         whole farm round to learn nothing, whereas a printed residual names the true
         shape in the same round that tests the guesses. *)
      apply Ok_inj in E as (-> & -> & _).
      (* THE FIX, and it is one tactic, because the lemma this arm needs was ALREADY
         PROVED eleven lines above.  [MSX] at :489 is exactly
           maps_subtract (vm_maps (m_vmmaps mo)) addr (addr + nZ)
             = map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)
         discharged from [MmapSim.maps_subtract_exact] with all four of its hypotheses --
         [0 < n], [Mpos], [Muniq] and [Mdisj].  :523's [rewrite ?MSX] then does NOTHING,
         because [Sys/Mm/Mmap.mmap_fixed_destroyed_next] is never unfolded, so [MSX]'s
         left-hand pattern is not present SYNTACTICALLY: the goal still carries
         [mmap_fixed_destroyed_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)] whole.
         The [?] made the no-op silent.  Unfolding it exposes
         [maps_subtract (vm_maps _) (bv_unsigned (Z_to_bv 64 addr)) (…)], which
         [unsigned_wz] normalises to [MSX]'s left side, and then both sides are
         [map_remove] and the goal closes.

         So the #38 repair here was never a restatement of [munmap_model].  I tried that
         (maps_subtract in the definition) and it was BACKWARDS: the bridge
         runs the other way, carrying the MODEL's [maps_subtract] DOWN to the [map_remove]
         this file's proof normalises to, and RefNodes.v:547 says so.  Reverted.
         The donor at RefNodes.v:539 restates the MmapSim TWIN, which is
         stated over a general ledger and carries no exactness hypothesis; this definition
         sits behind one that [mmsafe] supplies.  A donor is a donor PER HUNK.

         `auto` NEVER FAILS, so the earlier `first [auto | ...]` form always took branch
         one and its alternatives were dead -- which is why two rounds reported the same
         unfinished bullet and printed NOTHING.  `solve [t]` fails unless `t` closes the
         goal, so the chain below really is a chain.  Its last alternative used to PRINT the
         residual goal (a diagnostic, removed once the chain closed every goal); that print
         showed the right-hand side already in its restated form, which pointed here. *)
      (* [apply Ok_inj in E] already happened at :563; E is consumed. *)
      solve [ unfold mmap_fixed_destroyed_next; rewrite ?unsigned_wz by lia;
              rewrite ?MSX; split; reflexivity ]
      (* The `in *` alternative is GONE, and a farm round is why.  It
         closed the bullet -- `[Focus] Wrong bullet` at :591 became a TYPE error at :601,
         so the arm now finishes and what fails is inside it -- but `unfold … in *` and
         `rewrite … in *` touch the HYPOTHESES, including R and MSX themselves, and
         `solve [t]` does not catch an ELABORATION error the way it catches a tactic
         failure.  That is the `unfold mkEffectU` lesson a second time: a failing
         alternative must fail as a TACTIC to be skipped.  Goal-only forms cannot do it. *)
      || solve [ auto ].
  (* THE BACKWARD BULLET, and a farm round located it rather than my
     guessing.  Its error was at c.65-76 of this line -- `reflexivity|` inside
     [split; [right; reflexivity|]] -- NOT in the success arm above, which therefore sits
     above the first error and is CERTIFIED by that round: Rocq elaborates sequentially,
     so the [unfold mmap_fixed_destroyed_next] repair is measured, not argued.

     [right] is correct and is not the defect.  [RelSpec.v:391-401] puts the injected-errno
     arm LEFT and the success arm RIGHT, which is how the forward bullet at :538 destructures
     it ([(e & He & E)|E]).  What fails is the [reflexivity] after it, for the SAME reason
     the forward arm failed: the model side carries [mmap_fixed_destroyed_next … ] whole
     while [munmap_model] is in its [map_remove] normal form, and [MSX] cannot fire against
     an application that was never unfolded.  Same bridge, same lemma, other direction.

     I am NOT flipping [right] to [left].  A two-element disjunction makes a guess look like
     a diagnosis, and "a positional application tells you its next defect" has a two-element
     form that is simply a coin flip.  The chain below crosses the bridge, or closes the goal
     by reflexivity. *)
  - intros (-> & -> & ->). split; [reflexivity|]. split;
      [ solve [ right; unfold mmap_fixed_destroyed_next; rewrite ?unsigned_wz by lia;
                rewrite ?MSX; reflexivity ]
        || solve [ right; reflexivity ]
      |].
    (* `injected_arm_none_215` DOES NOT EXIST AND CANNOT, and that is the #38 finding here.
       A farm round: "The variable injected_arm_none_215 was not found in
       the current environment" -- the ABSENCE clause, in my own file.  Scfg.v carries
       `injected_arm_none_` for 29, 57, 63, 66, 93, 94 and 96 only; 215 is
         Scfg.v:28  injected_arm_215 : Run.injected_arm 215
                      = Some (Run.mkInjectedArm 215 Run.FamAlloc [ENOMEM])
       so munmap HAS an injected arm at this revision and `not_spurious_none` -- which
       wants `injected_arm … = None` (Scfg.v:45) -- is unavailable for it by construction.
       This is the other half of's subject: that commit made munmap's outcome a
       DISJUNCTION because the errno arm exists, and left behind a not-spurious proof that
       was only valid while it did not.  (LazyNodes.v:1845 spells the same missing name and
       is behind the frontier; flagged, not touched -- not my file.)

       The route that IS available is this lemma's own forward bullet at :545, which is
       ABOVE this line and therefore certified by the round that stopped here:
         apply family_off_munmap_true; exact SN      (Scfg.v:158, {AF : AllocForced SC})
       `Run.spurious_refusal_cfg` is `injected_family_off /\ refusal_b … /\ exists …`
       (:702-704), so family-off does NOT discharge it -- it SATISFIES one conjunct.  The
       contradiction has to come from `refusal_b`: this is the SUCCESS outcome, eff_ret 0,
       and a return of 0 is not a refusal.  The chain tries that, then the forms the mmap
       and mprotect siblings use at :453 and :671. *)
    solve [ intros (FO & RF & _); rewrite SN in RF; vm_compute in RF; discriminate RF ]
    || solve [ apply not_spurious_none; rewrite SN; reflexivity ]
    || solve [ intros (FO & RF & _); rewrite RBu in RF; cbn [eff_ret] in RF; discriminate RF ].
Qed.

(* [comment removed for export] *)
Definition mprotect_model (addr nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
                 (maps_subtract (vm_noaccess h) addr (addr + nZ))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma mprotect_gc3 : mprotect_grows_conflict_b (wz 3) = false. Proof. reflexivity. Qed.
Lemma mprotect_mod3 : mprotect_modeled_b (wz 3) = true. Proof. reflexivity. Qed.

Lemma nstep_mprotect_iff : forall addr len eff mo' evs,
  mmsafe (NMprotect addr len 3) mo ->
  let nZ := pgup len in
  nstep (NMprotect addr len 3) mo eff mo' evs <->
  evs = [] /\
  ((mprotect_budget_ok mo (wz addr) (wz nZ) = false /\ eff = efferr ENOMEM /\ mo' = mo)
   \/ (mprotect_budget_ok mo (wz addr) (wz nZ) = true /\ eff = mkEffect (wz 0) [] [(wz addr, wz nZ)] /\ mo' = mprotect_model addr nZ)).
Proof.
  intros addr len eff mo' evs (_ & AL & A0 & Hl & AH & NC & MC & VD) nZ.
  assert (PG : len <= nZ /\ nZ mod 4096 = 0) by (unfold nZ, pgup, page_round_up_Z, page_size; split; [Z.div_mod_to_equations; lia| apply Z_mod_mult]).
  fold nZ in AH, NC, MC, VD.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 3])) = 226) by reflexivity.
  rewrite (syscall_spec_226 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mprotect_spec _ _ _ ?i mo _] =>
  pose proof (fun o => mprotect_expose_outcome (wz addr) (wz len) (wz 3) i mo o mprotect_gc3
                ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)) as R end.
  cbv zeta in R. unfold wz at 1 2 4 6 7 9 12 13 in R. rewrite !unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  specialize (fun o => R o ltac:(unfold two_pow_64; lia) mprotect_mod3 VD NC MC) as R'. clear R. rename R' into R.
  setoid_rewrite mprotect_err_out_enomem in R.
  unfold wz in R |- *. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 3]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mprotect. exact SN. }
  assert (OKNR : bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM) = false) by reflexivity.
  unfold mprotect_model, mprotect_model_next. subst h. rewrite !unsigned_wz by lia.
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|(B & E)]; apply Ok_inj in E as (-> & -> & _).
    + left. destruct (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:B; [| auto].
      exfalso. apply NS. split; [apply family_off_mprotect_true; exact SN|]. split; [rewrite RB; apply bv_eqb_refl|].
      eexists _, _, [].
      split; [apply (syscall_spec_226 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; split; [reflexivity || exact B| reflexivity]
            | rewrite RB; cbn [eff_ret]; exact OKNR].
    + right. auto.
  - intros (-> & HO). split; [reflexivity|].
    destruct HO as [(B & -> & ->)|(B & -> & ->)].
    + split; [left; reflexivity|].
      intros (_ & _ & (eff' & m' & evs' & SP & NR)).
      apply (syscall_spec_226 _ mo _ SN) in SP. cbn [in_arg in_args nth pure_input] in SP. apply (proj1 (R _)) in SP.
      destruct SP as [E|(B' & E)]; apply Ok_inj in E as (-> & _ & _); cbn [eff_ret] in NR.
      * rewrite RB, bv_eqb_refl in NR. discriminate.
      * rewrite B in B'. discriminate.
    + split; [right; split; [exact B| reflexivity]|].
      intros (_ & RF & _). rewrite RB in RF. cbn [eff_ret] in RF. rewrite OKNR in RF. discriminate.
Qed.
End Shapes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma spurious_refusal_iff : forall cfg i i' m eff,
  in_sysno i = in_sysno i' -> in_arg i 0 = in_arg i' 0 ->
  (forall o, syscall_spec i m o <-> syscall_spec i' m o) ->
  Run.spurious_refusal_cfg cfg i m eff <-> Run.spurious_refusal_cfg cfg i' m eff.
Proof.
  intros cfg i i' m eff Hno Ha0 Hsp.
  assert (RB : forall ret, Run.refusal_b i m ret = Run.refusal_b i' m ret).
  { intros ret. unfold Run.refusal_b. rewrite Hno, Ha0. reflexivity. }
  assert (FO : Run.injected_family_off cfg i = Run.injected_family_off cfg i').
  { unfold Run.injected_family_off. rewrite Hno. reflexivity. }
  unfold Run.spurious_refusal_cfg. rewrite FO, !RB. split.
  - intros (A & B & (e & m' & evs & S & R)). split; [exact A|]. split; [exact B|].
    exists e, m', evs. rewrite <- RB. split; [apply Hsp; exact S| exact R].
  - intros (A & B & (e & m' & evs & S & R)). split; [exact A|]. split; [exact B|].
    exists e, m', evs. rewrite RB. split; [apply Hsp; exact S| exact R].
Qed.

Section Sound.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variable segs : list Segment.

#[local] Notation SSTEP := (sstep_cfg segs the_scfg).

(* [comment removed for export] *)
Lemma sstep_svc_inv : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> SSTEP (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)
                  /\ ~ Run.spurious_refusal_cfg the_scfg (sys_input segs ms x8) mo eff
                  /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
                  X = SNext (mkCfg (nret ms eff) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0)
                  /\ ~ Run.spurious_refusal_cfg the_scfg (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\ evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. eauto 6.
  - right; left. eexists _, _, _. repeat split; try eassumption.
  - right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; right. auto.
Qed.

Definition mm_kind (n : node) : bool :=
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => true | _ => false end.

Lemma at_node_pending : forall n ms, at_node segs n ms -> ms_svc_pending ms <> None.
Proof.
  intros n ms H. destruct n; cbn [at_node] in H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try match goal with H : _ \/ _ |- _ => destruct H end; congruence.
Qed.

(* [comment removed for export] *)
Lemma mm_input_spec_iff : forall n ms mo x8 i,
  mminv mo -> mmsafe n mo -> at_node segs n ms -> ms_svc_pending ms = Some x8 -> node_input n = Some i ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> syscall_spec i mo o)
  /\ in_sysno (sys_input segs ms x8) = in_sysno i /\ in_arg (sys_input segs ms x8) 0 = in_arg i 0.
Proof.
  intros n ms mo x8 i MI SF AT SV NI.
  destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-.
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as [SV' A0]. rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_214 _ mo o) by reflexivity. rewrite (syscall_spec_214 _ mo o) by reflexivity.
    rewrite in_a0_si, A0. cbn [in_arg in_args nth pure_input]. rewrite !brk_outcome. reflexivity.
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as (SV' & A0 & A1 & A2 & A3 & A4 & A5). rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_222 _ mo o) by reflexivity. rewrite (syscall_spec_222 _ mo o) by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, A0, A1, A2, A3, A4, A5. cbn [in_arg in_args nth pure_input].
    pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as [(-> & -> & PR & Hl)|(-> & -> & Hl & AL & Ap & AC & RF & MC)].
    + destruct PR as [-> | ->].
      * rewrite !(mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) _ mo o mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw ltac:(apply place_declined_b_null)). reflexivity.
      * rewrite !(mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) _ mo o mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na ltac:(apply place_declined_b_null)). reflexivity.
    + pose proof (pgup_range len Hl) as [PG1 PG2].
      pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
      rewrite !(mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) _ mo o mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)
                 mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx);
        unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len); [reflexivity | lia| unfold page_size; exact AL| lia| exact RF| exact MC | lia| unfold page_size; exact AL| lia| exact RF| exact MC].
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as (SV' & A0 & A1). rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_215 _ mo o) by reflexivity. rewrite (syscall_spec_215 _ mo o) by reflexivity.
    rewrite in_a0_si, in_a1_si, A0, A1. cbn [in_arg in_args nth pure_input].
    cbn [mmsafe] in SF. destruct SF as (AL & A0' & Hl & AH & MH & MNE & MEQ & MDJ). rewrite TASK_SIZE_val in AH.
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    rewrite !(munmap_exact_outcome (wz addr) (wz len) _ mo o ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
               ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia));
      unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len); [reflexivity| rewrite TASK_SIZE_val; lia| exact MH| rewrite TASK_SIZE_val; lia| exact MH].
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as (SV' & A0 & A1 & A2). rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_226 _ mo o) by reflexivity. rewrite (syscall_spec_226 _ mo o) by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, A0, A1, A2. cbn [in_arg in_args nth pure_input].
    cbn [mmsafe] in SF. destruct SF as (-> & AL & A0' & Hl & AH & NC & MC & VD).
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    rewrite !(mprotect_expose_outcome (wz addr) (wz len) (wz 3) _ mo o mprotect_gc3 ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
               ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia));
      unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len); [reflexivity| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC].
Qed.

(* [comment removed for export] *)
Lemma nstep_mm_nil : forall n mo eff mo' evs,
  mminv mo -> mmsafe n mo -> nstep n mo eff mo' evs -> evs = [].
Proof.
  intros n mo eff mo' evs MI SF NS. destruct n; try (exfalso; exact SF); cbn [nstep] in NS; exact (proj1 NS).
Qed.

(* [comment removed for export] *)
Lemma m_halted_vm_forget_range : forall lo hi m, m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mminv_vm_forget_range : forall lo hi m, mminv m -> mminv (vm_forget_range lo hi m).
Proof. intros lo hi m MI. rewrite vm_forget_range_id by exact MI. exact MI. Qed.

Lemma mm_raw_post : forall n mo i eff mo' evs,
  mminv mo -> mmsafe n mo -> node_input n = Some i ->
  syscall_spec i mo (Ok eff mo' evs) ->
  evs = [] /\ m_halted mo' = m_halted mo /\ mminv mo'.
Proof.
  intros n mo i eff mo' evs MI SF NI H.
  destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-.
  - apply (proj1 (syscall_spec_214 (pure_input 214 [Z_to_bv 64 req]) mo _ eq_refl)) in H. cbn [in_arg in_args nth pure_input] in H.
    apply brk_outcome in H as (r & _ & E). apply Ok_inj in E as (_ & -> & ->).
    rewrite with_brk_next_eq by exact MI. rewrite m_halted_with_vmmaps. auto using mminv_with_vmmaps.
  - apply (syscall_spec_222 (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo _ eq_refl) in H.
    cbn [in_arg in_args nth pure_input] in H.
    cbn [mmsafe] in SF. destruct SF as [(-> & -> & PR & Hl)|(-> & -> & Hl & AL & Ap & AC & RF & MC)].
    + destruct PR as [-> | ->].
      * apply (proj1 (mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw ltac:(apply place_declined_b_null))) in H.
        destruct H as [(e & _ & E)|(a & _ & E)]; apply Ok_inj in E as (_ & -> & ->); [auto|].
        change (with_mmap_backing (wz 34)) with (with_mmap_backing (wz 34)). rewrite with_mmap_backing_34, m_halted_with_vmmaps. auto using mminv_with_vmmaps.
      * apply (proj1 (mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na ltac:(apply place_declined_b_null))) in H.
        destruct H as [(e & _ & E)|(a & _ & E)]; apply Ok_inj in E as (_ & -> & ->); [auto|].
        rewrite with_mmap_backing_34, m_halted_with_vmmaps. auto using mminv_with_vmmaps.
    + pose proof (pgup_range len Hl) as [PG1 PG2].
      pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
      apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)
               mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in H; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
        [| lia| unfold page_size; exact AL| lia| exact RF| exact MC].
      destruct H as [(e & _ & E)|[E|(e & _ & E)]]; apply Ok_inj in E as (_ & -> & ->); [auto| |].
      * unfold with_mmap_replacement. rewrite with_mmap_backing_50, m_halted_vm_forget_range, m_halted_with_vmmaps.
        auto using mminv_vm_forget_range, mminv_with_vmmaps.
      * unfold with_mmap_destroyed. rewrite m_halted_vm_forget_range, m_halted_with_vmmaps.
        auto using mminv_vm_forget_range, mminv_with_vmmaps.
  - apply (syscall_spec_215 (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo _ eq_refl) in H. cbn [in_arg in_args nth pure_input] in H.
    cbn [mmsafe] in SF. destruct SF as (AL & A0' & Hl & AH & MH & MNE & MEQ & MDJ). rewrite TASK_SIZE_val in AH.
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    apply (fun X0__ Q1__ Q2__ => proj1 (munmap_exact_outcome (wz addr) (wz len) _ mo _ ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
             ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__) X0__) in H; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
      [| rewrite TASK_SIZE_val; lia| exact MH].
    destruct H as [(e & _ & E)|E]; apply Ok_inj in E as (_ & -> & ->); [auto|].
    unfold with_mmap_destroyed. rewrite m_halted_vm_forget_range, m_halted_with_vmmaps.
    auto using mminv_vm_forget_range, mminv_with_vmmaps.
  - apply (syscall_spec_226 (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo _ eq_refl) in H. cbn [in_arg in_args nth pure_input] in H.
    cbn [mmsafe] in SF. destruct SF as (-> & AL & A0' & Hl & AH & NC & MC & VD).
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mprotect_expose_outcome (wz addr) (wz len) (wz 3) _ mo _ mprotect_gc3 ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
             ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in H; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
      [| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC].
    destruct H as [(e & _ & E)|(_ & E)]; apply Ok_inj in E as (_ & -> & ->); [auto|].
    unfold mprotect_model_next. rewrite m_halted_with_vmmaps. auto using mminv_with_vmmaps.
Qed.

(* [comment removed for export] *)
Lemma mm_spec_iff : forall n ms mo x8 eff mo' evs,
  mminv mo -> mmsafe n mo -> at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  (syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)
   /\ ~ Run.spurious_refusal_cfg the_scfg (sys_input segs ms x8) mo eff)
  <-> nstep n mo eff mo' evs.
Proof.
  intros n ms mo x8 eff mo' evs MI SF AT SV.
  destruct (node_input n) as [i|] eqn:NI.
  2:{ exfalso. destruct n; try exact SF; discriminate NI. }
  destruct (mm_input_spec_iff n ms mo x8 i MI SF AT SV NI) as (SP & NO & A0).
  rewrite (spurious_refusal_iff the_scfg _ _ mo eff NO A0 SP). rewrite SP.
  split.
  - intros [H NS]. pose proof (mm_raw_post n mo i eff mo' evs MI SF NI H) as (-> & _ & _).
    destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-; cbn [nstep node_input]; auto.
  - intros NS. destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-; cbn [nstep node_input] in NS;
      destruct NS as (-> & S & N); auto.
Qed.

(* [comment removed for export] *)
Lemma nstep_mm_post : forall n mo eff mo' evs,
  mminv mo -> mmsafe n mo -> m_halted mo = None -> m_killed mo = None -> nstep n mo eff mo' evs ->
  evs = [] /\ m_halted mo' = None /\ m_killed mo' = None /\ mminv mo'
  /\ alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Proof.
  intros n mo eff mo' evs MI SF HH HK NS. destruct n; try (exfalso; exact SF).
  - apply (proj1 (nstep_brk_iff mo _ _ _ _ SF)) in NS. destruct NS as (-> & _ & ->).
    rewrite with_brk_next_eq by exact MI. split; [reflexivity|]. split; [exact HH|]. split; [exact HK|].
    split; [apply mminv_with_vmmaps; exact MI|]. rewrite alloc_top_with_vmmaps. apply alloc_top_brk_model_next.
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as [(-> & -> & [->| ->] & Hl)|(-> & -> & _)].
    + apply (fun X0__ Q1__ => proj1 (nstep_mmap_rw_iff mo _ _ _ _ Q1__) X0__) in NS; [|lia]. destruct NS as (-> & [(_ & -> & _)|(a & _ & _ & _ & ->)]); (split; [reflexivity|]);
        [auto| split; [exact HH|]; split; [exact HK|]; split; [apply mminv_with_vmmaps; exact MI| unfold mmap_rw_model; rewrite alloc_top_with_vmmaps; reflexivity]].
    + apply (fun X0__ Q1__ => proj1 (nstep_mmap_na_iff mo _ _ _ _ Q1__) X0__) in NS; [|lia]. destruct NS as (-> & [(_ & -> & _)|(a & _ & _ & ->)]); (split; [reflexivity|]);
        [auto| split; [exact HH|]; split; [exact HK|]; split; [apply mminv_with_vmmaps; exact MI| unfold mmap_na_model; rewrite alloc_top_with_vmmaps; reflexivity]].
    + apply (proj1 (nstep_mmap_fixed_iff mo _ _ _ _ _ MI SF0)) in NS. destruct NS as (-> & _ & ->). split; [reflexivity|].
      split; [exact HH|]. split; [exact HK|]. split; [apply mminv_with_vmmaps; exact MI| unfold mmap_fx_model; rewrite alloc_top_with_vmmaps; reflexivity].
  - apply (proj1 (nstep_munmap_iff mo _ _ _ _ _ MI SF)) in NS. destruct NS as (-> & _ & ->). split; [reflexivity|].
    split; [exact HH|]. split; [exact HK|]. split; [apply mminv_with_vmmaps; exact MI| unfold munmap_model; rewrite alloc_top_with_vmmaps; reflexivity].
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as (-> & _).
    apply (proj1 (nstep_mprotect_iff mo _ _ _ _ _ SF0)) in NS. destruct NS as (-> & [(_ & _ & ->)|(_ & _ & ->)]); (split; [reflexivity|]);
      [auto| split; [exact HH|]; split; [exact HK|]; split; [apply mminv_with_vmmaps; exact MI| unfold mprotect_model; rewrite alloc_top_with_vmmaps; reflexivity]].
Qed.

(* [comment removed for export] *)
Lemma mm_progress : forall n mo, mminv mo -> mmsafe n mo -> exists eff mo' evs, nstep n mo eff mo' evs.
Proof.
  intros n mo MI SF. destruct n; try (exfalso; exact SF).
  - (* [comment removed for export] *) eexists _, _, []. apply (nstep_brk_iff mo); [exact SF|]. split; [reflexivity|]. split; reflexivity.
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as [(-> & -> & [->| ->] & Hl)|(-> & -> & _)].
    + destruct (Classical_Prop.classic (exists a, mmap_grant_conds mo a (pgup len) /\ vm_backing_used mo + pgup len <= vm_limit (m_vmmaps mo))) as [(a & G & B)|NG].
      * eexists _, _, []. apply (nstep_mmap_rw_iff mo); [lia|]. split; [reflexivity|]. right. exists a. eauto.
      * eexists _, _, []. apply (nstep_mmap_rw_iff mo); [lia|]. split; [reflexivity|]. left. eauto.
    + destruct (Classical_Prop.classic (exists a, mmap_grant_conds mo a (pgup len))) as [(a & G)|NG].
      * eexists _, _, []. apply (nstep_mmap_na_iff mo); [lia|]. split; [reflexivity|]. right. exists a. eauto.
      * eexists _, _, []. apply (nstep_mmap_na_iff mo); [lia|]. split; [reflexivity|]. left. eauto.
    + eexists _, _, []. apply (nstep_mmap_fixed_iff mo); [exact MI| exact SF0|]. split; [reflexivity|]. split; reflexivity.
  - eexists _, _, []. apply (nstep_munmap_iff mo); [exact MI| exact SF|]. split; [reflexivity|]. split; reflexivity.
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as (-> & _).
    destruct (mprotect_budget_ok mo (wz addr) (wz (pgup len))) eqn:B.
    + eexists _, _, []. apply (nstep_mprotect_iff mo); [exact SF0|]. split; [reflexivity|]. right. auto.
    + eexists _, _, []. apply (nstep_mprotect_iff mo); [exact SF0|]. split; [reflexivity|]. left. auto.
Qed.

(* LPS 08b1429: brk (214), mmap (222), munmap (215) and mprotect (226) do not read [in_mem]
   ([RomBase.memfree_NN]), so each node's specification is the same over every larger read-only
   backing ([RomBase.sys_rob], asked by [ITree.ns_rob]). *)
Lemma mm_rob : forall n ms mo, at_node segs n ms -> mmsafe n mo -> RomBase.sys_rob segs (mkCfg ms mo).
Proof.
  intros n ms mo AT SF. destruct n; try (exfalso; exact SF); cbn [at_node] in AT; destruct AT as [SV _];
    (eapply RomBase.sys_rob_memfree; [exact SV | rewrite unsigned_wz by lia]).
  - exact RomBase.memfree_214.
  - exact RomBase.memfree_222.
  - exact RomBase.memfree_215.
  - exact RomBase.memfree_226.
Qed.

Theorem mm_node_sound : node_sound node segs (at_node segs) nstep nexit mminv mmsafe (fun _ => nret).
Proof.
  split.
  - (* [comment removed for export] *) apply at_node_pending.
  - (* [comment removed for export] *)
    intros n ms mo evs X AT HH MI SF ST.
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (at_node_pending n ms AT SV)].
    destruct (node_input n) as [i|] eqn:NI.
    2:{ exfalso. destruct n; try exact SF; discriminate NI. }
    pose proof (mm_input_spec_iff n ms mo x8 i MI SF AT SV NI) as (SP & _ & _).
    left. destruct (sstep_svc_inv ms mo x8 evs X SV ST)
      as [(eff & mo' & mo'' & S & NS & Hh & MAT & ->)
         |[(eff & mo' & evs0 & S & NS & Hh & MAT & -> & ->)
         |[(eff & mo' & evs0 & code & S & Hh & -> & ->)
         |[(eff & mo' & evs0 & sig & S & Hk & -> & ->)
         |(S & -> & ->)]]]].
    + pose proof (proj1 (mm_spec_iff n ms mo x8 eff mo' evs MI SF AT SV) (conj S NS)) as NST.
      pose proof (mm_raw_post n mo i eff mo' evs MI SF NI (proj1 (SP _) S)) as (_ & _ & MI1).
      rewrite (materialize_model_accesses_no_lazy _ _ (mminv_lazy _ MI1)) in MAT. injection MAT as <-.
      exists eff, mo'. auto.
    + exfalso. pose proof (mm_raw_post n mo i eff mo' evs0 MI SF NI (proj1 (SP _) S)) as (_ & _ & MI1).
      rewrite (materialize_model_accesses_no_lazy _ _ (mminv_lazy _ MI1)) in MAT. discriminate.
    + exfalso. pose proof (mm_raw_post n mo i eff mo' evs0 MI SF NI (proj1 (SP _) S)) as (_ & Hh' & _). congruence.
    + exfalso. pose proof (mm_raw_post n mo i eff mo' evs0 MI SF NI (proj1 (SP _) S)) as (_ & Hh' & _).
      rewrite (m_killed_of_m_halted_none mo') in Hk by congruence. discriminate.
    + exfalso. apply (proj1 (SP _)) in S. destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-.
      * apply (proj1 (syscall_spec_214 (pure_input 214 [Z_to_bv 64 req]) mo _ eq_refl)) in S. cbn [in_arg in_args nth pure_input] in S.
        apply brk_outcome in S as (r & _ & E). discriminate E.
      * cbn [mmsafe] in SF. destruct SF as [(-> & -> & PR & Hl)|(-> & -> & Hl & AL & Ap & AC & RF & MC)].
        -- apply (syscall_spec_222 (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo _ eq_refl) in S.
           cbn [in_arg in_args nth pure_input] in S. destruct PR as [-> | ->].
           ++ apply (proj1 (mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw ltac:(apply place_declined_b_null))) in S.
              destruct S as [(e & _ & E)|(a & _ & E)]; discriminate E.
           ++ apply (proj1 (mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na ltac:(apply place_declined_b_null))) in S.
              destruct S as [(e & _ & E)|(a & _ & E)]; discriminate E.
        -- apply (syscall_spec_222 (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo _ eq_refl) in S.
           cbn [in_arg in_args nth pure_input] in S.
           pose proof (pgup_range len Hl) as [PG1 PG2].
           pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
           apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)
                    mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in S; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
             [| lia| unfold page_size; exact AL| lia| exact RF| exact MC].
           destruct S as [(e & _ & E)|[E|(e & _ & E)]]; discriminate E.
      * apply (syscall_spec_215 (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo _ eq_refl) in S. cbn [in_arg in_args nth pure_input] in S.
        cbn [mmsafe] in SF. destruct SF as (AL & A0' & Hl & AH & MH & MNE & MEQ & MDJ). rewrite TASK_SIZE_val in AH.
        assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
        apply (fun X0__ Q1__ Q2__ => proj1 (munmap_exact_outcome (wz addr) (wz len) _ mo _ ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__) X0__) in S; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
          [destruct S as [(e & _ & E)|E]; discriminate E| rewrite TASK_SIZE_val; lia| exact MH].
      * apply (syscall_spec_226 (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo _ eq_refl) in S. cbn [in_arg in_args nth pure_input] in S.
        cbn [mmsafe] in SF. destruct SF as (-> & AL & A0' & Hl & AH & NC & MC & VD).
        assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
        apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mprotect_expose_outcome (wz addr) (wz len) (wz 3) _ mo _ mprotect_gc3 ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in S; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
          [| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC].
        destruct S as [(e & _ & E)|(_ & E)]; discriminate E.
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs AT HH MI SF NS.
    pose proof (nstep_mm_post n mo rsp mo' evs MI SF HH (m_killed_of_m_halted_none _ HH) NS) as (-> & Hh' & _ & MI' & _).
    split; [exact Hh'|]. split; [exact MI'|].
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (at_node_pending n ms AT SV)].
    destruct (proj2 (mm_spec_iff n ms mo x8 rsp mo' [] MI SF AT SV) NS) as [S NSP].
    unfold nret. eapply sstep_cfg_syscall; [exact HH| exact SV| exact S| exact NSP| exact Hh'| apply materialize_model_accesses_no_lazy; exact (mminv_lazy _ MI')].
  - (* [comment removed for export] *)
    intros n ms mo code mo' AT HH MI SF NX. exfalso. destruct n; cbn in NX, SF; contradiction.
  - (* [comment removed for export] *)
    intros n ms mo AT HH MI SF.
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (at_node_pending n ms AT SV)].
    left. exact (mm_progress n mo MI SF).
  - (* robustness over a larger read-only backing *)
    intros n ms mo AT _ _ SF. exact (mm_rob n ms mo AT SF).
Qed.
End Sound.
