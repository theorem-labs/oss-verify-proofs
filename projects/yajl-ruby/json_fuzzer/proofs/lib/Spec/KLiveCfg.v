(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesCfg NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc RawAlloc KArith KInv KLink KStep KLive KArena LB_Kernel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem KL_arena_lo : forall L pbrk mo len,
  KL L pbrk mo -> 0 < len ->
  let h := m_vmmaps mo in
  let n := mmap_len len in
  n * (live_bytes (vm_maps h) / PGSZ + rcost (vm_reserved h) + 1) <= alloc_ceiling - PGSZ ->
  exists r, (r mod 4096 = 0 /\ 0 < r /\ r + n <= alloc_ceiling)
         /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 r) (Z_to_bv 64 n) = true.
Proof.
  intros L pbrk mo len HK Hlen h n Hnum.
  assert (HF : 0 < PGSZ < alloc_ceiling) by (pose proof alloc_ceiling_ge; unfold PGSZ; lia).
  destruct (KL_arena_gen PGSZ L pbrk mo len eq_refl HF HK Hlen Hnum) as (r & Hr & HFr & Hrf).
  exists r. split; [exact Hr| exact Hrf].
Qed.

(* [comment removed for export] *)
Definition MMAP_ROOM (mo : Model) (len : Z) : Prop :=
  mmap_len len * (live_bytes (vm_maps (m_vmmaps mo)) / PGSZ + rcost (vm_reserved (m_vmmaps mo)) + 1) <= alloc_ceiling - PGSZ
  /\ live_bytes (vm_maps (m_vmmaps mo)) + mmap_len len <= vm_limit (m_vmmaps mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ret_in_errnos_errno_ret_in : forall es r, ret_in_errnos es r = errno_ret_in es r.
Proof. reflexivity. Qed.

Lemma ret_in_errnos_lit : forall es z, errnos_ok es = true -> 0 <= z < 2^63 -> ret_in_errnos es (Z_to_bv 64 z) = false.
Proof.
  intros es z Hes Hz. rewrite ret_in_errnos_errno_ret_in. apply errno_ret_in_below; [exact Hes|].
  rewrite unsigned_lit by lia. unfold two_pow_64. lia.
Qed.

Lemma ret_in_errnos_ENOMEM : forall es, In ENOMEM es -> ret_in_errnos es (errno_ret ENOMEM) = true.
Proof. intros es H. rewrite ret_in_errnos_errno_ret_in. apply errno_ret_in_intro. exact H. Qed.

(* [comment removed for export] *)
Lemma ncan_mmap : forall L pbrk mo len prot,
  KL L pbrk mo -> 0 < len < LEN_MAX -> (prot = PROT_NONE \/ prot = PROT_RW) -> MMAP_ROOM mo len ->
  ncan (NMmap 0 len prot MAPF) mo.
Proof.
  intros L pbrk mo len prot HK Hlen Hprot [Hwin Hbud]. pose proof alloc_ceiling_lt as Hcl.
  pose proof (mmap_len_ge len ltac:(lia)) as N1.
  destruct (KL_arena_lo L pbrk mo len HK ltac:(lia) Hwin) as (r & (R1 & R2 & R3) & R5).
  pose proof (vm_backing_used_le_live mo (minv_lazy _ (kl_minv _ _ _ HK)) (kl_mat _ _ _ HK)) as U.
  destruct Hprot as [-> | ->].
  - destruct (nstep_mmap_none_grant_can len r mo (kl_minv _ _ _ HK) ltac:(lia) (conj R1 (conj R2 R3)) R5) as (Hst & _).
    eexists _, _, []. split; [exact Hst|]. cbn [node_refusal eff_ret]. apply ret_in_errnos_lit; [reflexivity| lia].
  - destruct (nstep_mmap_grant_can len r mo (kl_minv _ _ _ HK) ltac:(lia) (conj R1 (conj R2 R3)) R5 ltac:(lia)) as (Hst & _).
    eexists _, _, []. split; [exact Hst|]. cbn [node_refusal eff_ret]. apply ret_in_errnos_lit; [reflexivity| lia].
Qed.

Theorem nstep_cfg_mmap_rw_granted : forall L pbrk mo len rsp mo' evs,
  KL L pbrk mo -> 0 < len < LEN_MAX -> MMAP_ROOM mo len ->
  nstep_cfg acfg (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs ->
  exists x, dec_mmap len [] rsp = Some (MmOk x) /\ is_err x = false.
Proof.
  intros L pbrk mo len rsp mo' evs HK Hlen Hroom Hcfg.
  pose proof (mmap_len_ge len ltac:(lia)) as N1. pose proof alloc_ceiling_lt as Hcl.
  destruct (nstep_cfg_succ_only acfg (NMmap 0 len PROT_RW MAPF) mo rsp mo' evs eq_refl (ncan_mmap L pbrk mo len PROT_RW HK Hlen (or_intror eq_refl) Hroom) Hcfg) as [Hst Hnr].
  destruct (nstep_dec_mmap len [] mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(unfold LEN_MAX in Hlen; lia) (Forall_nil _) Hst)
    as (_ & _ & x & Hd & Hx).
  destruct x as [e|a].
  - exfalso. destruct Hx as [-> _]. apply dec_mmap_Some in Hd as [-> _].
    cbn [node_refusal eff_ret efferr eff0] in Hnr. rewrite ret_in_errnos_ENOMEM in Hnr by (left; reflexivity). discriminate Hnr.
  - exists a. split; [exact Hd|]. destruct Hx as (Hok & _). exact (proj1 (mmap_ok_not_err _ _ _ Hok ltac:(lia))).
Qed.

Theorem nstep_cfg_mmap_none_granted : forall L pbrk mo len rsp mo' evs,
  KL L pbrk mo -> 0 < len < LEN_MAX -> MMAP_ROOM mo len ->
  nstep_cfg acfg (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs ->
  exists x, dec_mmap_none len [] rsp = Some (MmOk x) /\ is_err x = false.
Proof.
  intros L pbrk mo len rsp mo' evs HK Hlen Hroom Hcfg.
  pose proof (mmap_len_ge len ltac:(lia)) as N1. pose proof alloc_ceiling_lt as Hcl.
  destruct (nstep_cfg_succ_only acfg (NMmap 0 len PROT_NONE MAPF) mo rsp mo' evs eq_refl (ncan_mmap L pbrk mo len PROT_NONE HK Hlen (or_introl eq_refl) Hroom) Hcfg) as [Hst Hnr].
  destruct (nstep_dec_mmap_none len [] mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(unfold LEN_MAX in Hlen; lia) (Forall_nil _) Hst)
    as (_ & _ & x & Hd & Hx).
  destruct x as [e|a].
  - exfalso. destruct Hx as [-> _]. apply dec_mmap_none_Some in Hd as [-> _].
    cbn [node_refusal eff_ret efferr eff0] in Hnr. rewrite ret_in_errnos_ENOMEM in Hnr by (left; reflexivity). discriminate Hnr.
  - exists a. split; [exact Hd|]. destruct Hx as (Hok & _). exact (proj1 (mmap_ok_not_err _ _ _ Hok ltac:(lia))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MPROTECT_META.
  Variables (L : mled) (pbrk : Z) (mo : Model) (b l k : Z).
  Hypothesis HK : KL L pbrk mo.
  Hypothesis Hin : In (b, l, k) (ld_metas L).
  Hypothesis Hk2 : (2 + k) * PGSZ <= round_up_pg l.
  Let a := b + (1 + k) * PGSZ.
  Let h := m_vmmaps mo.

  (* [comment removed for export] *)
  Lemma meta_page_facts :
    (0 < a /\ a mod 4096 = 0 /\ a + PGSZ < 2^64)
    /\ map_contains (vm_noaccess h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
    /\ map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true.
  Proof.
    pose proof alloc_ceiling_lt as Hcl.
    pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    pose proof Hk2 as Hk2'. rewrite round_up_pg_eq in Hk2'. fold (mmap_len l) in Hk2'. set (nb := mmap_len l) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ha : 0 < a /\ a mod 4096 = 0 /\ a + PGSZ < 2^64).
    { split; [unfold PGSZ in *; lia|]. split; [| unfold PGSZ in *; lia]. subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
    split; [exact Ha|]. split.
    - destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
    - unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6.
      assert (B7 : bv_unsigned (snd (went b nb)) = nb) by (clear -B5 B6; lia). rewrite B5, B7.
      rewrite (proj2 (Z.leb_le _ _)) by (clear -Hab Ak; unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by (clear -Hab Ak; unfold PGSZ in *; lia). reflexivity.
  Qed.

  Hypothesis Hbud : live_bytes (vm_maps (m_vmmaps mo)) + PGSZ <= vm_limit (m_vmmaps mo).

  Lemma meta_page_budget : mprotect_budget_ok mo (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true.
  Proof.
    unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
    set (mo1 := mprotect_model_next mo (Z_to_bv 64 a) (Z_to_bv 64 PGSZ)).
    assert (E1 : vm_maps (m_vmmaps mo1) = vm_maps h /\ vm_limit (m_vmmaps mo1) = vm_limit h /\ m_vm_lazy mo1 = m_vm_lazy mo /\ m_vm_materialized mo1 = m_vm_materialized mo).
    { subst mo1. unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, m_vm_materialized_with_vmmaps. repeat split; reflexivity. }
    destruct E1 as (E1 & E2 & E3 & E4).
    pose proof (vm_backing_used_le_live mo1 ltac:(rewrite E3; exact (minv_lazy _ (kl_minv _ _ _ HK))) ltac:(rewrite E4; exact (kl_mat _ _ _ HK))) as U1.
    rewrite E1, E2 in *. unfold h in *. unfold PGSZ in *. lia.
  Qed.

  Lemma ncan_mprotect_meta : ncan (NMprotect a PGSZ PROT_RW) mo.
  Proof.
    destruct meta_page_facts as (Ha & Hcn & Hcm).
    destruct (nstep_mprotect_grant_can a mo Ha Hcn Hcm meta_page_budget) as (Hst & _).
    eexists _, _, []. split; [exact Hst|]. cbn [node_refusal eff_ret]. apply ret_in_errnos_lit; [reflexivity| lia].
  Qed.

  Theorem nstep_cfg_mprotect_granted_sec : forall rsp mo' evs,
    nstep_cfg acfg (NMprotect a PGSZ PROT_RW) mo rsp mo' evs ->
    dec_mprotect_rw a PGSZ rsp = Some (RgDone true).
  Proof.
    intros rsp mo' evs Hcfg. destruct meta_page_facts as (Ha & Hcn & Hcm).
    destruct (nstep_cfg_succ_only acfg (NMprotect a PGSZ PROT_RW) mo rsp mo' evs eq_refl ncan_mprotect_meta Hcfg) as [Hst Hnr].
    cbn [node_refusal eff_ret] in Hnr. rewrite ret_in_errnos_errno_ret_in in Hnr.
    apply nstep_mprotect_iff in Hst. rewrite (mprotect_gates a mo Ha Hcn Hcm) in Hst.
    destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Hnr.
    destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    rewrite Hnr in Hst.
    destruct (mprotect_budget_ok mo (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) && w_is0 r && listNN_eqb zs [(Z_to_bv 64 a, Z_to_bv 64 PGSZ)]) eqn:E; [|discriminate].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [_ E2]. unfold w_is0 in E2. apply bv_eqb_eq in E2. apply listNN_eqb_eq in E3. subst r zs.
    unfold dec_mprotect_rw, dec_mprotect. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true.
    change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. reflexivity.
  Qed.
End MPROTECT_META.

Theorem nstep_cfg_mprotect_granted : forall L pbrk mo b l k rsp mo' evs,
  KL L pbrk mo -> brk_quiet L -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  live_bytes (vm_maps (m_vmmaps mo)) + PGSZ <= vm_limit (m_vmmaps mo) ->
  nstep_cfg acfg (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo rsp mo' evs ->
  dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp = Some (RgDone true).
Proof.
  intros L pbrk mo b l k rsp mo' evs HK _ Hin Hk2 Hbud Hcfg.
  exact (nstep_cfg_mprotect_granted_sec L pbrk mo b l k HK Hin Hk2 Hbud rsp mo' evs Hcfg).
Qed.

End RC__.
