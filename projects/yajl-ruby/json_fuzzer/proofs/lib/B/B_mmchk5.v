(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import KLiveCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA_mm NodesA_mmW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma u64_small : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply unsigned_lit. exact Hz. Qed.
Lemma w_is0_false : forall z, 0 < z < 2^64 -> w_is0 (Z_to_bv 64 z) = false.
Proof. intros z Hz. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma w_is0_zero : w_is0 (Z_to_bv 64 0) = true.
Proof. rewrite w_is0_lit by lia. reflexivity. Qed.
Lemma page_round_up_aligned : forall z, z mod 4096 = 0 -> page_round_up_Z z = z.
Proof. intros z Hz. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.
(* [comment removed for export] *)
Lemma refusal_errno : forall addr len prot flags mo r,
  node_refusal (NMmap addr len prot flags) mo r = errno_ret_in mmap_errnos r.
Proof. intros. cbn [node_refusal]. apply ret_in_errnos_errno_ret_in. Qed.
Lemma errno_ret_in_lit : forall z, 0 <= z < 2^63 -> errno_ret_in mmap_errnos (Z_to_bv 64 z) = false.
Proof. intros z Hz. rewrite <- ret_in_errnos_errno_ret_in. apply (ret_in_errnos_lit mmap_errnos z mmap_errnos_ok Hz). Qed.

(* [comment removed for export] *)
Lemma cls_fixed_rw :
  mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 0x32) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 3) (Z_to_bv 64 0x32) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) (Z_to_bv 64 0x32) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) (Z_to_bv 64 0x32) (Z_to_bv 64 0) = true
  /\ mmap_noreserve_b (Z_to_bv 64 0x32) = false /\ mmap_anon_b (Z_to_bv 64 0x32) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma cls_fixed_nr :
  mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 0x4032) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 3) (Z_to_bv 64 0x4032) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) (Z_to_bv 64 0x4032) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) (Z_to_bv 64 0x4032) (Z_to_bv 64 0) = true
  /\ mmap_noreserve_b (Z_to_bv 64 0x4032) = true /\ mmap_anon_b (Z_to_bv 64 0x4032) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma cls_anon_rw :
  mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 0x22) (Z_to_bv 64 0) = true
  /\ mmap_noreserve_b (Z_to_bv 64 0x22) = false /\ mmap_anon_b (Z_to_bv 64 0x22) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma cls_anon_nr :
  mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 0x4022) (Z_to_bv 64 0) = true
  /\ mmap_noreserve_b (Z_to_bv 64 0x4022) = true /\ mmap_anon_b (Z_to_bv 64 0x4022) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma off0_aligned : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. reflexivity. Qed.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fixed.
Variables (A L : Z) (mo : Model).
Hypothesis AA : A mod 4096 = 0.
Hypothesis LA : L mod 4096 = 0.
Hypothesis A0 : 0 < A.
Hypothesis L0 : 0 < L.
Hypothesis AL : A + L <= alloc_top (m_vmmaps mo).
Hypothesis TOP : alloc_top (m_vmmaps mo) < 2^63.
Hypothesis RF : region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true.
Hypothesis MC : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true.

(* [comment removed for export] *)
Definition fixed_post (flags : Z) : Model :=
  with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 A) (Z_to_bv 64 L)
    (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 A) (Z_to_bv 64 L)) mo).
Definition fixed_destroyed : Model :=
  with_mmap_destroyed (Z_to_bv 64 A) (Z_to_bv 64 L) (mmap_fixed_destroyed_next (m_vmmaps mo) (Z_to_bv 64 A) (Z_to_bv 64 L)) mo.

Definition fixed_match (flags : Z) (eff : resp) : check_result :=
  match eff with
  | mkEffectU r [] zs us [] [] =>
      if errno_ret_in mmap_errnos r
      then match zs with
           | _ :: _ => CheckReject
           | [] => match us with
                   | [] => CheckOk mo []
                   | _ => if listNN_eqb us [(Z_to_bv 64 A, Z_to_bv 64 L)] then CheckOk fixed_destroyed [] else CheckReject
                   end
           end
      else match us with
           | _ :: _ => CheckReject
           | [] => if bv_eqb r (Z_to_bv 64 A) && listNN_eqb zs [(Z_to_bv 64 A, Z_to_bv 64 L)]
                      && mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 A) (Z_to_bv 64 L)
                   then CheckOk (fixed_post flags) []
                   else CheckReject
           end
  | _ => CheckReject
  end.

Local Ltac reduce_fixed C1 C2 C3 C4 C6 :=
  let HL := fresh in let HA := fresh in
  assert (HL : bv_unsigned (Z_to_bv 64 L) = L) by (apply u64_small; lia);
  assert (HA : bv_unsigned (Z_to_bv 64 A) = A) by (apply u64_small; lia);
  unfold mmap_CHK, check_mmap; rewrite off0_aligned, C6; cbn [negb]; rewrite (w_is0_false L) by lia; rewrite C1, C2, C3, C4; cbv zeta;
  rewrite HL, HA, (page_round_up_aligned L LA);
  replace (two_pow_64 <=? A + L) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia);
  replace (negb (A + L <=? alloc_top (m_vmmaps mo))) with false by (symmetry; rewrite Bool.negb_false_iff; apply Z.leb_le; lia);
  replace (negb (A mod page_size =? 0)) with false by (symmetry; rewrite Bool.negb_false_iff; apply Z.eqb_eq; unfold page_size; exact AA);
  replace (negb (0 <? A)) with false by (symmetry; rewrite Bool.negb_false_iff; apply Z.ltb_lt; lia);
  cbv beta iota; rewrite RF, MC; cbn [andb]; reflexivity.

Lemma chk_fixed_rw_red : forall eff, mmap_CHK A L 3 0x32 mo eff = fixed_match 0x32 eff.
Proof. intros eff. pose proof cls_fixed_rw as (C1 & C2 & C3 & C4 & C5 & C6). unfold fixed_match, fixed_post, fixed_destroyed. reduce_fixed C1 C2 C3 C4 C6. Qed.
Lemma chk_fixed_nr_red : forall eff, mmap_CHK A L 3 0x4032 mo eff = fixed_match 0x4032 eff.
Proof. intros eff. pose proof cls_fixed_nr as (C1 & C2 & C3 & C4 & C5 & C6). unfold fixed_match, fixed_post, fixed_destroyed. reduce_fixed C1 C2 C3 C4 C6. Qed.

Lemma fixed_match_nu : forall flags eff, fixed_match flags eff <> CheckUnmodeled.
Proof.
  intros flags [r ws zs us cs ci]. unfold fixed_match.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; try discriminate.
  all: try (destruct (listNN_eqb _ _); discriminate). all: destruct (_ && _ && _); discriminate.
Qed.

(* [comment removed for export] *)
Lemma fixed_match_ok : forall flags eff mo' evs, fixed_match flags eff = CheckOk mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false ->
  evs = [] /\ eff = mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] []
  /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 A) (Z_to_bv 64 L) = true
  /\ mo' = fixed_post flags.
Proof.
  intros flags [r ws zs us cs ci] mo' evs H NR. unfold fixed_match in H. cbn [eff_ret] in NR.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. rewrite NR in H.
  destruct us; [|discriminate].
  destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E1; [|discriminate].
  destruct (listNN_eqb zs [(Z_to_bv 64 A, Z_to_bv 64 L)]) eqn:E2; [|discriminate].
  destruct (mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 A) (Z_to_bv 64 L)) eqn:E3; [|discriminate].
  cbn [andb] in H. injection H as <- <-. apply bv_eqb_eq in E1. apply (proj1 (listNN_eqb_eq _ _)) in E2. subst. auto.
Qed.

Lemma fixed_match_grant : forall flags,
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 A) (Z_to_bv 64 L) = true ->
  fixed_match flags (mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] []) = CheckOk (fixed_post flags) [].
Proof.
  intros flags B. unfold fixed_match. rewrite (errno_ret_in_lit A) by lia. rewrite bv_eqb_refl, listNN_eqb_refl', B. reflexivity.
Qed.
End Fixed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Anon.
Variables (L : Z) (mo : Model).
Hypothesis LA : L mod 4096 = 0.
Hypothesis L0 : 0 < L.
Hypothesis LB : L < 2^47.

Definition anon_post (flags : Z) (r : word) : Model :=
  with_mmap_backing (Z_to_bv 64 flags) r (Z_to_bv 64 L)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((r, Z_to_bv 64 L) :: vm_maps (m_vmmaps mo))
                    (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))
                    (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo).

Definition anon_match (flags : Z) (eff : resp) : check_result :=
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if errno_ret_in mmap_errnos r
      then match zs with [] => CheckOk mo [] | _ => CheckReject end
      else
        if (bv_unsigned r mod page_size =? 0) && (0 <? bv_unsigned r) && (bv_unsigned r + L <=? alloc_top (m_vmmaps mo))
           && region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L)
           && mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo L
           && listNN_eqb zs [(r, Z_to_bv 64 L)]
        then CheckOk (anon_post flags r) []
        else CheckReject
  | _ => CheckReject
  end.

Local Ltac reduce_anon C1 C3 :=
  let HL := fresh in
  assert (HL : bv_unsigned (Z_to_bv 64 L) = L) by (apply u64_small; lia);
  unfold mmap_CHK, check_mmap; rewrite off0_aligned, C3; cbn [negb]; rewrite (w_is0_false L) by lia; rewrite C1; cbv zeta;
  rewrite HL, (page_round_up_aligned L LA); reflexivity.

Lemma chk_anon_rw_red : forall eff, mmap_CHK 0 L 3 0x22 mo eff = anon_match 0x22 eff.
Proof. intros eff. pose proof cls_anon_rw as (C1 & _ & C3). unfold anon_match, anon_post. reduce_anon C1 C3. Qed.
Lemma chk_anon_nr_red : forall eff, mmap_CHK 0 L 3 0x4022 mo eff = anon_match 0x4022 eff.
Proof. intros eff. pose proof cls_anon_nr as (C1 & _ & C3). unfold anon_match, anon_post. reduce_anon C1 C3. Qed.

Lemma anon_match_nu : forall flags eff, anon_match flags eff <> CheckUnmodeled.
Proof.
  intros flags [r ws zs us cs ci]. unfold anon_match.
  destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|]. destruct (_ && _); discriminate.
Qed.

Lemma anon_match_ok : forall flags eff mo' evs, anon_match flags eff = CheckOk mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false ->
  evs = [] /\ exists r, eff = mkEffectU r [] [(r, Z_to_bv 64 L)] [] [] []
  /\ bv_unsigned r mod 4096 = 0 /\ 0 < bv_unsigned r /\ bv_unsigned r + L <= alloc_top (m_vmmaps mo)
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L) = true
  /\ mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo L = true
  /\ mo' = anon_post flags r.
Proof.
  intros flags [r ws zs us cs ci] mo' evs H NR. unfold anon_match in H. cbn [eff_ret] in NR.
  destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. rewrite NR in H.
  destruct (bv_unsigned r mod page_size =? 0) eqn:E1; [|discriminate].
  destruct (0 <? bv_unsigned r) eqn:E2; [|discriminate].
  destruct (bv_unsigned r + L <=? alloc_top (m_vmmaps mo)) eqn:E3; [|discriminate].
  destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (Z_to_bv 64 L)) eqn:E4; [|discriminate].
  destruct (mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo L) eqn:E5; [|discriminate].
  destruct (listNN_eqb zs [(r, Z_to_bv 64 L)]) eqn:E7; [|discriminate].
  cbn [andb] in H. injection H as <- <-. apply (proj1 (listNN_eqb_eq _ _)) in E7. subst.
  apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3. unfold page_size in E1.
  split; [reflexivity|]. exists r. repeat split; assumption.
Qed.

Lemma anon_match_grant : forall flags (R : Z),
  R mod 4096 = 0 -> 0 < R -> R + L <= alloc_top (m_vmmaps mo) -> alloc_top (m_vmmaps mo) < 2^63 ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 R) (Z_to_bv 64 L) = true ->
  mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo L = true ->
  anon_match flags (mkEffectU (Z_to_bv 64 R) [] [(Z_to_bv 64 R, Z_to_bv 64 L)] [] [] []) = CheckOk (anon_post flags (Z_to_bv 64 R)) [].
Proof.
  intros flags R RA R0 RL TOP RFR NB. unfold anon_match.
  assert (HR : bv_unsigned (Z_to_bv 64 R) = R) by (apply u64_small; lia).
  rewrite (errno_ret_in_lit R) by lia. rewrite HR.
  replace (R mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; unfold page_size; exact RA).
  replace (0 <? R) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (R + L <=? alloc_top (m_vmmaps mo)) with true by (symmetry; apply Z.leb_le; lia).
  rewrite RFR, NB, listNN_eqb_refl'. reflexivity.
Qed.
End Anon.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition munmap_CHK (A L : Z) (mo : Model) (eff : resp) : check_result :=
  check_munmap (Z_to_bv 64 A) (Z_to_bv 64 L) eff mo.

Section Munmap.
Variables (A L : Z) (mo : Model).
Hypothesis AA : A mod 4096 = 0.
Hypothesis LA : L mod 4096 = 0.
Hypothesis A0 : 0 < A.
Hypothesis L0 : 0 < L.
Hypothesis AL : A + L <= TASK_SIZE.
Hypothesis MH : map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true.

Definition munmap_post : Model :=
  with_mmap_destroyed (Z_to_bv 64 A) (Z_to_bv 64 L)
    (mkVmMapsFull (vm_reserved (m_vmmaps mo)) (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A))
       (maps_subtract (vm_noaccess (m_vmmaps mo)) A (A + L))
       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.

Lemma chk_munmap_red : forall eff,
  munmap_CHK A L mo eff =
  match eff with
  | mkEffectU r [] [] us [] [] =>
      if w_is0 r && listNN_eqb us [(Z_to_bv 64 A, Z_to_bv 64 L)] then CheckOk munmap_post [] else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros eff.
  assert (HL : bv_unsigned (Z_to_bv 64 L) = L) by (apply u64_small; unfold TASK_SIZE in AL; lia).
  assert (HA : bv_unsigned (Z_to_bv 64 A) = A) by (apply u64_small; unfold TASK_SIZE in AL; lia).
  unfold munmap_CHK, check_munmap, munmap_post. rewrite (w_is0_false L) by (unfold TASK_SIZE in AL; lia). rewrite HA, HL.
  replace (negb (A mod page_size =? 0)) with false by (symmetry; rewrite Bool.negb_false_iff; apply Z.eqb_eq; unfold page_size; exact AA).
  cbn [orb]. cbv zeta. rewrite (page_round_up_aligned L LA).
  replace (TASK_SIZE <? A + L) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite MH. rewrite ?HA, ?HL. reflexivity.
Qed.

Lemma chk_munmap_nu : forall eff, munmap_CHK A L mo eff <> CheckUnmodeled.
Proof.
  intros [r ws zs us cs ci]. rewrite chk_munmap_red.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (_ && _); discriminate.
Qed.

Lemma chk_munmap_inv : forall eff mo' evs, munmap_CHK A L mo eff = CheckOk mo' evs ->
  evs = [] /\ eff = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] /\ mo' = munmap_post.
Proof.
  intros [r ws zs us cs ci] mo' evs H. rewrite chk_munmap_red in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (w_is0 r) eqn:E1; [|discriminate]. destruct (listNN_eqb us [(Z_to_bv 64 A, Z_to_bv 64 L)]) eqn:E2; [|discriminate].
  cbn [andb] in H. injection H as <- <-. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply (proj1 (listNN_eqb_eq _ _)) in E2. subst. auto.
Qed.

Lemma chk_munmap_grant :
  munmap_CHK A L mo (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] []) = CheckOk munmap_post [].
Proof. rewrite chk_munmap_red. rewrite w_is0_zero, listNN_eqb_refl'. reflexivity. Qed.
End Munmap.
End RC__1.
