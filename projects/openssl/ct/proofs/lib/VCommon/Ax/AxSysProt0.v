(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct AxMeasure AxSysFix.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_226 (i : SyscallInput) (m : Model) (r : word) :
  bv_unsigned (in_sysno i) = 226 -> refusal_b i m r = errno_ret_in mprotect_errnos r.
Proof. intros H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_226_of_errno (i : SyscallInput) (m : Model) (r : word) :
  bv_unsigned (in_sysno i) = 226 -> errno_ret_in mprotect_errnos r = true -> refusal_b i m r = true.
Proof. intros H E. rewrite (refusal_226 i m r H). exact E. Qed.

Lemma refusal_226_zero : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

Lemma injected_off_226 (cfg : SpuriousCfg) (i : SyscallInput) :
  bv_unsigned (in_sysno i) = 226 -> sc_alloc cfg = false -> injected_family_off cfg i = true.
Proof. intros H Hc. unfold injected_family_off. rewrite H. cbn. rewrite Hc. reflexivity. Qed.

Lemma spurious_226 (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (eff eff' : SyscallEffect) (m' : Model) (evs' : list event) :
  bv_unsigned (in_sysno i) = 226 -> sc_alloc cfg = false ->
  errno_ret_in mprotect_errnos (eff_ret eff) = true ->
  check_syscall i eff' m = CheckOk m' evs' -> errno_ret_in mprotect_errnos (eff_ret eff') = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros H Hc E Hok E'. split; [exact (injected_off_226 cfg i H Hc)|].
  split; [exact (refusal_226_of_errno i m _ H E)|].
  exists eff', m', evs'. split; [apply check_syscall_ok_iff; exact Hok | rewrite (refusal_226 i m _ H); exact E'].
Qed.

(* [comment removed for export] *)
Lemma prot_shape_lit (prot : word) : bv_unsigned prot = 3 -> mprotect_grows_conflict_b prot = false /\ mprotect_modeled_b prot = true.
Proof. intros H. unfold mprotect_grows_conflict_b, mprotect_modeled_b. rewrite H. split; reflexivity. Qed.

Record prot_gate (m : Model) (addr len : word) : Prop := mkProtGate {
  pg_len : bv_unsigned len <> 0;
  pg_al  : bv_unsigned addr mod 4096 = 0;
  pg_top : bv_unsigned addr + fix_nZ len < two_pow_64;
  pg_na  : map_contains (vm_noaccess (m_vmmaps m)) addr (fix_n len) = true;
  pg_own : map_contains (vm_maps (m_vmmaps m)) addr (fix_n len) = true
}.

Section Prot.
Variables (m : Model) (addr len prot : word).
Hypothesis S1 : mprotect_grows_conflict_b prot = false.
Hypothesis S2 : mprotect_modeled_b prot = true.
Hypothesis G : prot_gate m addr len.

Lemma check_mprotect_na (eff : SyscallEffect) :
  check_mprotect addr len prot eff m =
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if errno_ret_in mprotect_errnos r
      then match zs with [] => CheckOk m [] | _ => CheckReject end
      else if mprotect_budget_ok m addr (fix_n len) && w_is0 r && listNN_eqb zs [(addr, fix_n len)]
           then CheckOk (mprotect_model_next m addr (fix_n len)) []
           else CheckReject
  | _ => CheckReject
  end.
Proof.
  destruct G as [g1 g2 g3 g4 g5]. unfold check_mprotect. rewrite S1.
  replace (negb (bv_unsigned addr mod page_size =? 0)) with false by (symmetry; apply negb_false_iff, Z.eqb_eq; exact g2).
  rewrite (w_is0_false len g1). fold (fix_nZ len).
  replace (two_pow_64 <=? bv_unsigned addr + fix_nZ len) with false by (symmetry; apply Z.leb_gt; exact g3).
  rewrite S2. cbn [negb]. cbv zeta. fold (fix_nZ len). fold (fix_n len). rewrite g4, g5. reflexivity.
Qed.

Lemma chk_prot (eff : SyscallEffect) (m' : Model) (evs : list event) :
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  errno_ret_in mprotect_errnos (eff_ret eff) = true
  \/ (eff = mkEffect (Z_to_bv 64 0) [] [(addr, fix_n len)] /\ m' = mprotect_model_next m addr (fix_n len) /\ evs = []
      /\ mprotect_budget_ok m addr (fix_n len) = true).
Proof.
  rewrite check_mprotect_na. destruct eff as [r ws zs us cs ci]. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate].
  destruct ci; [|destruct zs; discriminate].
  destruct (errno_ret_in mprotect_errnos r) eqn:E; [intros _; left; reflexivity|].
  destruct (mprotect_budget_ok m addr (fix_n len) && w_is0 r && listNN_eqb zs [(addr, fix_n len)]) eqn:E2; [|discriminate].
  intros H. injection H as <- <-. right.
  apply andb_prop in E2 as [E2 E5]. apply andb_prop in E2 as [E3 E4]. unfold w_is0 in E4.
  apply bv_eqb_eq in E4. apply listNN_eqb_eq in E5. subst r zs. repeat split; try reflexivity. exact E3.
Qed.

Lemma chk_prot_grant :
  mprotect_budget_ok m addr (fix_n len) = true ->
  check_mprotect addr len prot (mkEffect (Z_to_bv 64 0) [] [(addr, fix_n len)]) m = CheckOk (mprotect_model_next m addr (fix_n len)) [].
Proof.
  intros Hb. rewrite check_mprotect_na. rewrite refusal_226_zero, Hb.
  replace (w_is0 (Z_to_bv 64 0)) with true by reflexivity.
  replace (listNN_eqb [(addr, fix_n len)] [(addr, fix_n len)]) with true by (symmetry; apply listNN_eqb_eq; reflexivity).
  reflexivity.
Qed.

Lemma chk_prot_modeled (eff : SyscallEffect) : check_mprotect addr len prot eff m <> CheckUnmodeled.
Proof.
  rewrite check_mprotect_na. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate].
  destruct ci; [|destruct zs; discriminate].
  destruct (errno_ret_in mprotect_errnos r).
  - destruct zs; discriminate.
  - destruct (_ && _); discriminate.
Qed.

Lemma chk_prot_halted (eff : SyscallEffect) (m' : Model) (evs : list event) :
  check_mprotect addr len prot eff m = CheckOk m' evs -> evs = [] /\ m_halted m' = m_halted m.
Proof.
  rewrite check_mprotect_na. destruct eff as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate].
  destruct ci; [|destruct zs; discriminate].
  destruct (errno_ret_in mprotect_errnos r).
  - destruct zs; [|discriminate]. intros H. injection H as <- <-. split; reflexivity.
  - destruct (_ && _); [|discriminate]. intros H. injection H as <- <-. split; reflexivity.
Qed.

End Prot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section UsedProt.
Variables (m : Model) (addr n : word).
Hypothesis Hmaps : nowrap (vm_maps (m_vmmaps m)).
Hypothesis Hna : nowrap (vm_noaccess (m_vmmaps m)).
Hypothesis Hrange : bv_unsigned addr + bv_unsigned n <= two64.

Local Notation lo := (bv_unsigned addr).
Local Notation hi := (bv_unsigned addr + bv_unsigned n).

Lemma used_prot (K : Z) :
  0 <= K -> (forall x, lo <= x < hi -> SW (vm_maps (m_vmmaps m)) x <= K) ->
  vm_backing_used (mprotect_model_next m addr n) <= vm_backing_used m + K * bv_unsigned n.
Proof.
  intros HK HSW. pose proof (bv_unsigned_in_range 64 n) as Hn.
  cut (vm_backing_used (mprotect_model_next m addr n) <= vm_backing_used m + K * (hi - lo)).
  { intros X. replace (hi - lo) with (bv_unsigned n) in X by lia. exact X. }
  apply used_le_pw; try assumption; try lia.
  - intros x Hx. unfold BWm at 1, mprotect_model_next. cbv zeta. rewrite with_vmmaps_vmmaps_eq, with_vmmaps_lazy_eq. cbn [vm_maps vm_noaccess].
    pose proof (BW_nonneg (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (m_vm_lazy m) x) as X2. fold (BWm m x) in X2.
    destruct (inrb lo hi x) eqn:E.
    + pose proof (BW_le_SW (vm_maps (m_vmmaps m)) (maps_subtract (vm_noaccess (m_vmmaps m)) lo hi) (m_vm_lazy m) x) as X1.
      apply inrb_iff in E. specialize (HSW x E). lia.
    + unfold BWm, BW. rewrite inlb_subtract by assumption. rewrite E, andb_true_r. lia.
  - unfold mprotect_model_next. cbv zeta. rewrite with_vmmaps_mat_eq. lia.
Qed.

End UsedProt.
