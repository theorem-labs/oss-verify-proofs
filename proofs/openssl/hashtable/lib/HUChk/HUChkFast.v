(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxHandoff FxDrive.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan H0Lim HUAtable HUFiPre HUFiTail.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrPure BrLedger BrKeep BrMain BrSinv BrInfer BrGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HUChk Require Import HUBrGlue2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint existsbL {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => false | a :: r => if f a then true else existsbL f r end.
Lemma existsbL_eq {T : Type} (f : T -> bool) (l : list T) : existsbL f l = existsb f l.
Proof. induction l as [|a r IH]; cbn [existsbL existsb]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Definition leaf_chkL (k : Z) (TB : list (int * Z * Z)) (CSL : list CAP.acs) (XRNG : nat -> Z -> Z -> bool)
    (XCHK : CAP.acs -> bdata -> fstate -> fledger -> bool) (x : fstate * fledger * int * stop) : bool :=
  let F := fst (fst (fst x)) in let L := snd (fst (fst x)) in
  existsbL (fun CS =>
    match br_infer IMH F L CS [] (TEQ k) TB 192 [] kit_pins with
    | Some bd0 =>
        if maps_check bd0 F L (CAP.a_maps CS) (fl_maps L) then
        if brk_check bd0 F L (CAP.a_brk CS) then
          leaf_chk k TB [CS] XRNG XCHK x
        else false else false
    | None => false
    end) CSL.

Lemma leaf_chkL_ok k TB CSL XRNG XCHK x : leaf_chkL k TB CSL XRNG XCHK x = true -> leaf_chk k TB CSL XRNG XCHK x = true.
Proof.
  unfold leaf_chkL. cbv zeta. rewrite existsbL_eq. intros Hc. apply existsb_exists in Hc as (CS & Hin & Hb).
  destruct (br_infer IMH (fst (fst (fst x))) (snd (fst (fst x))) CS [] (TEQ k) TB 192 [] kit_pins) as [bd0|]; [|discriminate].
  destruct (maps_check bd0 _ _ _ _); [|discriminate]. destruct (brk_check bd0 _ _ _); [|discriminate].
  unfold leaf_chk in Hb |- *. cbv zeta in Hb |- *. cbn [existsb] in Hb. rewrite orb_false_r in Hb.
  apply existsb_exists. exists CS. split; [exact Hin | exact Hb].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_nokn (cs : CAP.acs) : CAP.acs :=
  let ss := CAP.a_ss cs in CAP.with_ss cs (AX2.SS (AX2.s_pc ss) (AX2.s_regs ss) (AX2.s_log ss) [] (AX2.s_next ss)).
Definition with_resid (bd : bdata) (R : list nat) : bdata :=
  BD (bd_vt bd) (bd_tl bd) (bd_xt bd) (bd_teq bd) (bd_tb bd) (bd_ts bd) (bd_tc bd) (bd_ah bd) R.

Lemma kentry_check_resid IM A bd R keep KF F L k :
  kentry_check IM A (with_resid bd R) keep KF F L k = kentry_check IM A bd keep KF F L k.
Proof. destruct bd. reflexivity. Qed.

Lemma kn_check_auto IM A bd keep KF F L R : forall kn i,
  (forall j, In j (fail_pos IM A keep KF F L bd i kn) -> mem_nat j R = true) ->
  kn_check IM A (with_resid bd R) keep KF F L i kn = true.
Proof.
  induction kn as [|k r IH]; intros i Hin; cbn [kn_check]; [reflexivity|].
  cbn [fail_pos] in Hin. rewrite kentry_check_resid.
  replace (bd_resid (with_resid bd R)) with R by (destruct bd; reflexivity).
  destruct (kentry_check IM A bd keep KF F L k) eqn:Ek.
  - rewrite orb_true_r. cbn [andb]. apply IH. exact Hin.
  - rewrite (Hin i (or_introl eq_refl)). cbn [orb andb]. apply IH. intros j Hj. apply Hin. right. exact Hj.
Qed.

Lemma mem_nat_in j R : In j R -> mem_nat j R = true.
Proof. intros Hj. unfold mem_nat. apply existsb_exists. exists j. split; [exact Hj | apply Nat.eqb_refl]. Qed.

Lemma bridge_check_split IM A Rb Lim BD keep KF F L CS :
  bridge_check IM A Rb Lim BD keep KF F L (cs_nokn CS) = true ->
  kn_check IM A BD keep KF F L 0 (AX2.s_know (CAP.a_ss CS)) = true ->
  bridge_check IM A Rb Lim BD keep KF F L CS = true.
Proof.
  destruct CS as [ss mps tot ylo eag vis gh ab brk fd tid]. destruct ss as [pc regs lg kn nx].
  unfold bridge_check, cs_nokn, CAP.with_ss.
  cbn [CAP.a_ss CAP.a_maps CAP.a_totsz CAP.a_ylo CAP.a_eager CAP.a_vis CAP.a_ghost CAP.a_abytes CAP.a_brk CAP.a_fd CAP.a_tidset
       AX2.s_pc AX2.s_regs AX2.s_log AX2.s_know AX2.s_next].
  cbv zeta. intros H Hk. rewrite Hk. cbn [kn_check] in H. exact H.
Qed.

Definition leaf_chkL2 (k : Z) (TB : list (int * Z * Z)) (CSL : list CAP.acs) (XRNG : nat -> Z -> Z -> bool)
    (XCHK : CAP.acs -> bdata -> fstate -> fledger -> bool) (x : fstate * fledger * int * stop) : bool :=
  let F := fst (fst (fst x)) in let L := snd (fst (fst x)) in
  existsbL (fun CS =>
    match br_infer IMH F L CS [] (TEQ k) TB 192 [] kit_pins with
    | Some bd0 =>
        if maps_check bd0 F L (CAP.a_maps CS) (fl_maps L) then
        if brk_check bd0 F L (CAP.a_brk CS) then
          let bd := with_resid bd0 (fail_pos IMH H0T KEEP (kfacts k) F L bd0 0 (AX2.s_know (CAP.a_ss CS))) in
          bridge_check IMH H0T RB LIM bd KEEP (kfacts k) F L (cs_nokn CS)
          && sinv_check (bd_vt bd) (f_mem F) (bd_tl bd) (bd_xt bd) 1%uint63 8388608
          && (bd_ts bd =? 1)%uint63 && (bd_tc bd =? 8388608)
          && match CAP.a_fd CS with CAP.FdStd => true | _ => false end
          && CAP.a_tidset CS
          && resid_chk XRNG k CS bd F L
          && XCHK CS bd F L
        else false else false
    | None => false
    end) CSL.

Lemma leaf_chkL2_ok k TB CSL XRNG XCHK x : leaf_chkL2 k TB CSL XRNG XCHK x = true -> leaf_chk k TB CSL XRNG XCHK x = true.
Proof.
  unfold leaf_chkL2. cbv zeta. rewrite existsbL_eq. intros Hc. apply existsb_exists in Hc as (CS & Hin & Hb).
  set (F := fst (fst (fst x))) in *. set (L := snd (fst (fst x))) in *.
  destruct (br_infer IMH F L CS [] (TEQ k) TB 192 [] kit_pins) as [bd0|] eqn:Ebr; [|discriminate].
  destruct (maps_check bd0 _ _ _ _); [|discriminate]. destruct (brk_check bd0 _ _ _); [|discriminate].
  unfold leaf_chk. cbv zeta. fold F L. apply existsb_exists. exists CS. split; [exact Hin|].
  unfold br_infer_auto. rewrite Ebr. fold (with_resid bd0 (fail_pos IMH H0T KEEP (kfacts k) F L bd0 0 (AX2.s_know (CAP.a_ss CS)))).
  set (bd := with_resid bd0 (fail_pos IMH H0T KEEP (kfacts k) F L bd0 0 (AX2.s_know (CAP.a_ss CS)))) in *.
  assert (Hkn : kn_check IMH H0T bd KEEP (kfacts k) F L 0 (AX2.s_know (CAP.a_ss CS)) = true)
    by (apply kn_check_auto; intros j Hj; exact (mem_nat_in j _ Hj)).
  destruct (bridge_check IMH H0T RB LIM bd KEEP (kfacts k) F L (cs_nokn CS)) eqn:Ebc; [|discriminate Hb].
  rewrite (bridge_check_split _ _ _ _ _ _ _ _ _ _ Ebc Hkn). exact Hb.
Qed.

Lemma forallb_leaf_chkL2_ok k TB CSL XRNG XCHK l :
  forallb (leaf_chkL2 k TB CSL XRNG XCHK) l = true -> forallb (leaf_chk k TB CSL XRNG XCHK) l = true.
Proof.
  intros Hc. apply forallb_forall. intros x Hx. rewrite forallb_forall in Hc. exact (leaf_chkL2_ok _ _ _ _ _ x (Hc x Hx)).
Qed.

Lemma forallb_leaf_chkL_ok k TB CSL XRNG XCHK l :
  forallb (leaf_chkL k TB CSL XRNG XCHK) l = true -> forallb (leaf_chk k TB CSL XRNG XCHK) l = true.
Proof.
  intros Hc. apply forallb_forall. intros x Hx. rewrite forallb_forall in Hc. exact (leaf_chkL_ok _ _ _ _ _ x (Hc x Hx)).
Qed.
