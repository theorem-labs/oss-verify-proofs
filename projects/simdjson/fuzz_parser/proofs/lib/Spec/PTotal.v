(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState ITree Nodes Decode Image.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe MPaths STree Malloc MallocCtrl KInv KStep KLink KEv Relim ProgP StepB RSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation M := Monad.M.

(* [comment removed for export] *)
Lemma dec_mmap_err_errno : forall atop len avoid rsp e,
  dec_mmap atop len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); congruence.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

Lemma dec_mmap_none_err_errno : forall atop len avoid rsp e,
  dec_mmap_none atop len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap_none in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|]].
  - destruct cs; [|discriminate]. destruct (errno_of r); congruence.
  - destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

Lemma dec_mprotect_err_errno : forall addr len rsp e,
  dec_mprotect addr len rsp = Some (RgErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros addr len [r ws zs us cs ci] e H. unfold dec_mprotect in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); [congruence|]. destruct (_ =? _); discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PhiP (n : node) (mo : Model) : Prop :=
  minv mo /\ m_halted mo = None /\ nsafe n mo /\ NF n mo.

(* [comment removed for export] *)
Lemma nstep_progress_brk : forall req mo, exists rsp mo' evs, nstep (NBrk req) mo rsp mo' evs.
Proof.
  intros req mo. pose proof (receptive (pure_input 214 [Z_to_bv 64 req]) mo) as Hr.
  destruct (syscall_spec_witness (pure_input 214 [Z_to_bv 64 req]) mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_brk_iff. split; [|exact Hns2].
    rewrite <- (check_syscall_brk (pure_input 214 [Z_to_bv 64 req])) by reflexivity.
    apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_brk (pure_input 214 [Z_to_bv 64 req])) in Hr by reflexivity. cbn [in_arg in_args nth pure_input] in Hr.
    revert Hr. destruct (eff0 (Z_to_bv 64 0)) as [r ws zs us cs ci] eqn:Ee. unfold check_brk.
    destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate]. destruct (_ && _); discriminate.
Qed.

Lemma nstep_progress_mmap : forall addr len prot flags mo,
  nsafe (NMmap addr len prot flags) mo -> mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  exists rsp mo' evs, nstep (NMmap addr len prot flags) mo rsp mo' evs.
Proof.
  intros addr len prot flags mo Hsafe Hnr.
  set (i := pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_mmap_iff. split; [exact Hnr|]. split; [|exact Hns2].
    rewrite <- (check_syscall_mmap i) by reflexivity. apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_mmap i) in Hr by reflexivity. cbn [in_arg in_args nth pure_input i] in Hr.
    exact (mmap_safe_no_unmodeled _ _ _ _ _ _ _ _ Hsafe Hr).
Qed.

Lemma nstep_progress_munmap : forall addr len mo,
  nsafe (NMunmap addr len) mo -> exists rsp mo' evs, nstep (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hsafe. set (i := pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - exists eff, mo', evs. apply nstep_munmap_iff. rewrite <- (check_syscall_munmap i) by reflexivity. apply check_syscall_ok_iff. exact Hr.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_munmap i) in Hr by reflexivity. cbn [in_arg in_args nth pure_input i] in Hr.
    exact (munmap_safe_no_unmodeled _ _ _ _ Hsafe Hr).
Qed.

Lemma nstep_progress_mprotect : forall addr len prot mo,
  nsafe (NMprotect addr len prot) mo -> exists rsp mo' evs, nstep (NMprotect addr len prot) mo rsp mo' evs.
Proof.
  intros addr len prot mo Hsafe. set (i := pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]).
  pose proof (receptive i mo) as Hr.
  destruct (syscall_spec_witness i mo) as [eff mo' evs|] eqn:E.
  - destruct (exists_nonspurious ACFG _ _ _ _ _ Hr) as (eff2 & mo2 & evs2 & Hs2 & Hns2).
    exists eff2, mo2, evs2. apply nstep_mprotect_iff. split; [|exact Hns2].
    rewrite <- (check_syscall_mprotect i) by reflexivity. apply check_syscall_ok_iff. exact Hs2.
  - exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr.
    rewrite (check_syscall_mprotect i) in Hr by reflexivity. cbn [in_arg in_args nth pure_input i] in Hr.
    exact (mprotect_safe_no_unmodeled _ _ _ _ _ Hsafe Hr).
Qed.

Lemma nstep_progress_settid : forall mo, exists rsp mo' evs, nstep NSetTid mo rsp mo' evs.
Proof.
  intros mo. cbn [nstep]. destruct (m_tid mo) as [t0|] eqn:E.
  - exists (eff0 t0), mo, []. split; [reflexivity|]. exists t0. auto.
  - exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) mo), []. split; [reflexivity|]. exists (Z_to_bv 64 1). split; [reflexivity|].
    rewrite unsigned_lit by lia. unfold Fork.PID_MAX_ENVELOPE. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma tglob_PhiP_intro : forall {R} (t : itree node R) mo,
  minv mo -> m_halted mo = None -> tsafe nstep nsafe t mo -> tnf t mo -> tglob nstep PhiP t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo Hmi Hh Hs Hn; cbn -[NF]; [exact I|].
  cbn -[NF] in Hs, Hn. destruct Hs as [Hsafe Hs]. destruct Hn as [HNF Hn].
  split; [split; [exact Hmi|]; split; [exact Hh|]; split; [exact Hsafe| exact HNF]|].
  intros rsp mo' evs Hst. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi'].
  apply IH; [exact Hmi'| exact Hh'| exact (Hs _ _ _ Hst)| exact (Hn _ _ _ Hst)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition good_ans (e : Malloc.ev) (z : Z) : Prop :=
  match e with
  | EMmap a len prot flags => Z.land flags MAP_FIXED_Z =? 0 = true -> Malloc.is_err z = false
  | EMprotect _ _ _ => z = 0
  | _ => True
  end.

(* [comment removed for export] *)
Fixpoint sgood {R} (P : R -> Prop) (t : stree Malloc.ev Z R) : Prop :=
  match t with
  | SRet r => P r
  | SVis (EUndef _) _ => True
  | SVis (EPeek _ _ _) _ => True
  | SVis e k => forall z, good_ans e z -> sgood P (k z)
  end.

Lemma sgood_vis {R} (P : R -> Prop) e k : (forall z, good_ans e z -> sgood P (k z)) -> sgood P (SVis e k).
Proof. intros H. destruct e; cbn; auto. Qed.

Lemma sgood_bind {A B} (P1 : A -> Prop) (P : B -> Prop) (t : stree Malloc.ev Z A) (f : A -> stree Malloc.ev Z B) :
  sgood P1 t -> (forall a, P1 a -> sgood P (f a)) -> sgood P (sbind t f).
Proof.
  induction t as [r|e k IH]; intros Ht Hf; cbn [sbind].
  - apply Hf. exact Ht.
  - destruct e; cbn in Ht |- *; auto.
Qed.

Lemma sgood_mono {R} (P P' : R -> Prop) (t : stree Malloc.ev Z R) : sgood P t -> (forall r, P r -> P' r) -> sgood P' t.
Proof. induction t as [r|e k IH]; intros Ht HP; cbn in *; [auto|]. destruct e; auto; intros z Hz; apply IH; auto. Qed.

Section Walk.
Context {R : Type}.
Variable P : R -> Prop.
Local Notation sgood := (sgood P).

Ltac sg_leaf := first [ assumption | exact I | apply sgood_vis ].

Lemma guard_sg tag c (k bail : Malloc.M R) : sgood k -> sgood (guard tag c k bail).
Proof. intros Hk. unfold guard. destruct c; [exact Hk| exact I]. Qed.

Lemma bad_answer_sg (bail : Malloc.M R) : sgood (bad_answer bail).
Proof. exact I. Qed.

Lemma queue_sg h m st (k : mstate -> Malloc.M R) bail : (forall st', sgood (k st')) -> sgood (queue h m st k bail).
Proof. intros Hk. unfold queue. apply guard_sg. apply guard_sg. destruct (get_head st h); apply Hk. Qed.

Lemma free_meta_sg m st (k : mstate -> Malloc.M R) bail : (forall st', sgood (k st')) -> sgood (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply queue_sg. exact Hk. Qed.

Lemma activate_group_sg m st (k : mstate -> Z -> Malloc.M R) bail : (forall st' z, sgood (k st' z)) -> sgood (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply guard_sg. apply Hk. Qed.

Lemma am_take_sg st (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk| exact I]. Qed.

Lemma am_carve_sg st p (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply am_take_sg. exact Hk. Qed.

Lemma am_finish_sg st nu (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu); [|apply am_carve_sg; exact Hk].
  cbn -[am_carve]. intros z ->. cbn -[am_carve]. apply am_carve_sg. exact Hk.
Qed.

Lemma am_after_brk_sg st nu (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [|apply am_finish_sg; exact Hk].
  cbn -[am_finish new_region Malloc.mmap_answer_ok Malloc.is_err]. intros z Hz. destruct (negb (Malloc.mmap_answer_ok _ _ _ z)); [exact I|].
  rewrite (Hz eq_refl). destruct (new_region RKMeta z _ st) as [st1 rid]. apply am_finish_sg. exact Hk.
Qed.

(* [comment removed for export] *)
Ltac sgauto Hk :=
  repeat first
    [ exact I
    | apply Hk
    | apply am_after_brk_sg; [exact Hk]
    | apply am_finish_sg; [exact Hk]
    | apply am_take_sg; [exact Hk]
    | apply guard_sg
    | progress (cbv zeta)
    | lazymatch goal with
      | |- sgood (SVis _ _) => apply sgood_vis; intros ? ?
      | |- sgood (if ?c then _ else _) => destruct c
      | |- sgood (match ?x with _ => _ end) => destruct x
      end ].

Lemma alloc_meta_sg st (k : mstate -> optr -> Malloc.M R) bail : (forall st' m, sgood (k st' (Some m))) -> sgood (alloc_meta st k bail).
Proof. intros Hk. unfold alloc_meta. sgauto Hk. Qed.

Lemma ta_fin_sg st m mask (k : mstate -> Z -> Malloc.M R) : (forall st' z, sgood (k st' z)) -> sgood (ta_fin st m mask k).
Proof. intros Hk. unfold ta_fin. apply Hk. Qed.

Lemma try_avail_sg sc st (k : mstate -> Z -> Malloc.M R) bail : (forall st' z, sgood (k st' z)) -> sgood (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail.
  repeat first
    [ exact I
    | apply Hk
    | apply ta_fin_sg; [exact Hk]
    | apply guard_sg
    | apply activate_group_sg; intros ? ?
    | progress (cbv zeta)
    | lazymatch goal with
      | |- sgood (if ?c then _ else _) => destruct c
      | |- sgood (match ?x with _ => _ end) => destruct x
      end ].
Qed.

Lemma ag_tail_sg lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) : (forall st' g, sgood (k st' (Some g))) -> sgood (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

Lemma alloc_group_sg lay (aslot : mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R) st sc req (k : mstate -> optr -> Malloc.M R) bail :
  (forall st' g, sgood (k st' (Some g))) ->
  (forall st' sc' req' k', (forall st'' idx, 0 <= idx -> sgood (k' st'' idx)) -> sgood (aslot st' sc' req' k' bail)) ->
  sgood (alloc_group R lay aslot st sc req k bail).
Proof.
  intros Hk Has. unfold alloc_group. apply alloc_meta_sg. intros st1 m.
  repeat first
    [ exact I
    | apply ag_tail_sg; [exact Hk]
    | progress (cbv zeta)
    | lazymatch goal with
      | |- sgood (SVis _ _) => apply sgood_vis; intros ? HANS
      | |- sgood (if Malloc.is_err ?r then _ else _) => rewrite (HANS eq_refl)
      | |- sgood (if ?c then _ else _) => destruct c
      | |- sgood (match ?x with _ => _ end) => destruct x
      | |- sgood (aslot _ _ _ _ _) => apply Has; intros ? idx Hidx; replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia)
      end ].
Qed.

Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma alloc_slot_sg lay : forall fuel st sc req (k : mstate -> Z -> Malloc.M R) bail,
  (forall st' idx, 0 <= idx -> sgood (k st' idx)) -> sgood (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply try_avail_sg. intros st1 first. destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply alloc_group_sg.
  - intros st2 g. cbn. apply queue_sg. intros st4. apply Hk. lia.
  - intros st' sc' req' k' Hk'. apply IH. exact Hk'.
Qed.

Lemma malloc_small_ctrl_sg lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  (forall st' g i, sgood (k st' (Some (g, i)))) -> sgood (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl. cbn beta iota zeta.
  match goal with |- sgood (match ?g with _ => _ end) => destruct g as [gp|] end;
    [match goal with |- sgood (if ?c then _ else _) => destruct c end; [apply Hk|] |];
    (apply alloc_slot_sg; intros st1 idx Hidx; replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia);
     destruct (active st1 _) as [gp'|]; [apply Hk| exact I]).
Qed.
End Walk.

Lemma malloc_core_sg lay st n : size_overflows n = false ->
  sgood (fun r : mstate * option (aptr * Z) => snd r <> None) (malloc_core lay st n).
Proof.
  intros Hov. unfold malloc_core. rewrite Hov.
  destruct (MMAP_THRESHOLD <=? n).
  - repeat first
      [ exact I
      | progress (cbv zeta)
      | lazymatch goal with
        | |- sgood _ (SRet _) => cbn; discriminate
        | |- sgood _ (Malloc.ret _) => cbn; discriminate
        | |- sgood _ (SVis _ _) => apply sgood_vis; intros ? HANS
        | |- sgood _ (if Malloc.is_err ?r then _ else _) => rewrite (HANS eq_refl)
        | |- sgood _ (if ?c then _ else _) => destruct c
        | |- sgood _ (match ?x with _ => _ end) => destruct x
        | |- sgood _ (alloc_meta _ _ _) => apply alloc_meta_sg; intros ? ?
        end ].
  - apply malloc_small_ctrl_sg. intros st' g i. cbn. discriminate.
Qed.

Lemma cmalloc_sg cs n : size_overflows n = false ->
  sgood (fun r : mstate * option cptr => snd r <> None) (cmalloc cs n).
Proof.
  intros Hov. unfold cmalloc. eapply sgood_bind; [apply malloc_core_sg; exact Hov|].
  intros [st1 [[g idx]|]] H; cbn in H |- *; [discriminate| exfalso; apply H; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma is_err_of_addr_ok : forall atop len avoid a, 0 < len -> atop < 2^63 -> mmap_addr_ok atop len avoid a = true -> Malloc.is_err a = false.
Proof.
  intros atop len avoid a Hlen Hat H. apply mmap_addr_ok_true in H as [(_ & Ha & Hc) _].
  pose proof (mmap_len_ge len Hlen). unfold Malloc.is_err, Malloc.TWO64. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma tpath_sys_then {St A B} (n : node) (dec : resp -> option A) (k : A -> M St B) (s : St) mo tr x mo' :
  tpath nstep (mbind (msys n dec) k s) mo tr x mo' ->
  exists rsp mo1 evs, nstep n mo rsp mo1 evs /\
    ((x = Unr /\ tr = evs /\ dec rsp = None) \/ (exists a tr2, dec rsp = Some a /\ tpath nstep (k a s) mo1 tr2 x mo' /\ tr = evs ++ tr2)).
Proof.
  intros Hp. apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)].
  - apply tpath_msys_any in Hp as (rsp & Hst & E). exists rsp, mo', tr. split; [exact Hst|]. left.
    destruct (dec rsp); [discriminate|]. auto.
  - apply tpath_msys_ok in Hp1 as (rsp & Hst & Hd & ->). exists rsp, mo1, tr1. split; [exact Hst|]. right. exists a, tr2. auto.
Qed.

Ltac pure_tail H :=
  repeat first
    [ apply tpath_mret in H as (? & ? & ?)
    | apply tpath_mupd in H as (? & ? & ?)
    | apply tpath_mbind_any in H as [[H ?]|(? & ? & ? & ? & ? & ? & H & ?)]
    | match type of H with tpath _ (match ?a with _ => _ end _) _ _ _ _ => destruct a end ];
  subst.

(* [comment removed for export] *)
Lemma ev_step_silent : forall atop e s mo tr x mo', tpath nstep (ev_step atop e s) mo tr x mo' -> tr = [].
Proof.
  intros atop e s mo tr x mo' Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [ev_step] in Hp.
  - destruct (req =? 0).
    + apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NBrk 0) _ _ _ _ I Hst) as [_ ->].
      destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
    + unfold mbind at 1 in Hp. unfold mget in Hp. cbn [ebind ITree.bind fst snd] in Hp.
      apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NBrk req) _ _ _ _ I Hst) as [_ ->].
      destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)];
      (apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC); pose proof (nstep_mm_vm_only (NMmap addr len prot flags) _ _ _ _ I Hst) as [_ ->];
       destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]; pure_tail Hp; reflexivity).
  - apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NMunmap addr len) _ _ _ _ I Hst) as [_ ->].
    destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
  - apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). pose proof (nstep_mm_vm_only (NMprotect addr len prot) _ _ _ _ I Hst) as [_ ->].
    destruct HC as [(-> & -> & _)|(a & tr2 & Hd & Hp & ->)]; [reflexivity|]. pure_tail Hp; reflexivity.
  - cbn in Hp. destruct Hp as (_ & _ & ->). reflexivity.
  - cbn in Hp. destruct Hp as (_ & _ & ->). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ev_step_noexit : forall atop e s mo tr, ~ texit nstep nexit (ev_step atop e s) mo tr.
Proof.
  intros atop e s mo tr Hx. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [ev_step] in Hx.
  - destruct (req =? 0).
    + apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)|].
      apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & ? & Hx & ?)]; [exact (texit_mupd _ _ _ _ Hx)| exact (texit_mret _ _ _ _ Hx)].
    + unfold mbind at 1 in Hx. unfold mget in Hx. cbn [ebind ITree.bind fst snd] in Hx.
      apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)|].
      destruct a; [apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & ? & Hx & ?)]; [exact (texit_mupd _ _ _ _ Hx)| exact (texit_mret _ _ _ _ Hx)]| exact (texit_mret _ _ _ _ Hx)].
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)];
      (apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)| exact (texit_mret _ _ _ _ Hx)]).
  - apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)| exact (texit_mret _ _ _ _ Hx)].
  - apply texit_mbind in Hx as [Hx|(tr1 & a & s1 & mo1 & tr2 & Hp1 & Hx & ->)]; [(eapply texit_msys_nonexit; [| exact Hx]; exact I)| exact (texit_mret _ _ _ _ Hx)].
  - exact Hx.
  - exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ev_step_good : forall atop e s mo tr z s' mo',
  atop < 2^63 ->
  match e with EMmap _ len _ _ => 0 < len | _ => True end ->
  tglob nstep PhiP (ev_step atop e s) mo -> tpath nstep (ev_step atop e s) mo tr (Ok (z, s')) mo' -> good_ans e z.
Proof.
  intros atop e s mo tr z s' mo' Hat Hlen HG Hp. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [good_ans]; auto.
  - cbn [ev_step] in HG, Hp. intros EF. rewrite EF in HG, Hp. cbn [negb] in HG, Hp.
    assert (HNF : NF (NMmap addr len prot flags) mo).
    { destruct (prot =? 0); cbn -[NF PhiP] in HG; (destruct HG as [HP _]; destruct HP as (_ & _ & _ & HNF); exact HNF). }
    destruct (prot =? 0);
      (apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC); destruct HC as [(E & _)|(a & tr2 & Hd & Hp & _)]; [discriminate|];
       apply (proj1 (tpath_mret _ _ _ _ _ _)) in Hp as (E & _ & _)).
    + destruct a as [e|x]; [exfalso; pose proof (dec_mmap_none_err_errno _ _ _ _ _ Hd) as He; rewrite (HNF _ _ _ Hst) in He; discriminate|].
      injection E as -> _. destruct (dec_mmap_none_Some _ _ _ _ _ Hd) as (ci & _ & Hok). eapply is_err_of_addr_ok; [exact Hlen| exact Hat| exact Hok].
    + destruct a as [e|x]; [exfalso; pose proof (dec_mmap_err_errno _ _ _ _ _ Hd) as He; rewrite (HNF _ _ _ Hst) in He; discriminate|].
      injection E as -> _. destruct (dec_mmap_Some _ _ _ _ _ Hd) as (ci & _ & Hok). eapply is_err_of_addr_ok; [exact Hlen| exact Hat| exact Hok].
  - cbn [ev_step] in HG, Hp.
    assert (HNF : NF (NMprotect addr len prot) mo).
    { cbn -[NF PhiP] in HG. destruct HG as [HP _]. destruct HP as (_ & _ & _ & HNF). exact HNF. }
    apply tpath_sys_then in Hp as (rsp & mo1 & evs & Hst & HC). destruct HC as [(E & _)|(a & tr2 & Hd & Hp & _)]; [discriminate|].
    apply (proj1 (tpath_mret _ _ _ _ _ _)) in Hp as (E & _ & _). injection E as -> _.
    destruct a as [e|b]; [|reflexivity]. exfalso.
    unfold dec_mprotect_rw in Hd. destruct (dec_mprotect addr len rsp) as [[e'|[|]]|] eqn:Hd'; try discriminate.
    pose proof (dec_mprotect_err_errno _ _ _ _ Hd') as He. rewrite (HNF _ _ _ Hst) in He. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ev_step_exists : forall atop e s mo,
  match e with
  | EBrk req => True
  | EMmap addr len prot flags => nsafe (NMmap addr len prot flags) mo /\ mmap_noreserve_b (Z_to_bv 64 flags) = false
  | EMunmap addr len => nsafe (NMunmap addr len) mo
  | EMprotect addr len prot => nsafe (NMprotect addr len prot) mo
  | _ => True
  end ->
  exists tr r mo', tpath nstep (ev_step atop e s) mo tr r mo'.
Proof.
  intros atop e s mo He.
  assert (SYS : forall A B (n : node) (dec : resp -> option A) (k : A -> M PState B) rsp mo1 evs,
            nstep n mo rsp mo1 evs ->
            (forall a, exists tr r mo', tpath nstep (k a s) mo1 tr r mo') ->
            exists tr r mo', tpath nstep (mbind (msys n dec) k s) mo tr r mo').
  { intros A B n dec k rsp mo1 evs Hst Hk. destruct (dec rsp) as [a|] eqn:Hd.
    - destruct (Hk a) as (tr & r & mo' & Hp). exists (evs ++ tr), r, mo'. unfold mbind. apply tpath_ebind. right.
      exists evs, (a, s), mo1, tr. split; [| auto]. unfold msys. apply tpath_enode. exists rsp. rewrite Hd. auto.
    - exists evs, Unr, mo1. unfold mbind. apply tpath_ebind. left. split; [| reflexivity]. unfold msys. apply tpath_enode. exists rsp. rewrite Hd. auto. }
  assert (RET : forall A (a : A) (s1 : PState) mo1, exists tr r mo', tpath nstep (mret a s1) mo1 tr r mo').
  { intros A a s1 mo1. exists [], (Ok (a, s1)), mo1. cbn. auto. }
  assert (UPD : forall (f : PState -> PState) (s1 : PState) mo1 B (k : unit -> M PState B),
            (forall s2, exists tr r mo', tpath nstep (k tt s2) mo1 tr r mo') -> exists tr r mo', tpath nstep (mbind (mupd f) k s1) mo1 tr r mo').
  { intros f s1 mo1 B k Hk. destruct (Hk (f s1)) as (tr & r & mo' & Hp). exists tr, r, mo'. unfold mbind, mupd. cbn [ebind ITree.bind fst snd]. exact Hp. }
  destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; cbn [ev_step].
  - destruct (req =? 0).
    + destruct (nstep_progress_brk 0 mo) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros a. apply UPD. intros s2. apply RET.
    + unfold mbind at 1. unfold mget. cbn [ebind ITree.bind fst snd].
      destruct (nstep_progress_brk req mo) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros [|]; [apply UPD; intros; apply RET| apply RET].
  - destruct He as [Hsafe Hnr]. destruct (nstep_progress_mmap addr len prot flags mo Hsafe Hnr) as (rsp & mo1 & evs & Hst).
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)]; (eapply SYS; [exact Hst|]; intros; apply RET).
  - destruct (nstep_progress_munmap addr len mo He) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros; apply RET.
  - destruct (nstep_progress_mprotect addr len prot mo He) as (rsp & mo1 & evs & Hst). eapply SYS; [exact Hst|]. intros; apply RET.
  - exists [], Unr, mo. cbn. auto.
  - exists [], Unr, mo. cbn. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma membed_silent {R} atop (t : stree Malloc.ev Z R) : forall s mo tr x mo', tpath nstep (membed atop t s) mo tr x mo' -> tr = [].
Proof.
  induction t as [r|e k IH]; intros s mo tr x mo' Hp; cbn [membed] in Hp.
  - apply tpath_mret in Hp as (_ & _ & ->). reflexivity.
  - apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & z & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + eapply ev_step_silent. exact Hp.
    + rewrite (ev_step_silent _ _ _ _ _ _ _ Hp1), (IH _ _ _ _ _ _ Hp2). reflexivity.
Qed.

Lemma membed_noexit {R} atop (t : stree Malloc.ev Z R) : forall s mo tr, ~ texit nstep nexit (membed atop t s) mo tr.
Proof.
  induction t as [r|e k IH]; intros s mo tr Hx; cbn [membed] in Hx.
  - exact (texit_mret _ _ _ _ Hx).
  - apply texit_mbind in Hx as [Hx|(tr1 & z & s1 & mo1 & tr2 & _ & Hx & ->)]; [exact (ev_step_noexit _ _ _ _ _ Hx)| exact (IH _ _ _ _ Hx)].
Qed.

Lemma ev_step_nsafe : forall atop e s mo, tglob nstep PhiP (ev_step atop e s) mo ->
  match e with
  | EMmap addr len prot flags => nsafe (NMmap addr len prot flags) mo
  | EMunmap addr len => nsafe (NMunmap addr len) mo
  | EMprotect addr len prot => nsafe (NMprotect addr len prot) mo
  | _ => True
  end.
Proof.
  intros atop e s mo HG. destruct e as [req|addr len prot flags|addr len|addr len prot|p ca hint|why]; auto; cbn [ev_step] in HG.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)]; cbn -[NF PhiP nsafe] in HG; destruct HG as [HP _]; destruct HP as (_ & _ & HS & _); exact HS.
  - cbn -[NF PhiP nsafe] in HG. destruct HG as [HP _]. destruct HP as (_ & _ & HS & _). exact HS.
  - cbn -[NF PhiP nsafe] in HG. destruct HG as [HP _]. destruct HP as (_ & _ & HS & _). exact HS.
Qed.

Lemma noreserve_MAPF : mmap_noreserve_b (Z_to_bv 64 MAPF) = false. Proof. vm_compute. reflexivity. Qed.
Lemma noreserve_MAPFX : mmap_noreserve_b (Z_to_bv 64 MAPFX) = false. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma membed_stot {R} (t : stree Malloc.ev Z R) : forall Post (G : PState -> Model -> Prop) L s mo (P : R -> Prop),
  frame_ok G -> ctree_ok L t Post -> KL L (ps_brk s) mo -> G s mo -> sgood P t -> tglob nstep PhiP (membed (ld_atop L) t s) mo ->
  (forall tr x mo', tpath nstep (membed (ld_atop L) t s) mo tr x mo' -> match x with Unr => True | Ok (r, _) => P r end)
  /\ (exists x mo', tpath nstep (membed (ld_atop L) t s) mo [] x mo').
Proof.
  induction t as [r|e k IH]; intros Post G L s mo P HG Hok HK HGs Hsg HT; cbn [membed] in HT |- *.
  - split.
    + intros tr x mo' Hp. apply tpath_mret in Hp as (-> & _ & _). exact Hsg.
    + exists (Ok (r, s)), mo. cbn. auto.
  - cbn [ctree_ok] in Hok. destruct Hok as [Hpre Hk].
    assert (NOTUP : match e with EUndef _ | EPeek _ _ _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    assert (Hsgk : forall z, good_ans e z -> sgood P (k z)) by (destruct e; cbn in Hsg; auto; destruct NOTUP).
    assert (Hlen : match e with EMmap _ len _ _ => 0 < len | _ => True end).
    { destruct e; auto. cbn in Hpre. destruct Hpre as [(_ & _ & _ & _ & Hl)|(cur & _ & _ & -> & _)]; [lia| unfold PGSZ; lia]. }
    pose proof (tglob_ebind_l nstep PhiP _ _ _ HT) as HTe.
    (* [comment removed for export] *)
    pose proof (KL_atop_lt _ _ _ HK) as HKat.
    assert (STEP : forall tr1 z s1 mo1, tpath nstep (ev_step (ld_atop L) e s) mo tr1 (Ok (z, s1)) mo1 ->
              tr1 = [] /\ answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s1) mo1 /\ G s1 mo1 /\ good_ans e z
              /\ tglob nstep PhiP (membed (ld_atop L) (k z) s1) mo1).
    { intros tr1 z s1 mo1 Hp1.
      pose proof (ev_step_spec L e G s HG Hpre s mo (conj eq_refl (conj HK HGs))) as W.
      pose proof (twf_tpath _ _ _ _ _ _ W Hp1) as HQ. cbn [fst snd] in HQ. destruct HQ as (Hans & HK1 & HG1 & _).
      split; [exact (ev_step_silent _ _ _ _ _ _ _ Hp1)|]. split; [exact Hans|]. split; [exact HK1|]. split; [exact HG1|].
      split; [exact (ev_step_good _ _ _ _ _ _ _ _ (proj2 HKat) Hlen HTe Hp1)|].
      exact (tglob_ebind_r nstep PhiP _ _ _ _ _ _ HT Hp1). }
    split.
    + intros tr x mo' Hp. apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & z & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [exact I|].
      destruct (STEP _ _ _ _ Hp1) as (-> & Hans & HK1 & HG1 & Hgood & HT1).
      rewrite <- (event_post_atop L e z) in HT1, Hp2.
      exact (proj1 (IH z Post G (event_post L e z) s1 mo1 P HG (Hk z Hans) HK1 HG1 (Hsgk z Hgood) HT1) _ _ _ Hp2).
    + assert (HEX : exists tr x mo', tpath nstep (ev_step (ld_atop L) e s) mo tr x mo').
      { apply ev_step_exists. pose proof (ev_step_nsafe (ld_atop L) e s mo HTe) as HS. destruct e; auto.
        split; [exact HS|]. cbn in Hpre. destruct Hpre as [(_ & _ & -> & _)|(cur & _ & _ & _ & _ & ->)]; [apply noreserve_MAPF| apply noreserve_MAPFX]. }
      destruct HEX as (tr0 & x0 & mo0 & Hp0). pose proof (ev_step_silent _ _ _ _ _ _ _ Hp0) as ->.
      destruct x0 as [|[z s1]].
      * exists Unr, mo0. unfold mbind. apply tpath_ebind. left. auto.
      * destruct (STEP _ _ _ _ Hp0) as (_ & Hans & HK1 & HG1 & Hgood & HT1).
        rewrite <- (event_post_atop L e z) in HT1.
        destruct (proj2 (IH z Post G (event_post L e z) s1 mo0 P HG (Hk z Hans) HK1 HG1 (Hsgk z Hgood) HT1)) as (x & mo' & Hp2).
        rewrite (event_post_atop L e z) in Hp2.
        exists x, mo'. unfold mbind. apply tpath_ebind. destruct x as [|[r s2]].
        -- right. exists [], (z, s1), mo0, []. auto.
        -- right. exists [], (z, s1), mo0, []. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Lemma vm_only_tables : forall mo mo', vm_only mo mo' -> m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo.
Proof. intros mo mo' (Hfd & _ & Hfs & _). unfold m_fds, m_fs. rewrite Hfd, Hfs. auto. Qed.

(* [comment removed for export] *)
Definition FRZ (G : PState -> Model -> Prop) (s0 : PState) (mo0 : Model) : PState -> Model -> Prop :=
  fun s mo => G s mo /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ m_fds mo = m_fds mo0 /\ m_fs mo = m_fs mo0.

Lemma frame_ok_FRZ G s0 mo0 : frame_ok G -> frame_ok (FRZ G s0 mo0).
Proof.
  intros HG s s' mo mo' Hfa Hso Hv (HGs & E1 & E2 & E3 & E4). destruct (vm_only_tables _ _ Hv) as [E5 E6].
  split; [eapply HG; eauto|]. repeat split; congruence.
Qed.

Theorem raw_malloc_STOT : forall X (G : PState -> Model -> Prop) n s mo,
  frame_ok G -> OWN X G s mo -> 0 <= n -> size_overflows n = false ->
  tglob nstep PhiP (raw_malloc n s) mo ->
  STOTP (raw_malloc n s) mo
        (fun r s' mo' => exists p, r = Some p /\ OWN (p :: X) G s' mo' /\ n < 2^63
                         /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros X G n s mo HG HO Hn Hov HT.
  pose proof (raw_malloc_spec X (FRZ G s mo) n (frame_ok_FRZ G s mo HG) Hn s mo ltac:(eapply OWN_weakG; [exact HO|]; intros; repeat split; auto)) as W.
  destruct HO as [(L & Hcr & HK & Hi) [Hnd HGs]].
  pose proof (MI_Contracts.cmalloc_contract_proof _ _ _ Hcr Hn) as Hok.
  (* [comment removed for export] *)
  unfold raw_malloc in HT, W |- *. unfold mbind at 1 in HT. unfold mbind at 1 in W. unfold mbind at 1. unfold mget in HT, W |- *. cbn [ebind ITree.bind fst snd] in HT, W |- *.
  rewrite (MI_Contracts.creach_atop _ _ Hcr) in HT, W |- *.   (* [comment removed for export] *)
  pose proof (tglob_ebind_l nstep PhiP _ _ _ HT) as HTm.
  destruct (membed_stot (cmalloc (ps_m s) n) _ (FRZ G s mo) L s mo (fun r => snd r <> None) (frame_ok_FRZ G s mo HG) Hok HK
              ltac:(repeat split; auto) (cmalloc_sg _ _ Hov) HTm) as [SOUND (x0 & mo0 & EX)].
  split; [| split].
  - intros tr x mo' Hp. pose proof (twf_tpath _ _ _ _ _ _ W Hp) as HQ. cbn [fst snd] in HQ.
    apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & [st' p] & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [destruct HQ|].
    pose proof (SOUND _ _ _ Hp1) as HS. cbn [snd] in HS. rewrite (membed_silent _ _ _ _ _ _ _ Hp1).
    unfold mbind, mupd in Hp2. cbn [ebind ITree.bind fst snd] in Hp2. apply tpath_mret in Hp2 as (-> & -> & ->). split; [reflexivity|].
    destruct p as [c|]; [| exfalso; apply HS; reflexivity]. cbn [fst snd] in HQ. destruct HQ as [HO' Hn63].
    pose proof (OWN_G _ _ _ _ HO') as (HGs' & Hso & Hfa & Hfds & Hfs).
    eexists _, _. split; [reflexivity|]. exists (c, fresh_off st' c n). split; [reflexivity|]. split; [eapply OWN_weakG; [exact HO'|]; intros [? _]; assumption|]. auto.
  - intros tr Hx. apply texit_mbind in Hx as [Hx|(tr1 & sp & s1 & mo1 & tr2 & _ & Hx & ->)]; [exact (membed_noexit _ _ _ _ _ Hx)|].
    destruct sp as [st' p]. unfold mbind, mupd in Hx. cbn [ebind ITree.bind fst snd] in Hx. exact Hx.
  - destruct x0 as [|[[st' p] s1]].
    + (* [comment removed for export] *)
      exfalso. assert (Hp : tpath nstep (mbind (membed (ld_atop L) (cmalloc (ps_m s) n)) (fun x => let '(st', p) := x in mupd (set_m st') ;;; mret match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end) s) mo [] Unr mo0).
      { unfold mbind at 1. apply tpath_ebind. left. auto. }
      exact (twf_tpath _ _ _ _ _ _ W Hp).
    + eexists _, _. unfold mbind at 1. apply tpath_ebind. right. exists [], (st', p, s1), mo0, []. split; [exact EX|]. split; [| reflexivity].
      cbn. auto.
Qed.

Theorem raw_free_STOT : forall X (G : PState -> Model -> Prop) p s mo,
  frame_ok G -> OWN (p :: X) G s mo ->
  tglob nstep PhiP (raw_free p s) mo ->
  STOTP (raw_free p s) mo
        (fun _ s' mo' => OWN X G s' mo' /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
Proof.
  intros X G p s mo HG HO HT.
  pose proof (raw_free_spec X (FRZ G s mo) p (frame_ok_FRZ G s mo HG) s mo ltac:(eapply OWN_weakG; [exact HO|]; intros; repeat split; auto)) as W.
  destruct HO as [(L & Hcr & HK & Hi) [Hnd HGs]].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  pose proof (MI_Contracts.cfree_contract_proof _ _ _ Hcr Hin) as Hok.
  unfold raw_free in HT, W |- *. unfold mbind at 1 in HT. unfold mbind at 1 in W. unfold mbind at 1. unfold mget in HT, W |- *. cbn [ebind ITree.bind fst snd] in HT, W |- *.
  rewrite (MI_Contracts.creach_atop _ _ Hcr) in HT, W |- *.
  pose proof (tglob_ebind_l nstep PhiP _ _ _ HT) as HTm.
  destruct (membed_stot (cfree (ps_m s) (Some (fst p))) _ (FRZ G s mo) L s mo (fun _ => True) (frame_ok_FRZ G s mo HG) Hok HK
              ltac:(repeat split; auto) ltac:(clear; induction (cfree (ps_m s) (Some (fst p))) as [|e k IH]; cbn; [exact I| destruct e; auto]) HTm) as [_ (x0 & mo0 & EX)].
  split; [| split].
  - intros tr x mo' Hp. pose proof (twf_tpath _ _ _ _ _ _ W Hp) as HQ. cbn [fst snd] in HQ.
    apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & st' & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [destruct HQ|].
    rewrite (membed_silent _ _ _ _ _ _ _ Hp1). apply tpath_mupd in Hp2 as (-> & -> & ->). split; [reflexivity|].
    rename HQ into HO'. pose proof (OWN_G _ _ _ _ HO') as (HGs' & Hso & Hfa & Hfds & Hfs).
    eexists _, _. split; [reflexivity|]. split; [eapply OWN_weakG; [exact HO'|]; intros [? _]; assumption|]. auto.
  - intros tr Hx. apply texit_mbind in Hx as [Hx|(tr1 & sp & s1 & mo1 & tr2 & _ & Hx & ->)]; [exact (membed_noexit _ _ _ _ _ Hx)| exact (texit_mupd _ _ _ _ Hx)].
  - destruct x0 as [|[st' s1]].
    + exfalso. assert (Hp : tpath nstep (mbind (membed (ld_atop L) (cfree (ps_m s) (Some (fst p)))) (fun st' => mupd (set_m st')) s) mo [] Unr mo0).
      { unfold mbind. apply tpath_ebind. left. auto. }
      exact (twf_tpath _ _ _ _ _ _ W Hp).
    + eexists _, _. unfold mbind. apply tpath_ebind. right. exists [], (st', s1), mo0, []. split; [exact EX|]. split; [| reflexivity]. cbn. auto.
Qed.

(* [comment removed for export] *)
Theorem startup_STOT : forall s mo, minv mo -> m_halted mo = None ->
  STOTP (startup s) mo (fun _ s' mo' => s' = s /\ m_vmmaps mo' = m_vmmaps mo /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ minv mo' /\ m_halted mo' = None).
Proof.
  intros s mo Hmi Hh. unfold startup.
  eapply STOT_bind; [| intros a s' mo' H; exact (STOT_mono _ _ _ _ _ _ (STOT_ret _ _ tt s' mo') ltac:(intros ? ? ? (-> & -> & ->); exact H))].
  apply STOT_sys.
  - intros rsp mo' evs Hst. pose proof (minv_preserved _ _ _ _ _ Hmi Hh Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_set_tid mo _ _ _ Hmi Hst) as (-> & t & Hd & _ & _). split; [reflexivity|]. exists t. split; [exact Hd|].
    cbn [nstep] in Hst. destruct Hst as (_ & t' & -> & Ht). split; [reflexivity|].
    destruct (m_tid mo); [destruct Ht as [_ ->]; auto 6| destruct Ht as [_ ->]]. rewrite m_vmmaps_with_tid, m_fds_with_tid, m_fs_with_tid. auto 6.
  - intros code mo' Hx. exact Hx.
  - apply nstep_progress_settid.
Qed.
