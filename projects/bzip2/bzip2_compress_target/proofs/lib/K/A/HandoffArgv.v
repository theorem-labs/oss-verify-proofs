(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the argument block over the launch input ProcInput, the CONFIG_RSEQ flag and the new auxv layout). *)
(* [comment removed for export] *)
(* #108 (open): the pem-donor merge of this file is unresolved (12 + 5 conflicts, TwinB / A).
   Whoever resolves it: order every [first [...]] driven over goals by [;] so that nothing
   ambiguous runs before the hypotheses that pin it.  The bare [word] goals here ([sp], [brk0],
   [mbase]) are closed WRONGLY by an early [eassumption] or [exact <var>] arm (openssl's
   AsanNodesStartXInit [wp4] mis-binding, fixed by ordering).  Pass 1: arms
   unambiguous by type or that pin by unification; pass 2: [eassumption]; pass 3: a naming
   [fail 1 "TAG:" G] arm. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound CatExec FileSim RefLayout AsanInit AgentLib StepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Frame Mem Arr RzCPS ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface D_defs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound CatExec FileSim RefLayout AsanInit AgentLib StepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Frame Mem Arr RzCPS ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* #108: per value of the CONFIG_RSEQ flag [r] (the string base moves with [AUXSZ r]); a run's
   hand-off table is checked at its own [r] *)
Definition hs_argv_ok (r : Z) (ch : acs) : bool :=
  (existsb (kentry_eqb (KWord (SA e_sp0 8) 8 (e_str0 r))) (kn ch)
   && (existsb (kentry_eqb (kw_argv1 (e_str1 r))) (kn ch) || existsb (kentry_eqb (kw_argv1 (e_argv1w r))) (kn ch)
       || match xhi (kn ch) (EVar V_ARGC) with Some h => Z.leb h 1 | None => false end))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ev_only (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ev_only a && ev_only b)%bool
  | EExt _ _ _ a => ev_only a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_agree_ev : forall b E E' e, (forall n, (n < b)%nat -> ev E n = ev E' n) ->
  expr_vars_lt b e = true -> ev_only e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e Hv. induction e; cbn [expr_vars_lt edenot ev_only]; intros H Ho;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity);
    try discriminate.
  apply Nat.ltb_lt in H. apply Hv. exact H.
Qed.

Lemma e_sp0_vars : expr_vars_lt NX0 e_sp0 = true /\ ev_only e_sp0 = true. Proof. split; reflexivity. Qed.
(* over the two values of the flag: [mkAlu]'s linear normal form does not reduce under a symbolic
   [AUXSZ r], so the check is made on the closed [rseq_z b] *)
Lemma e_str0_vars : forall b, expr_vars_lt NX0 (e_str0 (rseq_z b)) = true /\ ev_only (e_str0 (rseq_z b)) = true.
Proof. intros [|]; split; reflexivity. Qed.
Lemma e_str1_vars : forall b, expr_vars_lt NX0 (e_str1 (rseq_z b)) = true /\ ev_only (e_str1 (rseq_z b)) = true.
Proof. intros [|]; split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma argc_vars : expr_vars_lt NX0 (EVar V_ARGC) = true /\ ev_only (EVar V_ARGC) = true. Proof. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Instance ha_fx : PropExec.FPState := PropExec.fx0.

Section Argv.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (FS0 : Fs.Fs).
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation execfn := (in_execfn inp).
#[local] Notation top := (ed_top rdraw).
#[local] Notation rseq := (kb_rseq (in_kernel inp)).
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
#[local] Notation entryw := (Z_to_bv 64 (Z.of_N apc)).
#[local] Notation bsb := (entry_stack_image inp mbase ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw).
#[local] Notation CSO := (Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))).
#[local] Notation LSTR := (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).

#[local] Notation SINV := (SINV0 ph apc sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation E0 := (AsanInit.E0 sp rdraw brk0 inp).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.
Hypothesis HT : hs_argv_ok RZ ch = true.

#[local] Notation m := (mH FULL model A').

Let dHS : nat -> option acs := fun _ => None.
Let dXN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let dXE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let dXB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

Lemma ha_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E1 a H. exact (argH0_high apc sp rdraw inp Hsp Hva E1 a H). Qed.

Lemma ha_vars : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> edenot E e = edenot E0 e.
Proof.
  intros e H1 H2. destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [Hv _].
  exact (edenot_agree_ev NX0 E E0 e Hv H1 H2).
Qed.

Lemma ha_u : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> APS.uE E e = APS.uE E0 e.
Proof. intros e H1 H2. unfold APS.uE. rewrite (ha_vars e H1 H2). reflexivity. Qed.

(* [comment removed for export] *)
Lemma ha_block : forall a : word, argH E a = true -> FULL a = wrap_mem inp mbase ph entryw sp rdraw a.
Proof. intros a Ha. destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [_ Hm]. exact (Hm a Ha). Qed.

(* [comment removed for export] *)
Lemma ha_visible : forall a : word, alloc_top (m_vmmaps model) <= bv_unsigned a < 2 ^ 47 -> m a = FULL a.
Proof.
  intros a [Ha1 Ha2]. unfold mH, mrestrict.
  assert (Hh : HID A' model a = false).
  { unfold HID, mkH. apply orb_false_iff. split; [|apply Z.leb_gt; exact Ha2].
    destruct (page_in_ranges (page_base a) (m_vm_lazy model)) eqn:Hl; [|reflexivity]. exfalso.
    destruct (APS.page_in_ranges_in dHS dXN dXE dXB O a _ Hl) as (iv & Hin & Hr).
    pose proof (proj1 (Forall_forall _ _) (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as [L1 L2]. lia. }
  rewrite Hh. reflexivity.
Qed.


Lemma ha_sp0 : APS.uE E e_sp0 = usp.
Proof.
  rewrite (ha_u e_sp0 (proj1 e_sp0_vars) (proj2 e_sp0_vars)).
  exact (u_e_sp0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau).
Qed.

Lemma ha_argc : APS.uE E (EVar V_ARGC) = Z.of_nat (length argv).
Proof.
  rewrite (ha_u (EVar V_ARGC) (proj1 argc_vars) (proj2 argc_vars)).
  destruct (uE0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as (_ & _ & U & _). exact U.
Qed.

Lemma ha_lens : 1 <= Z.of_nat (length argv) <= 1024 /\ 0 <= Z.of_nat (length envp) <= 256
  /\ sp_window_lo <= usp <= sp_window_hi.
Proof.
  pose proof (len_av apc sp rdraw inp Hva). pose proof (len_ev apc sp rdraw inp Hve).
  destruct Hsp as (H1 & H2 & _). repeat split; assumption || lia.
Qed.

(* the block: sp .. ed_top; the strings end eight bytes below ed_top.  Shape: openssl/pem
   A/HandoffArgv ha_layout (shape only, not green there); this tree's AsanInit lemmas. *)
Lemma ha_layout : usp + Z.of_nat (length bsb) <= 2 ^ 47
  /\ Z.of_nat (length bsb) = CSO + LSTR + 8
  /\ 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 482 <= Z.of_nat (length bsb)
  /\ (usp + Z.of_nat (length bsb)) mod 8 = 0
  /\ usp + Z.of_nat (length bsb) = bv_unsigned top.
Proof.
  pose proof (usp_fit ph apc sp rdraw brk0 mbase inp Hlau) as F.
  pose proof (length_bsb_sum ph apc sp rdraw brk0 mbase inp Hlau) as L.
  pose proof (bsb_ge ph apc sp rdraw brk0 mbase inp Hva Hlau) as G.
  pose proof (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau) as T.
  assert (Htop : bv_unsigned top mod 4096 = 0).
  { destruct Hlau as (Hst & _ & _). destruct Hst as (Hm & _ & _). unfold page_size in Hm. exact Hm. }
  assert (CS : CSO = Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
    by (unfold cat_string_off; rewrite Nat2Z.inj_add; reflexivity).
  assert (M8 : (usp + Z.of_nat (length bsb)) mod 8 = 0).
  { rewrite T. replace (usp + (bv_unsigned top - usp)) with (bv_unsigned top) by lia. clear - Htop.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  split; [exact F|]. split; [rewrite CS; lia|]. split; [exact G|]. split; [exact M8 | lia].
Qed.

(* argv[k]'s address: the string area at the top of the block *)
Lemma ha_ptrk : forall k, (k < length argv)%nat ->
  bv_unsigned (cat_argv_ptr top argv envp execfn k) = usp + CSO + Z.of_nat (total_arg_bytes_nat (firstn k argv))
  /\ Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (length execfn) + 1 = LSTR.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2). split.
  - rewrite (u_cat_argv_ptr Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau S1 S2 k Hk). rewrite Nat2Z.inj_add. lia.
  - unfold launch_string_bytes. rewrite ?length_flatten_strings. lia.
Qed.

Lemma ha_ptr0 : edenot E (e_str0 RZ) = cat_argv_ptr top argv envp execfn 0.
Proof.
  rewrite (ha_vars (e_str0 RZ) (proj1 (e_str0_vars rseq)) (proj2 (e_str0_vars rseq))).
  pose proof (u_e_str0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as U1.
  destruct (ha_ptrk 0 ltac:(destruct ha_lens as (L1 & _); lia)) as [U2 _].
  replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in U2 by reflexivity.
  unfold cat_string_off in U2. apply bv_eq. unfold APS.uE in U1. rewrite U1, U2. lia.
Qed.

Lemma ha_ptr1 : (1 < length argv)%nat -> edenot E (e_str1 RZ) = cat_argv_ptr top argv envp execfn 1.
Proof.
  intros Hk.
  rewrite (ha_vars (e_str1 RZ) (proj1 (e_str1_vars rseq)) (proj2 (e_str1_vars rseq))).
  pose proof (u_e_str1 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau) as U1.
  destruct (ha_ptrk 1 Hk) as [U2 _].
  assert (T1 : total_arg_bytes_nat (firstn 1 argv) = (length (nth 0 argv []) + 1)%nat).
  { revert Hk. destruct (in_argv inp) as [|a0 rest]; intros Hk; [cbn in Hk; lia|].
    cbn. rewrite firstn_O. cbn. lia. }
  rewrite T1 in U2. unfold cat_string_off in U2. apply bv_eq. unfold APS.uE in U1. rewrite U1, U2. lia.
Qed.

(* the word at sp0+16 the plan keeps *)
Lemma ha_word1 : (1 < length argv)%nat ->
  exists v, In (KWord (SA e_sp0 16) 8 v) (kn ch) /\ edenot E v = cat_argv_ptr top argv envp execfn 1.
Proof.
  intros Hk. unfold hs_argv_ok in HT. apply andb_prop in HT as [_ H2].
  apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]|].
  - apply existsb_exists in H2 as (K & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K.
    exists (e_str1 RZ). split; [exact Hin | exact (ha_ptr1 Hk)].
  - apply existsb_exists in H2 as (K & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K.
    exists (e_argv1w RZ). split; [exact Hin|]. rewrite <- (ha_ptr1 Hk).
    unfold e_argv1w. cbn [edenot]. apply bv_eq.
    pose proof ha_argc as U. unfold APS.uE in U. cbn [edenot] in U.
    rewrite u_mul64, u_sltu64, u64_lit, U by lia.
    replace (1 <? Z.of_nat (length argv)) with true by (symmetry; apply Z.ltb_lt; lia).
    pose proof (u64_range (edenot E (e_str1 RZ))). rewrite Z.mul_1_l, Z.mod_small by lia. reflexivity.
  - exfalso. destruct (xhi (kn ch) (EVar V_ARGC)) as [h|] eqn:Hx; [|discriminate]. apply Z.leb_le in H2.
    pose proof (xhi_sound bsegs E _ (kn ch) (EVar V_ARGC) h (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as Hb.
    pose proof ha_argc as U. unfold APS.uE in U. rewrite U in Hb. lia.
Qed.

Lemma tab_firstn_S : forall k (l : list (list byte)), (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk; destruct l as [|s0 rest]; cbn [length] in Hk; try lia.
  - cbn [firstn nth]. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - cbn [firstn nth]. rewrite !total_arg_bytes_cons. specialize (IH rest ltac:(lia)). lia.
Qed.

Lemma ha_isp : alloc_top (m_vmmaps model) = usp - 8388608.
Proof.
  destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. unfold alloc_top, stack_max_size. rewrite I1, ha_sp0. lia.
Qed.

(* argv[k]'s bytes, from the string area at the top of the block *)
Lemma ha_str : forall k, (k < length argv)%nat ->
  bytes_at bsegs m (bv_unsigned (cat_argv_ptr top argv envp execfn k)) (nth k argv [] ++ [Z_to_bv 8 0])
  /\ usp + 8 + 8 * Z.of_nat (length argv) <= bv_unsigned (cat_argv_ptr top argv envp execfn k)
  /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 <= USTACK_TOP - 9.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2).
  destruct ha_layout as (F1 & F2 & F3 & F6 & F7).
  destruct (ha_ptrk k Hk) as [Up Ls].
  pose proof (tab_firstn_S k argv Hk) as T.
  pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
  pose proof (Nat2Z.is_nonneg (length execfn)).
  pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
  assert (CS : CSO = Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
    by (unfold cat_string_off; rewrite Nat2Z.inj_add; reflexivity).
  assert (BH : 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 3) <= Z.of_nat (block_head_size rseq argv envp))
    by (unfold block_head_size, block_items; cbv zeta; lia).
  set (p := cat_argv_ptr top argv envp execfn k) in *.
  set (n := (length (nth k argv []) + 1)%nat).
  set (LB := Z.of_nat (length bsb)) in *.
  assert (Hlo : usp + CSO <= bv_unsigned p) by (rewrite Up; lia).
  assert (Hend : bv_unsigned p + Z.of_nat n <= usp + LB - 9) by (unfold n; rewrite Up; lia).
  pose proof (read_argv_cstr_k Sv48 bsegs inp mbase ph entryw sp brk0 rdraw k Hlau Hk) as RD.
  change (cat_argv_ptr top argv envp execfn k) with p in RD.
  rewrite <- (rdn_wrap_stack_above bsegs inp mbase ph entryw sp rdraw p (length (nth k argv []) + 1)) in RD
    by (unfold n in Hend; lia).
  assert (RD' : AS_rdn bsegs m p n = Some (nth k argv [] ++ [Z_to_bv 8 0])).
  { rewrite <- RD. apply rdn_ext; [unfold n in Hend; lia|]. intros x Hx. fold n in Hx.
    rewrite (ha_visible x) by (rewrite ha_isp; lia).
    apply ha_block. unfold argH0. cbv zeta. apply orb_true_iff. right. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite rdn_AS_Lib in RD'.
  split; [|split; [lia | unfold USTACK_TOP; unfold n in Hend; lia]].
  exact (rdn_bytes_at bsegs m n p _ ltac:(unfold n in Hend; lia) RD').
Qed.

(* the bytes from argv[k]'s NUL up to the next 8-byte boundary, all in the string area *)
Lemma ha_slack : forall k, (k < length argv)%nat ->
  exists slack, bytes_at bsegs m (bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1) slack
    /\ (- (bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 8.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2).
  destruct ha_layout as (F1 & F2 & F3 & F6 & F7).
  destruct (ha_ptrk k Hk) as [Up Ls].
  pose proof (tab_firstn_S k argv Hk) as T.
  pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
  pose proof (Nat2Z.is_nonneg (length execfn)).
  pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
  unfold sp_window_lo, sp_window_hi in S1, S2.
  set (LB := Z.of_nat (length bsb)) in *.
  set (off := (cat_string_off rseq sp top argv envp execfn + total_arg_bytes_nat (firstn k argv) + length (nth k argv []) + 1)%nat).
  set (q := bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1).
  assert (Hq : q = usp + Z.of_nat off) by (unfold q, off; rewrite Up; rewrite !Nat2Z.inj_add; lia).
  set (r := (- q) mod 8).
  assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hqe : q <= usp + LB - 9) by (rewrite Hq; unfold off; rewrite !Nat2Z.inj_add; lia).
  assert (Hend : q + r <= usp + LB - 8).
  { assert (BE8 : (usp + LB - 8) mod 8 = 0).
    { clear - F6. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    unfold r. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  set (slack := firstn (Z.to_nat r) (skipn off bsb)).
  assert (Hsl : length slack = Z.to_nat r).
  { unfold slack. rewrite firstn_length, skipn_length. rewrite Hq in Hend. lia. }
  exists slack. split; [|split; [rewrite Hsl; lia | rewrite Hsl; unfold USTACK_TOP; lia]].
  assert (Hsplit : bsb = firstn off bsb ++ slack ++ skipn (Z.to_nat r) (skipn off bsb)).
  { unfold slack. rewrite firstn_skipn. rewrite firstn_skipn. reflexivity. }
  pose proof (read_at_offset_image bsegs inp mbase ph entryw sp rdraw (firstn off bsb) slack (skipn (Z.to_nat r) (skipn off bsb))
                (Z.to_nat r) Hsplit Hsl ltac:(clear - F1; unfold LB in F1; lia)) as RD.
  rewrite firstn_length_le in RD by (rewrite Hq in Hend; lia).
  assert (Hw : (sp + nat_to_word off)%bv = Z_to_bv 64 q).
  { apply bv_eq. rewrite word_add_nat, u64_lit by lia. rewrite u64_lit by lia. lia. }
  rewrite Hw in RD.
  rewrite <- (rdn_wrap_stack_above bsegs inp mbase ph entryw sp rdraw (Z_to_bv 64 q) (Z.to_nat r)) in RD
    by (rewrite u64_lit by lia; lia).
  assert (Hoff : Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn) <= Z.of_nat off)
    by (unfold off, cat_string_off; rewrite !Nat2Z.inj_add; lia).
  assert (RD' : AS_rdn bsegs m (Z_to_bv 64 q) (Z.to_nat r) = Some slack).
  { rewrite <- RD. apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
    rewrite (ha_visible x) by (rewrite ha_isp; lia).
    apply ha_block. unfold argH0. cbv zeta. apply orb_true_iff. right. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; rewrite Hq in Hx; lia. }
  rewrite rdn_AS_Lib in RD'.
  pose proof (rdn_bytes_at bsegs m (Z.to_nat r) (Z_to_bv 64 q) slack ltac:(rewrite u64_lit by lia; lia) RD') as B.
  rewrite u64_lit in B by lia. exact B.
Qed.

Lemma ha_word0 : In (KWord (SA e_sp0 8) 8 (e_str0 RZ)) (kn ch).
Proof.
  unfold hs_argv_ok in HT. apply andb_prop in HT as [H1 _]. apply existsb_exists in H1 as (K & Hin & Heq).
  apply APS.kentry_eqb_eq in Heq. subst K. exact Hin.
Qed.

(* the words at sp0 .. sp0+16 the plan keeps *)
Lemma ha_kw : forall o v, In (KWord (SA e_sp0 o) 8 v) (kn ch) -> 0 <= o <= 16 ->
  bytes_at bsegs m (usp + o) (le8 (edenot E v)).
Proof.
  intros o v Hin Ho. destruct ha_lens as (L1 & L2 & S1 & S2).
  pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok ha_argH_high E ch R FULL model HC A' HA'
                (SA e_sp0 o) 8 v Hin) as K.
  pose proof ha_sp0 as U. unfold APS.uE in U. unfold AX2S.estart in K. cbn [a_base a_off] in K. rewrite U in K.
  apply K. destruct ha_layout as (F1 & F2 & F3 & _). lia.
Qed.

Lemma ha_wr : forall a bs, bytes_at bsegs m a bs -> CEIL <= a -> a + Z.of_nat (length bs) <= 2 ^ 47 ->
  wr_at bsegs m a (Z.of_nat (length bs)).
Proof.
  intros a bs (B1 & B2 & B3) Ha Hb. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hi' : (Z.to_nat i < length bs)%nat) by lia.
  pose proof (B3 (Z.to_nat i) Hi') as Hr. rewrite Z2Nat.id in Hr by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
  pose proof HULL_ok as (H0 & H1 & H2 & H3).
  assert (Hseg : find_segment bsegs (bv_unsigned (wa (a + i))) 1 = None).
  { apply SEGS_in_hull. unfold APS.in_hull. rewrite wa_unsigned by lia. apply andb_false_iff. right. apply Z.ltb_ge.
    unfold KHI, CEIL in *. lia. }
  unfold mrd in Hr. unfold wview. destruct (m (wa (a + i))) as [b'|] eqn:Hm; [discriminate|].
  exfalso. unfold PropExec.seg_rom, memory_read in Hr. cbn [Z.of_N] in Hr. rewrite Hseg in Hr. discriminate.
Qed.

(* the argv handed to main *)
Theorem hi_argv : argv_rep argv m (usp + 8).
Proof.
  destruct ha_lens as (L1 & L2 & S1 & S2). destruct ha_layout as (F1 & F2 & F3 & _).
  unfold sp_window_lo, sp_window_hi, CEIL in *.
  pose proof (ha_kw 8 (e_str0 RZ) ha_word0 ltac:(lia)) as K0. rewrite ha_ptr0 in K0.
  unfold argv_rep.
  destruct (Nat.ltb_spec 1 (length argv)) as [H2|H1].
  - destruct (ha_word1 H2) as (v & Hin & Hv).
    pose proof (ha_kw 16 v Hin ltac:(lia)) as K1. rewrite Hv in K1.
    exists [cat_argv_ptr top argv envp execfn 0; cat_argv_ptr top argv envp execfn 1].
    assert (B : bytes_at bsegs m (usp + 8) (le8 (cat_argv_ptr top argv envp execfn 0) ++ le8 (cat_argv_ptr top argv envp execfn 1))).
    { apply bytes_at_app. split; [exact K0|]. rewrite length_le8. replace (usp + 8 + Z.of_nat 8) with (usp + 16) by lia. exact K1. }
    split; [|split; [|split]].
    + unfold u64arr. cbn [u64s]. rewrite app_nil_r. split; [exact B|].
      pose proof (ha_wr _ _ B ltac:(unfold CEIL; lia) ltac:(rewrite length_app, !length_le8; lia)) as W.
      rewrite length_app, !length_le8 in W. cbn [length]. exact W.
    + cbn [length]. lia.
    + intros i s0 p Hs Hp. destruct i as [|[|i]]; cbn [nth_error] in Hp; [| |destruct i; discriminate].
      * injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_str 0 ltac:(lia)).
      * injection Hp as <-. rewrite <- (nth_error_nth argv 1 [] Hs). exact (ha_str 1 H2).
    + intros i s0 p Hs Hp. destruct i as [|[|i]]; cbn [nth_error] in Hp; [| |destruct i; discriminate].
      * injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_slack 0 ltac:(lia)).
      * injection Hp as <-. rewrite <- (nth_error_nth argv 1 [] Hs). exact (ha_slack 1 H2).
  - exists [cat_argv_ptr top argv envp execfn 0].
    split; [|split; [|split]].
    + unfold u64arr. cbn [u64s]. rewrite app_nil_r. split; [exact K0|].
      pose proof (ha_wr _ _ K0 ltac:(unfold CEIL; lia) ltac:(rewrite length_le8; lia)) as W.
      rewrite length_le8 in W. cbn [length]. exact W.
    + cbn [length]. lia.
    + intros i s0 p Hs Hp. destruct i as [|i]; cbn [nth_error] in Hp; [|destruct i; discriminate].
      injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_str 0 ltac:(lia)).
    + intros i s0 p Hs Hp. destruct i as [|i]; cbn [nth_error] in Hp; [|destruct i; discriminate].
      injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_slack 0 ltac:(lia)).
Qed.

End Argv.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound CatExec FileSim RefLayout AsanInit AgentLib StepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Frame Mem Arr RzCPS ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface D_defs HandoffKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* #108: per value of the CONFIG_RSEQ flag [r] (the string base moves with [AUXSZ r]); a run's
   hand-off table is checked at its own [r] *)
Definition hs_argv_ok (r : Z) (ch : acs) : bool :=
  (existsb (kentry_eqb (KWord (SA e_sp0 8) 8 (e_str0 r))) (kn ch)
   && (existsb (kentry_eqb (kw_argv1 (e_str1 r))) (kn ch) || existsb (kentry_eqb (kw_argv1 (e_argv1w r))) (kn ch)
       || match xhi (kn ch) (EVar V_ARGC) with Some h => Z.leb h 1 | None => false end))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ev_only (e : expr) : bool :=
  match e with
  | ELit _ | EVar _ => true
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => (ev_only a && ev_only b)%bool
  | EExt _ _ _ a => ev_only a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_agree_ev : forall b E E' e, (forall n, (n < b)%nat -> ev E n = ev E' n) ->
  expr_vars_lt b e = true -> ev_only e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e Hv. induction e; cbn [expr_vars_lt edenot ev_only]; intros H Ho;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity);
    try discriminate.
  apply Nat.ltb_lt in H. apply Hv. exact H.
Qed.

Lemma e_sp0_vars : expr_vars_lt NX0 e_sp0 = true /\ ev_only e_sp0 = true. Proof. split; reflexivity. Qed.
(* over the two values of the flag (see the twin above) *)
Lemma e_str0_vars : forall b, expr_vars_lt NX0 (e_str0 (rseq_z b)) = true /\ ev_only (e_str0 (rseq_z b)) = true.
Proof. intros [|]; split; reflexivity. Qed.
Lemma e_str1_vars : forall b, expr_vars_lt NX0 (e_str1 (rseq_z b)) = true /\ ev_only (e_str1 (rseq_z b)) = true.
Proof. intros [|]; split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma argc_vars : expr_vars_lt NX0 (EVar V_ARGC) = true /\ ev_only (EVar V_ARGC) = true. Proof. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Instance ha_fx : PropExec.FPState := PropExec.fx0.

Section Argv.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (FS0 : Fs.Fs).
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation execfn := (in_execfn inp).
#[local] Notation top := (ed_top rdraw).
#[local] Notation rseq := (kb_rseq (in_kernel inp)).
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
#[local] Notation entryw := (Z_to_bv 64 (Z.of_N apc)).
#[local] Notation bsb := (entry_stack_image inp mbase ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw).
#[local] Notation CSO := (Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))).
#[local] Notation LSTR := (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).

#[local] Notation SINV := (SINV0 ph apc sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation E0 := (AsanInit.E0 sp rdraw brk0 inp).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.
Hypothesis HT : hs_argv_ok RZ ch = true.

#[local] Notation m := (mH FULL model A').

Let dHS : nat -> option acs := fun _ => None.
Let dXN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let dXE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let dXB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

Lemma ha_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E1 a H. exact (argH0_high apc sp rdraw inp Hsp Hva E1 a H). Qed.

Lemma ha_vars : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> edenot E e = edenot E0 e.
Proof.
  intros e H1 H2. destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [Hv _].
  exact (edenot_agree_ev NX0 E E0 e Hv H1 H2).
Qed.

Lemma ha_u : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> APS.uE E e = APS.uE E0 e.
Proof. intros e H1 H2. unfold APS.uE. rewrite (ha_vars e H1 H2). reflexivity. Qed.

(* [comment removed for export] *)
Lemma ha_block : forall a : word, argH E a = true -> FULL a = wrap_mem inp mbase ph entryw sp rdraw a.
Proof. intros a Ha. destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [_ Hm]. exact (Hm a Ha). Qed.

(* [comment removed for export] *)
Lemma ha_visible : forall a : word, alloc_top (m_vmmaps model) <= bv_unsigned a < 2 ^ 47 -> m a = FULL a.
Proof.
  intros a [Ha1 Ha2]. unfold mH, mrestrict.
  assert (Hh : HID A' model a = false).
  { unfold HID, mkH. apply orb_false_iff. split; [|apply Z.leb_gt; exact Ha2].
    destruct (page_in_ranges (page_base a) (m_vm_lazy model)) eqn:Hl; [|reflexivity]. exfalso.
    destruct (APS.page_in_ranges_in dHS dXN dXE dXB O a _ Hl) as (iv & Hin & Hr).
    pose proof (proj1 (Forall_forall _ _) (APS.co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) iv Hin) as [L1 L2]. lia. }
  rewrite Hh. reflexivity.
Qed.


Lemma ha_sp0 : APS.uE E e_sp0 = usp.
Proof.
  rewrite (ha_u e_sp0 (proj1 e_sp0_vars) (proj2 e_sp0_vars)).
  exact (u_e_sp0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau).
Qed.

Lemma ha_argc : APS.uE E (EVar V_ARGC) = Z.of_nat (length argv).
Proof.
  rewrite (ha_u (EVar V_ARGC) (proj1 argc_vars) (proj2 argc_vars)).
  destruct (uE0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as (_ & _ & U & _). exact U.
Qed.

Lemma ha_lens : 1 <= Z.of_nat (length argv) <= 1024 /\ 0 <= Z.of_nat (length envp) <= 256
  /\ sp_window_lo <= usp <= sp_window_hi.
Proof.
  pose proof (len_av apc sp rdraw inp Hva). pose proof (len_ev apc sp rdraw inp Hve).
  destruct Hsp as (H1 & H2 & _). repeat split; assumption || lia.
Qed.

(* the block: sp .. ed_top; the strings end eight bytes below ed_top.  Shape: openssl/pem
   A/HandoffArgv ha_layout (shape only, not green there); this tree's AsanInit lemmas. *)
Lemma ha_layout : usp + Z.of_nat (length bsb) <= 2 ^ 47
  /\ Z.of_nat (length bsb) = CSO + LSTR + 8
  /\ 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 482 <= Z.of_nat (length bsb)
  /\ (usp + Z.of_nat (length bsb)) mod 8 = 0
  /\ usp + Z.of_nat (length bsb) = bv_unsigned top.
Proof.
  pose proof (usp_fit ph apc sp rdraw brk0 mbase inp Hlau) as F.
  pose proof (length_bsb_sum ph apc sp rdraw brk0 mbase inp Hlau) as L.
  pose proof (bsb_ge ph apc sp rdraw brk0 mbase inp Hva Hlau) as G.
  pose proof (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau) as T.
  assert (Htop : bv_unsigned top mod 4096 = 0).
  { destruct Hlau as (Hst & _ & _). destruct Hst as (Hm & _ & _). unfold page_size in Hm. exact Hm. }
  assert (CS : CSO = Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
    by (unfold cat_string_off; rewrite Nat2Z.inj_add; reflexivity).
  assert (M8 : (usp + Z.of_nat (length bsb)) mod 8 = 0).
  { rewrite T. replace (usp + (bv_unsigned top - usp)) with (bv_unsigned top) by lia. clear - Htop.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  split; [exact F|]. split; [rewrite CS; lia|]. split; [exact G|]. split; [exact M8 | lia].
Qed.

(* argv[k]'s address: the string area at the top of the block *)
Lemma ha_ptrk : forall k, (k < length argv)%nat ->
  bv_unsigned (cat_argv_ptr top argv envp execfn k) = usp + CSO + Z.of_nat (total_arg_bytes_nat (firstn k argv))
  /\ Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (length execfn) + 1 = LSTR.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2). split.
  - rewrite (u_cat_argv_ptr Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau S1 S2 k Hk). rewrite Nat2Z.inj_add. lia.
  - unfold launch_string_bytes. rewrite ?length_flatten_strings. lia.
Qed.

Lemma ha_ptr0 : edenot E (e_str0 RZ) = cat_argv_ptr top argv envp execfn 0.
Proof.
  rewrite (ha_vars (e_str0 RZ) (proj1 (e_str0_vars rseq)) (proj2 (e_str0_vars rseq))).
  pose proof (u_e_str0 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau) as U1.
  destruct (ha_ptrk 0 ltac:(destruct ha_lens as (L1 & _); lia)) as [U2 _].
  replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in U2 by reflexivity.
  unfold cat_string_off in U2. apply bv_eq. unfold APS.uE in U1. rewrite U1, U2. lia.
Qed.

Lemma ha_ptr1 : (1 < length argv)%nat -> edenot E (e_str1 RZ) = cat_argv_ptr top argv envp execfn 1.
Proof.
  intros Hk.
  rewrite (ha_vars (e_str1 RZ) (proj1 (e_str1_vars rseq)) (proj2 (e_str1_vars rseq))).
  pose proof (u_e_str1 ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau) as U1.
  destruct (ha_ptrk 1 Hk) as [U2 _].
  assert (T1 : total_arg_bytes_nat (firstn 1 argv) = (length (nth 0 argv []) + 1)%nat).
  { revert Hk. destruct (in_argv inp) as [|a0 rest]; intros Hk; [cbn in Hk; lia|].
    cbn. rewrite firstn_O. cbn. lia. }
  rewrite T1 in U2. unfold cat_string_off in U2. apply bv_eq. unfold APS.uE in U1. rewrite U1, U2. lia.
Qed.

(* the word at sp0+16 the plan keeps *)
Lemma ha_word1 : (1 < length argv)%nat ->
  exists v, In (KWord (SA e_sp0 16) 8 v) (kn ch) /\ edenot E v = cat_argv_ptr top argv envp execfn 1.
Proof.
  intros Hk. unfold hs_argv_ok in HT. apply andb_prop in HT as [_ H2].
  apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]|].
  - apply existsb_exists in H2 as (K & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K.
    exists (e_str1 RZ). split; [exact Hin | exact (ha_ptr1 Hk)].
  - apply existsb_exists in H2 as (K & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K.
    exists (e_argv1w RZ). split; [exact Hin|]. rewrite <- (ha_ptr1 Hk).
    unfold e_argv1w. cbn [edenot]. apply bv_eq.
    pose proof ha_argc as U. unfold APS.uE in U. cbn [edenot] in U.
    rewrite u_mul64, u_sltu64, u64_lit, U by lia.
    replace (1 <? Z.of_nat (length argv)) with true by (symmetry; apply Z.ltb_lt; lia).
    pose proof (u64_range (edenot E (e_str1 RZ))). rewrite Z.mul_1_l, Z.mod_small by lia. reflexivity.
  - exfalso. destruct (xhi (kn ch) (EVar V_ARGC)) as [h|] eqn:Hx; [|discriminate]. apply Z.leb_le in H2.
    pose proof (xhi_sound asegs E _ (kn ch) (EVar V_ARGC) h (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as Hb.
    pose proof ha_argc as U. unfold APS.uE in U. rewrite U in Hb. lia.
Qed.

Lemma tab_firstn_S : forall k (l : list (list byte)), (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk; destruct l as [|s0 rest]; cbn [length] in Hk; try lia.
  - cbn [firstn nth]. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - cbn [firstn nth]. rewrite !total_arg_bytes_cons. specialize (IH rest ltac:(lia)). lia.
Qed.

Lemma ha_isp : alloc_top (m_vmmaps model) = usp - 8388608.
Proof.
  destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. unfold alloc_top, stack_max_size. rewrite I1, ha_sp0. lia.
Qed.

(* argv[k]'s bytes, from the string area at the top of the block *)
Lemma ha_str : forall k, (k < length argv)%nat ->
  bytes_at asegs m (bv_unsigned (cat_argv_ptr top argv envp execfn k)) (nth k argv [] ++ [Z_to_bv 8 0])
  /\ usp + 8 + 8 * Z.of_nat (length argv) <= bv_unsigned (cat_argv_ptr top argv envp execfn k)
  /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 <= USTACK_TOP - 9.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2).
  destruct ha_layout as (F1 & F2 & F3 & F6 & F7).
  destruct (ha_ptrk k Hk) as [Up Ls].
  pose proof (tab_firstn_S k argv Hk) as T.
  pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
  pose proof (Nat2Z.is_nonneg (length execfn)).
  pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
  assert (CS : CSO = Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
    by (unfold cat_string_off; rewrite Nat2Z.inj_add; reflexivity).
  assert (BH : 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 3) <= Z.of_nat (block_head_size rseq argv envp))
    by (unfold block_head_size, block_items; cbv zeta; lia).
  set (p := cat_argv_ptr top argv envp execfn k) in *.
  set (n := (length (nth k argv []) + 1)%nat).
  set (LB := Z.of_nat (length bsb)) in *.
  assert (Hlo : usp + CSO <= bv_unsigned p) by (rewrite Up; lia).
  assert (Hend : bv_unsigned p + Z.of_nat n <= usp + LB - 9) by (unfold n; rewrite Up; lia).
  pose proof (read_argv_cstr_k Sv48 asegs inp mbase ph entryw sp brk0 rdraw k Hlau Hk) as RD.
  change (cat_argv_ptr top argv envp execfn k) with p in RD.
  rewrite <- (rdn_wrap_stack_above asegs inp mbase ph entryw sp rdraw p (length (nth k argv []) + 1)) in RD
    by (unfold n in Hend; lia).
  assert (RD' : AS_rdn asegs m p n = Some (nth k argv [] ++ [Z_to_bv 8 0])).
  { rewrite <- RD. apply rdn_ext; [unfold n in Hend; lia|]. intros x Hx. fold n in Hx.
    rewrite (ha_visible x) by (rewrite ha_isp; lia).
    apply ha_block. unfold argH0. cbv zeta. apply orb_true_iff. right. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite rdn_AS_Lib in RD'.
  split; [|split; [lia | unfold USTACK_TOP; unfold n in Hend; lia]].
  exact (rdn_bytes_at asegs m n p _ ltac:(unfold n in Hend; lia) RD').
Qed.

(* the bytes from argv[k]'s NUL up to the next 8-byte boundary, all in the string area *)
Lemma ha_slack : forall k, (k < length argv)%nat ->
  exists slack, bytes_at asegs m (bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1) slack
    /\ (- (bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 8.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2).
  destruct ha_layout as (F1 & F2 & F3 & F6 & F7).
  destruct (ha_ptrk k Hk) as [Up Ls].
  pose proof (tab_firstn_S k argv Hk) as T.
  pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
  pose proof (Nat2Z.is_nonneg (length execfn)).
  pose proof (Nat2Z.is_nonneg (block_pad_len rseq sp top argv envp execfn)).
  unfold sp_window_lo, sp_window_hi in S1, S2.
  set (LB := Z.of_nat (length bsb)) in *.
  set (off := (cat_string_off rseq sp top argv envp execfn + total_arg_bytes_nat (firstn k argv) + length (nth k argv []) + 1)%nat).
  set (q := bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1).
  assert (Hq : q = usp + Z.of_nat off) by (unfold q, off; rewrite Up; rewrite !Nat2Z.inj_add; lia).
  set (r := (- q) mod 8).
  assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hqe : q <= usp + LB - 9) by (rewrite Hq; unfold off; rewrite !Nat2Z.inj_add; lia).
  assert (Hend : q + r <= usp + LB - 8).
  { assert (BE8 : (usp + LB - 8) mod 8 = 0).
    { clear - F6. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    unfold r. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  set (slack := firstn (Z.to_nat r) (skipn off bsb)).
  assert (Hsl : length slack = Z.to_nat r).
  { unfold slack. rewrite firstn_length, skipn_length. rewrite Hq in Hend. lia. }
  exists slack. split; [|split; [rewrite Hsl; lia | rewrite Hsl; unfold USTACK_TOP; lia]].
  assert (Hsplit : bsb = firstn off bsb ++ slack ++ skipn (Z.to_nat r) (skipn off bsb)).
  { unfold slack. rewrite firstn_skipn. rewrite firstn_skipn. reflexivity. }
  pose proof (read_at_offset_image asegs inp mbase ph entryw sp rdraw (firstn off bsb) slack (skipn (Z.to_nat r) (skipn off bsb))
                (Z.to_nat r) Hsplit Hsl ltac:(clear - F1; unfold LB in F1; lia)) as RD.
  rewrite firstn_length_le in RD by (rewrite Hq in Hend; lia).
  assert (Hw : (sp + nat_to_word off)%bv = Z_to_bv 64 q).
  { apply bv_eq. rewrite word_add_nat, u64_lit by lia. rewrite u64_lit by lia. lia. }
  rewrite Hw in RD.
  rewrite <- (rdn_wrap_stack_above asegs inp mbase ph entryw sp rdraw (Z_to_bv 64 q) (Z.to_nat r)) in RD
    by (rewrite u64_lit by lia; lia).
  assert (Hoff : Z.of_nat (block_head_size rseq argv envp) + Z.of_nat (block_pad_len rseq sp top argv envp execfn) <= Z.of_nat off)
    by (unfold off, cat_string_off; rewrite !Nat2Z.inj_add; lia).
  assert (RD' : AS_rdn asegs m (Z_to_bv 64 q) (Z.to_nat r) = Some slack).
  { rewrite <- RD. apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
    rewrite (ha_visible x) by (rewrite ha_isp; lia).
    apply ha_block. unfold argH0. cbv zeta. apply orb_true_iff. right. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; rewrite Hq in Hx; lia. }
  rewrite rdn_AS_Lib in RD'.
  pose proof (rdn_bytes_at asegs m (Z.to_nat r) (Z_to_bv 64 q) slack ltac:(rewrite u64_lit by lia; lia) RD') as B.
  rewrite u64_lit in B by lia. exact B.
Qed.

Lemma ha_word0 : In (KWord (SA e_sp0 8) 8 (e_str0 RZ)) (kn ch).
Proof.
  unfold hs_argv_ok in HT. apply andb_prop in HT as [H1 _]. apply existsb_exists in H1 as (K & Hin & Heq).
  apply APS.kentry_eqb_eq in Heq. subst K. exact Hin.
Qed.

(* the words at sp0 .. sp0+16 the plan keeps *)
Lemma ha_kw : forall o v, In (KWord (SA e_sp0 o) 8 v) (kn ch) -> 0 <= o <= 16 ->
  bytes_at asegs m (usp + o) (le8 (edenot E v)).
Proof.
  intros o v Hin Ho. destruct ha_lens as (L1 & L2 & S1 & S2).
  pose proof (hk_kword asegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok ha_argH_high E ch R FULL model HC A' HA'
                (SA e_sp0 o) 8 v Hin) as K.
  pose proof ha_sp0 as U. unfold APS.uE in U. unfold AX2S.estart in K. cbn [a_base a_off] in K. rewrite U in K.
  apply K. destruct ha_layout as (F1 & F2 & F3 & _). lia.
Qed.

Lemma ha_wr : forall a bs, bytes_at asegs m a bs -> CEIL <= a -> a + Z.of_nat (length bs) <= 2 ^ 47 ->
  wr_at asegs m a (Z.of_nat (length bs)).
Proof.
  intros a bs (B1 & B2 & B3) Ha Hb. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hi' : (Z.to_nat i < length bs)%nat) by lia.
  pose proof (B3 (Z.to_nat i) Hi') as Hr. rewrite Z2Nat.id in Hr by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
  pose proof HULL_ok as (H0 & H1 & H2 & H3).
  assert (Hseg : find_segment asegs (bv_unsigned (wa (a + i))) 1 = None).
  { apply SEGS_in_hull. unfold APS.in_hull. rewrite wa_unsigned by lia. apply andb_false_iff. right. apply Z.ltb_ge.
    unfold KHI, CEIL in *. lia. }
  unfold mrd in Hr. unfold wview. destruct (m (wa (a + i))) as [b'|] eqn:Hm; [discriminate|].
  exfalso. unfold PropExec.seg_rom, memory_read in Hr. cbn [Z.of_N] in Hr. rewrite Hseg in Hr. discriminate.
Qed.

(* the argv handed to main *)
Theorem hi_argv : argv_rep argv m (usp + 8).
Proof.
  destruct ha_lens as (L1 & L2 & S1 & S2). destruct ha_layout as (F1 & F2 & F3 & _).
  unfold sp_window_lo, sp_window_hi, CEIL in *.
  pose proof (ha_kw 8 (e_str0 RZ) ha_word0 ltac:(lia)) as K0. rewrite ha_ptr0 in K0.
  unfold argv_rep.
  destruct (Nat.ltb_spec 1 (length argv)) as [H2|H1].
  - destruct (ha_word1 H2) as (v & Hin & Hv).
    pose proof (ha_kw 16 v Hin ltac:(lia)) as K1. rewrite Hv in K1.
    exists [cat_argv_ptr top argv envp execfn 0; cat_argv_ptr top argv envp execfn 1].
    assert (B : bytes_at asegs m (usp + 8) (le8 (cat_argv_ptr top argv envp execfn 0) ++ le8 (cat_argv_ptr top argv envp execfn 1))).
    { apply bytes_at_app. split; [exact K0|]. rewrite length_le8. replace (usp + 8 + Z.of_nat 8) with (usp + 16) by lia. exact K1. }
    split; [|split; [|split]].
    + unfold u64arr. cbn [u64s]. rewrite app_nil_r. split; [exact B|].
      pose proof (ha_wr _ _ B ltac:(unfold CEIL; lia) ltac:(rewrite length_app, !length_le8; lia)) as W.
      rewrite length_app, !length_le8 in W. cbn [length]. exact W.
    + cbn [length]. lia.
    + intros i s0 p Hs Hp. destruct i as [|[|i]]; cbn [nth_error] in Hp; [| |destruct i; discriminate].
      * injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_str 0 ltac:(lia)).
      * injection Hp as <-. rewrite <- (nth_error_nth argv 1 [] Hs). exact (ha_str 1 H2).
    + intros i s0 p Hs Hp. destruct i as [|[|i]]; cbn [nth_error] in Hp; [| |destruct i; discriminate].
      * injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_slack 0 ltac:(lia)).
      * injection Hp as <-. rewrite <- (nth_error_nth argv 1 [] Hs). exact (ha_slack 1 H2).
  - exists [cat_argv_ptr top argv envp execfn 0].
    split; [|split; [|split]].
    + unfold u64arr. cbn [u64s]. rewrite app_nil_r. split; [exact K0|].
      pose proof (ha_wr _ _ K0 ltac:(unfold CEIL; lia) ltac:(rewrite length_le8; lia)) as W.
      rewrite length_le8 in W. cbn [length]. exact W.
    + cbn [length]. lia.
    + intros i s0 p Hs Hp. destruct i as [|i]; cbn [nth_error] in Hp; [|destruct i; discriminate].
      injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_str 0 ltac:(lia)).
    + intros i s0 p Hs Hp. destruct i as [|i]; cbn [nth_error] in Hp; [|destruct i; discriminate].
      injection Hp as <-. rewrite <- (nth_error_nth argv 0 [] Hs). exact (ha_slack 0 ltac:(lia)).
Qed.

End Argv.
