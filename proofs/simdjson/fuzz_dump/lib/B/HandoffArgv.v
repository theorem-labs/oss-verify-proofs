(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound CatExec FileSim RefLayout AsanInit AgentLib StepTac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Frame Mem Arr RzCPS ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import RT_iface D_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Definition hs_argv_ok (ch : acs) : bool :=
  (existsb (kentry_eqb (KWord (SA e_sp0 8) 8 e_str0)) (kn ch)
   && (existsb (kentry_eqb (kw_argv1 e_str1)) (kn ch) || existsb (kentry_eqb (kw_argv1 e_argv1w)) (kn ch)
       || match xhi (kn ch) (EVar V_ARGC) with Some h => Z.leb h 1 | None => false end))%bool.

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
Lemma e_str0_vars : expr_vars_lt NX0 e_str0 = true /\ ev_only e_str0 = true. Proof. split; reflexivity. Qed.
Lemma e_str1_vars : expr_vars_lt NX0 e_str1 = true /\ ev_only e_str1 = true. Proof. split; reflexivity. Qed.
Lemma e_argv1w_vars : expr_vars_lt NX0 e_argv1w = true /\ ev_only e_argv1w = true. Proof. split; reflexivity. Qed.
Lemma argc_vars : expr_vars_lt NX0 (EVar V_ARGC) = true /\ ev_only (EVar V_ARGC) = true. Proof. split; reflexivity. Qed.

Local Instance ha_fx : PropExec.FPState := PropExec.fx0.

Section Argv.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (FS0 : Fs.Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation E0 := (AsanInit.E0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.
Hypothesis HT : hs_argv_ok ch = true.

#[local] Notation m := (mH FULL model A').

Let dHS : nat -> option acs := fun _ => None.
Let dXN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let dXE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let dXB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.

Lemma ha_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E1 a H. exact (argH0_high ph sp rdraw argv envp uid hw Hsp Hva E1 a H). Qed.

Lemma ha_vars : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> edenot E e = edenot E0 e.
Proof.
  intros e H1 H2. destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [Hv _].
  exact (edenot_agree_ev NX0 E E0 e Hv H1 H2).
Qed.

Lemma ha_u : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> APS.uE E e = APS.uE E0 e.
Proof. intros e H1 H2. unfold APS.uE. rewrite (ha_vars e H1 H2). reflexivity. Qed.

Lemma ha_block : forall a : word, argH E a = true -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a.
Proof. intros a Ha. destruct (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as [_ Hm]. exact (Hm a Ha). Qed.

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
  exact (u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
Qed.

Lemma ha_argc : APS.uE E (EVar V_ARGC) = Z.of_nat (length argv).
Proof.
  rewrite (ha_u (EVar V_ARGC) (proj1 argc_vars) (proj2 argc_vars)).
  destruct (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & U & _). exact U.
Qed.

Lemma ha_lens : 1 <= Z.of_nat (length argv) <= 1024 /\ 0 <= Z.of_nat (length envp) <= 256
  /\ sp_window_lo <= usp <= sp_window_hi.
Proof.
  pose proof (len_av ph sp rdraw argv envp uid hw Hva). pose proof (len_ev ph sp rdraw argv envp uid hw Hve).
  destruct Hsp as (H1 & H2 & _). repeat split; assumption || lia.
Qed.

Lemma ha_ptr0 : edenot E e_str0 = cat_argv_ptr sp argv envp 0.
Proof.
  destruct ha_lens as (L1 & L2 & S1 & S2).
  rewrite (ha_vars e_str0 (proj1 e_str0_vars) (proj2 e_str0_vars)).
  apply bv_eq. rewrite (u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve S1 S2 0 ltac:(lia)).
  pose proof (u_e_str0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold APS.uE in U. rewrite U.
  unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity. lia.
Qed.

Lemma ha_ptr1 : (1 < length argv)%nat -> edenot E e_str1 = cat_argv_ptr sp argv envp 1.
Proof.
  intros Hk. destruct ha_lens as (L1 & L2 & S1 & S2).
  rewrite (ha_vars e_str1 (proj1 e_str1_vars) (proj2 e_str1_vars)).
  apply bv_eq. rewrite (u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve S1 S2 1 Hk).
  pose proof (u_e_str1 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U. unfold APS.uE in U. rewrite U.
  unfold cat_struct_size, auxv_size.
  destruct argv as [|a0 rest] eqn:Hav; [cbn in Hk; lia|].
  change (firstn 1 (a0 :: rest)) with [a0]. cbn [nth total_arg_bytes_nat fold_right length]. lia.
Qed.

Lemma ha_word1 : (1 < length argv)%nat ->
  exists v, In (KWord (SA e_sp0 16) 8 v) (kn ch) /\ edenot E v = cat_argv_ptr sp argv envp 1.
Proof.
  intros Hk. unfold hs_argv_ok in HT. apply andb_prop in HT as [_ H2].
  apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]|].
  - apply existsb_exists in H2 as (K & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K.
    exists e_str1. split; [exact Hin | exact (ha_ptr1 Hk)].
  - apply existsb_exists in H2 as (K & Hin & Heq). apply APS.kentry_eqb_eq in Heq. subst K.
    exists e_argv1w. split; [exact Hin|]. rewrite <- (ha_ptr1 Hk).
    unfold e_argv1w. cbn [edenot]. apply bv_eq.
    pose proof ha_argc as U. unfold APS.uE in U. cbn [edenot] in U.
    rewrite u_mul64, u_sltu64, u64_lit, U by lia.
    replace (1 <? Z.of_nat (length argv)) with true by (symmetry; apply Z.ltb_lt; lia).
    pose proof (u64_range (edenot E e_str1)). rewrite Z.mul_1_l, Z.mod_small by lia. reflexivity.
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

Lemma ha_bsb : usp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw)) <= 2 ^ 47
  /\ Z.of_nat (cat_struct_size argv envp) + Z.of_nat (total_arg_bytes_nat argv) + 16
     <= Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw)).
Proof.
  split; [exact (usp_fit ph sp rdraw argv envp uid hw Hfit)|].
  rewrite (length_bsb_eq ph sp rdraw argv envp uid hw). unfold stack_image_size, cat_struct_size, auxv_size. cbv zeta.
  rewrite !total_arg_bytes_Z.
  match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
  assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold len in Hpd |- *. lia.
Qed.

Lemma ha_str : forall k, (k < length argv)%nat ->
  bytes_at bsegs m (bv_unsigned (cat_argv_ptr sp argv envp k)) (nth k argv [] ++ [Z_to_bv 8 0])
  /\ usp + 8 + 8 * Z.of_nat (length argv) <= bv_unsigned (cat_argv_ptr sp argv envp k)
  /\ bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1 <= USTACK_TOP - 16.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2). destruct ha_bsb as (F1 & F2).
  pose proof (u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve S1 S2 k Hk) as Up.
  pose proof (tab_firstn_S k argv Hk) as T.
  pose proof (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
  set (p := cat_argv_ptr sp argv envp k) in *.
  set (n := (length (nth k argv []) + 1)%nat).
  set (LB := Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw))) in *.
  assert (Cs : Z.of_nat (cat_struct_size argv envp) = 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)
    by (unfold cat_struct_size, auxv_size; lia).
  assert (Hlo : usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184 <= bv_unsigned p) by (rewrite Up; lia).
  assert (Hend : bv_unsigned p + Z.of_nat n <= usp + LB - 16) by (unfold n; rewrite Up; lia).
  pose proof (read_argv_cstr_k ph bsegs sp argv envp k uid hw rdraw Hk ltac:(lia)) as RD. fold p in RD.
  rewrite <- (rdn_wrap_stack_above bsegs ph sp argv envp p (length (nth k argv []) + 1) uid hw rdraw) in RD
    by (unfold n in Hend; lia).
  assert (Hisp : alloc_top (m_vmmaps model) = usp - 8388608).
  { destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. unfold alloc_top, stack_max_size. rewrite I1, ha_sp0. lia. }
  assert (RD' : AS_rdn bsegs m p n = Some (nth k argv [] ++ [Z_to_bv 8 0])).
  { rewrite <- RD. apply rdn_ext; [unfold n in Hend; lia|]. intros x Hx. fold n in Hx.
    rewrite (ha_visible x) by (rewrite Hisp; lia).
    apply ha_block. apply argH0_of_old. unfold argH0_old. cbv zeta. fold LB. apply orb_true_iff. right. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite rdn_AS_Lib in RD'.
  split; [|split; [lia | unfold USTACK_TOP; unfold n in Hend; lia]].
  exact (rdn_bytes_at bsegs m n p _ ltac:(unfold n in Hend; lia) RD').
Qed.

Lemma ha_slack : forall k, (k < length argv)%nat ->
  exists slack, bytes_at bsegs m (bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1) slack
    /\ (- (bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16.
Proof.
  intros k Hk. destruct ha_lens as (L1 & L2 & S1 & S2). destruct ha_bsb as (F1 & F2).
  pose proof (u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve S1 S2 k Hk) as Up.
  pose proof (tab_firstn_S k argv Hk) as T.
  pose proof (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
  pose proof (bsb_ge ph sp rdraw argv envp uid hw) as (G1 & G2).
  unfold sp_window_lo, sp_window_hi in S1, S2.
  assert (Hal16 : usp mod 16 = 0) by (destruct Hsp as (_ & _ & H16); exact H16).
  set (bsb := build_stack_bytes ph sp argv envp uid hw rdraw) in *.
  set (LB := Z.of_nat (length bsb)) in *.
  assert (Cs : Z.of_nat (cat_struct_size argv envp) = 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184)
    by (unfold cat_struct_size, auxv_size; lia).
  set (off := (cat_struct_size argv envp + total_arg_bytes_nat (firstn k argv) + length (nth k argv []) + 1)%nat).
  set (q := bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1).
  assert (Hq : q = usp + Z.of_nat off) by (unfold q, off; rewrite Up; lia).
  set (r := (- q) mod 8).
  assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).

  assert (Hend : q + r <= usp + LB - 16).
  { assert (BE8 : (usp + LB - 16) mod 8 = 0).
    { clear - Hal16 G2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (Hqe : q <= usp + LB - 16) by (rewrite Hq; unfold off; lia).
    unfold r. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  set (slack := firstn (Z.to_nat r) (skipn off bsb)).
  assert (Hsl : length slack = Z.to_nat r).
  { unfold slack. rewrite firstn_length, skipn_length. rewrite Hq in Hend. lia. }
  exists slack. split; [|split; [rewrite Hsl; lia | rewrite Hsl; unfold USTACK_TOP; lia]].
  assert (Hsplit : bsb = firstn off bsb ++ slack ++ skipn (Z.to_nat r) (skipn off bsb)).
  { unfold slack. rewrite firstn_skipn. rewrite firstn_skipn. reflexivity. }
  pose proof (read_at_offset_image bsegs ph sp argv envp uid hw rdraw (firstn off bsb) slack (skipn (Z.to_nat r) (skipn off bsb))
                (Z.to_nat r) Hsplit Hsl ltac:(clear - F1; unfold LB, bsb in F1; lia)) as RD.
  rewrite firstn_length_le in RD by (rewrite Hq in Hend; lia).
  assert (Hw : (sp + nat_to_word off)%bv = Z_to_bv 64 q).
  { apply bv_eq. rewrite word_add_nat, u64_lit by lia. rewrite u64_lit by lia. lia. }
  rewrite Hw in RD.
  rewrite <- (rdn_wrap_stack_above bsegs ph sp argv envp (Z_to_bv 64 q) (Z.to_nat r) uid hw rdraw) in RD
    by (rewrite u64_lit by lia; lia).
  assert (Hisp : alloc_top (m_vmmaps model) = usp - 8388608).
  { destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. unfold alloc_top, stack_max_size. rewrite I1, ha_sp0. lia. }
  assert (RD' : AS_rdn bsegs m (Z_to_bv 64 q) (Z.to_nat r) = Some slack).
  { rewrite <- RD. apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
    rewrite (ha_visible x) by (rewrite Hisp; lia).
    apply ha_block. apply argH0_of_old. unfold argH0_old. cbv zeta. fold bsb. fold LB. apply orb_true_iff. right. apply andb_true_iff.
    split; [apply Z.leb_le | apply Z.ltb_lt]; rewrite Hq in Hx; unfold off in Hx; lia. }
  rewrite rdn_AS_Lib in RD'.
  pose proof (rdn_bytes_at bsegs m (Z.to_nat r) (Z_to_bv 64 q) slack ltac:(rewrite u64_lit by lia; lia) RD') as B.
  rewrite u64_lit in B by lia. exact B.
Qed.

Lemma ha_word0 : In (KWord (SA e_sp0 8) 8 e_str0) (kn ch).
Proof.
  unfold hs_argv_ok in HT. apply andb_prop in HT as [H1 _]. apply existsb_exists in H1 as (K & Hin & Heq).
  apply APS.kentry_eqb_eq in Heq. subst K. exact Hin.
Qed.

Lemma ha_kw : forall o v, In (KWord (SA e_sp0 o) 8 v) (kn ch) -> 0 <= o <= 16 ->
  bytes_at bsegs m (usp + o) (le8 (edenot E v)).
Proof.
  intros o v Hin Ho. destruct ha_lens as (L1 & L2 & S1 & S2).
  pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok ha_argH_high E ch R FULL model HC A' HA'
                (SA e_sp0 o) 8 v Hin) as K.
  pose proof ha_sp0 as U. unfold APS.uE in U. unfold AX2S.estart in K. cbn [a_base a_off] in K. rewrite U in K.
  apply K. destruct ha_bsb as (F1 & F2).
  assert (Cs : 192 <= Z.of_nat (cat_struct_size argv envp)) by (unfold cat_struct_size, auxv_size; lia). lia.
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

Theorem hi_argv : argv_rep argv m (usp + 8).
Proof.
  destruct ha_lens as (L1 & L2 & S1 & S2). destruct ha_bsb as (F1 & F2).
  assert (Cs : 192 <= Z.of_nat (cat_struct_size argv envp)) by (unfold cat_struct_size, auxv_size; lia).
  unfold sp_window_lo, sp_window_hi, CEIL in *.
  pose proof (ha_kw 8 e_str0 ha_word0 ltac:(lia)) as K0. rewrite ha_ptr0 in K0.
  unfold argv_rep.
  destruct (Nat.ltb_spec 1 (length argv)) as [H2|H1].
  - destruct (ha_word1 H2) as (v & Hin & Hv).
    pose proof (ha_kw 16 v Hin ltac:(lia)) as K1. rewrite Hv in K1.
    exists [cat_argv_ptr sp argv envp 0; cat_argv_ptr sp argv envp 1].
    assert (B : bytes_at bsegs m (usp + 8) (le8 (cat_argv_ptr sp argv envp 0) ++ le8 (cat_argv_ptr sp argv envp 1))).
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
  - exists [cat_argv_ptr sp argv envp 0].
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
