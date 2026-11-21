(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the auxv hand-off section takes the run's whole launch input, as A/HandoffArgv.v and A/HandoffG1.v do, and reads the sp window, the auxv's address and the start block's bounds through their lemmas at that input; the slot table and [hi_auxv] name the slots of the revision's auxv layout (pairs 10, 11, 13-15, 19, 20, 23, 24), not the released model's ten contiguous pairs, and AT_NULL is not named because its index moves with the kernel's rseq flag. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_kit D_auxv HandoffKit HandoffImage HandoffArgv RT_state RT_init RT_init_mem HandoffG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hx_fx : PropExec.FPState := PropExec.fx0.

Definition auxv_slot (ch : acs) (j : nat) : option expr := kw_find (kn ch) (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j) 8.

Definition auxv_slot_ok (ch : acs) (jx : nat * (Z + nat)) : bool :=
  match auxv_slot ch (fst jx), snd jx with
  | Some v, inl z => expr_eqb v (ELit z)
  | Some v, inr k => match auxv_slot ch k with Some v' => expr_eqb v v' | None => false end
  | None, _ => false
  end.

(* LPS 727298f3: the slots [el_auxvA] names, at the revision's auxv layout (D_auxv.v:
   pair k's key in slot 2k, its value in slot 2k + 1): AT_HWCAP pair 10, AT_PAGESZ 11,
   AT_PHDR 13, AT_PHENT 14, AT_PHNUM 15, AT_UID 19, AT_EUID 20, AT_SECURE 23, AT_RANDOM 24
   (AS/AsanPlanCore.v [init_kn_with] states each of these pairs at the start).  AT_NULL is
   not listed: its pair is 26 + 2*r, which moves with the rseq flag. *)
Definition AUXV_TABLE : list (nat * (Z + nat)) :=
  [(20%nat, inl 16); (21%nat, inr 21%nat); (22%nat, inl 6); (23%nat, inl 4096);
   (26%nat, inl 3); (27%nat, inl EL_AT_PHDR); (28%nat, inl 4); (29%nat, inl 56); (30%nat, inl 5); (31%nat, inl 11);
   (38%nat, inl 11); (39%nat, inr 39%nat); (40%nat, inl 12); (41%nat, inr 39%nat);
   (46%nat, inl 23); (47%nat, inl 0); (48%nat, inl 25); (49%nat, inr 49%nat)].

Definition hs_auxv_ok (ch : acs) : bool :=
  (lit_word ch EL_AUXV_CELL 8 e_auxv && forallb (auxv_slot_ok ch) AUXV_TABLE)%bool.

Section Aux.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (FS0 : Fs.Fs).
(* the launch, as AS/AsanInit.v's Section Init names it: the run's whole input [inp]
   (A/HandoffArgv.v and A/HandoffG1.v take it the same way) *)
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation SINV := (SINV0 A ph sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation E0 := (AsanInit.E0 sp rdraw brk0 inp).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation bsb := (entry_stack_image inp mbase ph (Z_to_bv 64 (a_entry A)) sp rdraw).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Lemma hx_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. intros E1 a H. eapply argH0_high; eassumption. Qed.

Let AH := hx_argH_high.

Let av : Z := usp + 8 * argc + 8 * envc + 24.

Lemma hx_usp : sp_window_lo <= usp <= sp_window_hi /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof.
  assert (L : 1 <= argc <= 1024 /\ 0 <= envc <= 256 /\ sp_window_lo <= usp <= sp_window_hi) by (eapply ha_lens; eassumption).
  tauto.
Qed.

Lemma hx_u : forall e, expr_vars_lt NX0 e = true -> ev_only e = true -> APS.uE E e = APS.uE E0 e.
Proof. intros e H1 H2. eapply ha_u; eassumption. Qed.

Lemma hx_av : APS.uE E (fst e_auxb) + 24 = av.
Proof. unfold av. eapply sw_uauxv; eassumption. Qed.

Lemma hx_auxv : APS.uE E e_auxv = av.
Proof.
  rewrite (hx_u e_auxv (proj1 e_auxv_vars) (proj2 e_auxv_vars)).
  unfold av. eapply u_e_auxv; eassumption.
Qed.

Lemma hx_bounds : usp + 32 <= av /\ av + 416 <= 2 ^ 47 /\ av mod 8 = 0.
Proof.
  pose proof hx_usp as ((U1 & U2) & LA & LE).
  assert (G : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb)) by (edestruct bsb_ge as [G _]; first [exact G | eassumption]).
  assert (F1 : usp + Z.of_nat (length bsb) <= 2 ^ 47) by (eapply usp_fit; eassumption).
  pose proof Hsp as HS. unfold valid_sp, sp_window_lo, sp_window_hi in *. unfold av.
  split; [lia|]. split; [lia|].
  destruct HS as (_ & _ & M16). apply Z.mod_divide; [lia|]. apply Z.mod_divide in M16; [|lia]. destruct M16 as (q & Hq). exists (2 * q + argc + envc + 3). lia.
Qed.

Lemma hx_slot : forall j v, (j < 50)%nat -> auxv_slot ch j = Some v ->
  bytes_at asegs m (av + 8 * Z.of_nat j) (le8 (edenot E v)).
Proof.
  intros j v Hj H. unfold auxv_slot in H. apply kw_find_in in H.
  pose proof hx_bounds as (B1 & B2 & B3). pose proof hx_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo in U1.
  pose proof (hk_kword asegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok AH E ch R FULL model HC A' HA' _ 8%nat v H) as X.
  unfold estart in X. cbn [a_base a_off] in X. rewrite e_auxb_k in X. pose proof hx_av as UA. unfold APS.uE in UA.
  replace (bv_unsigned (edenot E (fst e_auxb)) + (24 + 8 * Z.of_nat j)) with (av + 8 * Z.of_nat j) in X by lia.
  exact (X ltac:(change (Z.of_nat 8) with 8; lia)).
Qed.

Lemma hx_table : hs_auxv_ok ch = true -> forall jx, In jx AUXV_TABLE -> auxv_slot_ok ch jx = true.
Proof. intros HT jx Hin. unfold hs_auxv_ok in HT. apply andb_prop in HT as [_ HT]. exact (proj1 (forallb_forall _ _) HT jx Hin). Qed.

Lemma hx_lit : forall j z, auxv_slot_ok ch (j, inl z) = true -> (j < 50)%nat -> 0 <= z < 2 ^ 64 ->
  bytes_at asegs m (av + 8 * Z.of_nat j) (le8 (Z_to_bv 64 z)).
Proof.
  intros j z H Hj Hz. unfold auxv_slot_ok in H. cbn [fst snd] in H.
  destruct (auxv_slot ch j) as [v|] eqn:Hs; [|discriminate]. apply expr_eqb_eq in H. subst v.
  pose proof (hx_slot j (ELit z) Hj Hs) as X. cbn [edenot] in X. exact X.
Qed.

Lemma hx_var : forall j k, auxv_slot_ok ch (j, inr k) = true -> (j < 50)%nat -> (k < 50)%nat ->
  exists v, auxv_slot ch k = Some v /\ bytes_at asegs m (av + 8 * Z.of_nat j) (le8 (edenot E v)).
Proof.
  intros j k H Hj Hk. unfold auxv_slot_ok in H. cbn [fst snd] in H.
  destruct (auxv_slot ch j) as [v|] eqn:Hs; [|discriminate]. destruct (auxv_slot ch k) as [v'|] eqn:Hs'; [|discriminate].
  apply expr_eqb_eq in H. subst v'. exists v. split; [reflexivity| exact (hx_slot j v Hj Hs)].
Qed.

Local Ltac tab_in := cbn [AUXV_TABLE In]; tauto.

Theorem hi_auxv : hs_auxv_ok ch = true -> forall lo, lo <= usp -> el_auxvA lo m.
Proof.
  intros HT lo Hlo. pose proof hx_bounds as (B1 & B2 & B3). pose proof hx_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo in U1.
  pose proof HT as HT'. unfold hs_auxv_ok in HT'. apply andb_prop in HT' as [HL _].
  pose proof (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok AH E ch R FULL model HC A' HA' _ _ HL) as CELL.
  assert (EV : edenot E e_auxv = Z_to_bv 64 av).
  { rewrite <- hx_auxv. unfold APS.uE. symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite EV in CELL.

  destruct (hx_var 21%nat 21%nat (hx_table HT (21%nat, inr 21%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v21 & S21 & W21).
  destruct (hx_var 39%nat 39%nat (hx_table HT (39%nat, inr 39%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v39 & S39 & W39).
  destruct (hx_var 41%nat 39%nat (hx_table HT (41%nat, inr 39%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v41 & S41 & W41).
  rewrite S39 in S41. injection S41 as <-.
  destruct (hx_var 49%nat 49%nat (hx_table HT (49%nat, inr 49%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v49 & S49 & W49).
  exists av, (bv_unsigned (edenot E v21)), (bv_unsigned (edenot E v39)), (bv_unsigned (edenot E v49)).
  pose proof (bv_unsigned_in_range 64 (edenot E v21)) as R21. pose proof (bv_unsigned_in_range 64 (edenot E v39)) as R39.
  pose proof (bv_unsigned_in_range 64 (edenot E v49)) as R49. unfold bv_modulus in R21, R39, R49. change (2 ^ Z.of_N 64) with (2 ^ 64) in R21, R39, R49.
  split; [exact (proj1 CELL)|].
  split.
  { (* one word per slot: [hx_lit]/[hx_var] state slot j at [av + 8 * Z.of_nat j], which is
       [av + 8 j] by computation *)
    unfold el_auxv_at, el_auxv_word, EL_AT_PHDR.
    split; [exact (hx_lit 20%nat 16 (hx_table HT (20%nat, inl 16) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [rewrite Z_to_bv_bv_unsigned; exact W21|].
    split; [exact (hx_lit 22%nat 6 (hx_table HT (22%nat, inl 6) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 23%nat 4096 (hx_table HT (23%nat, inl 4096) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 26%nat 3 (hx_table HT (26%nat, inl 3) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 27%nat 65600 (hx_table HT (27%nat, inl 65600) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 28%nat 4 (hx_table HT (28%nat, inl 4) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 29%nat 56 (hx_table HT (29%nat, inl 56) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 30%nat 5 (hx_table HT (30%nat, inl 5) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 31%nat 11 (hx_table HT (31%nat, inl 11) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 38%nat 11 (hx_table HT (38%nat, inl 11) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [rewrite Z_to_bv_bv_unsigned; exact W39|].
    split; [exact (hx_lit 40%nat 12 (hx_table HT (40%nat, inl 12) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [rewrite Z_to_bv_bv_unsigned; exact W41|].
    split; [exact (hx_lit 46%nat 23 (hx_table HT (46%nat, inl 23) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 47%nat 0 (hx_table HT (47%nat, inl 0) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    split; [exact (hx_lit 48%nat 25 (hx_table HT (48%nat, inl 25) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    rewrite Z_to_bv_bv_unsigned; exact W49.
  }
  unfold USTACK_TOP. repeat (split; [lia|]). lia.
Qed.

End Aux.
