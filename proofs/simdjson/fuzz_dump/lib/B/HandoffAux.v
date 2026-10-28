(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_kit D_auxv HandoffImage HandoffArgv RT_state RT_init RT_init_mem HandoffG1.
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

Definition AUXV_TABLE : list (nat * (Z + nat)) :=
  [(0%nat, inl 3); (1%nat, inl EL_AT_PHDR); (2%nat, inl 4); (3%nat, inl 56); (4%nat, inl 5); (5%nat, inl 11); (6%nat, inl 16); (7%nat, inr 7%nat);
   (8%nat, inl 6); (9%nat, inl 4096); (10%nat, inl 11); (11%nat, inr 11%nat); (12%nat, inl 12); (13%nat, inr 11%nat); (14%nat, inl 23); (15%nat, inl 0);
   (16%nat, inl 25); (17%nat, inr 17%nat); (18%nat, inl 0); (19%nat, inl 0)].

Definition hs_auxv_ok (ch : acs) : bool :=
  (lit_word ch EL_AUXV_CELL 8 e_auxv && forallb (auxv_slot_ok ch) AUXV_TABLE)%bool.

Section Aux.
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
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation bsb := (build_stack_bytes ph sp argv envp uid hw rdraw).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Let AH := ha_argH_high ph sp rdraw argv envp uid hw Hsp Hva.

Let av : Z := usp + 8 * argc + 8 * envc + 24.

Lemma hx_usp : sp_window_lo <= usp <= sp_window_hi /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256.
Proof. exact (sw_usp ph sp rdraw argv envp uid hw Hsp Hva Hve). Qed.

Lemma hx_av : APS.uE E (fst e_auxb) + 24 = av.
Proof. exact (sw_uauxv A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC). Qed.

Lemma hx_auxv : APS.uE E e_auxv = av.
Proof.
  rewrite (ha_u A nx0 LIMIT FS0 ph sp rdraw brk0 argv envp uid hw E ch R FULL model HC e_auxv (proj1 e_auxv_vars) (proj2 e_auxv_vars)).
  exact (u_e_auxv ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
Qed.

Lemma hx_bounds : usp + 32 <= av /\ av + 176 <= 2 ^ 47 /\ av mod 8 = 0.
Proof.
  pose proof hx_usp as ((U1 & U2) & LA & LE). pose proof (bsb_ge ph sp rdraw argv envp uid hw) as (G & _).
  destruct (ha_bsb ph sp rdraw argv envp uid hw Hfit) as (F1 & _).
  pose proof Hsp as HS. unfold valid_sp, sp_window_lo, sp_window_hi in *. unfold av.
  split; [lia|]. split; [lia|].
  destruct HS as (_ & _ & M16). apply Z.mod_divide; [lia|]. apply Z.mod_divide in M16; [|lia]. destruct M16 as (q & Hq). exists (2 * q + argc + envc + 3). lia.
Qed.

Lemma hx_slot : forall j v, (j < 20)%nat -> auxv_slot ch j = Some v ->
  bytes_at bsegs m (av + 8 * Z.of_nat j) (le8 (edenot E v)).
Proof.
  intros j v Hj H. unfold auxv_slot in H. apply kw_find_in in H.
  pose proof hx_bounds as (B1 & B2 & B3). pose proof hx_usp as ((U1 & U2) & LA & LE). unfold sp_window_lo in U1.
  pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok AH E ch R FULL model HC A' HA' _ 8%nat v H) as X.
  unfold estart in X. cbn [a_base a_off] in X. rewrite e_auxb_k in X. pose proof hx_av as UA. unfold APS.uE in UA.
  replace (bv_unsigned (edenot E (fst e_auxb)) + (24 + 8 * Z.of_nat j)) with (av + 8 * Z.of_nat j) in X by lia.
  exact (X ltac:(change (Z.of_nat 8) with 8; lia)).
Qed.

Lemma hx_table : hs_auxv_ok ch = true -> forall jx, In jx AUXV_TABLE -> auxv_slot_ok ch jx = true.
Proof. intros HT jx Hin. unfold hs_auxv_ok in HT. apply andb_prop in HT as [_ HT]. exact (proj1 (forallb_forall _ _) HT jx Hin). Qed.

Lemma hx_lit : forall j z, auxv_slot_ok ch (j, inl z) = true -> (j < 20)%nat -> 0 <= z < 2 ^ 64 ->
  bytes_at bsegs m (av + 8 * Z.of_nat j) (le8 (Z_to_bv 64 z)).
Proof.
  intros j z H Hj Hz. unfold auxv_slot_ok in H. cbn [fst snd] in H.
  destruct (auxv_slot ch j) as [v|] eqn:Hs; [|discriminate]. apply expr_eqb_eq in H. subst v.
  pose proof (hx_slot j (ELit z) Hj Hs) as X. cbn [edenot] in X. exact X.
Qed.

Lemma hx_var : forall j k, auxv_slot_ok ch (j, inr k) = true -> (j < 20)%nat -> (k < 20)%nat ->
  exists v, auxv_slot ch k = Some v /\ bytes_at bsegs m (av + 8 * Z.of_nat j) (le8 (edenot E v)).
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

  destruct (hx_var 7%nat 7%nat (hx_table HT (7%nat, inr 7%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v7 & S7 & W7).
  destruct (hx_var 11%nat 11%nat (hx_table HT (11%nat, inr 11%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v11 & S11 & W11).
  destruct (hx_var 13%nat 11%nat (hx_table HT (13%nat, inr 11%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v13 & S13 & W13).
  rewrite S11 in S13. injection S13 as <-.
  destruct (hx_var 17%nat 17%nat (hx_table HT (17%nat, inr 17%nat) ltac:(tab_in)) ltac:(lia) ltac:(lia)) as (v17 & S17 & W17).
  exists av, (bv_unsigned (edenot E v7)), (bv_unsigned (edenot E v11)), (bv_unsigned (edenot E v17)).
  pose proof (bv_unsigned_in_range 64 (edenot E v7)) as R7. pose proof (bv_unsigned_in_range 64 (edenot E v11)) as R11.
  pose proof (bv_unsigned_in_range 64 (edenot E v17)) as R17. unfold bv_modulus in R7, R11, R17. change (2 ^ Z.of_N 64) with (2 ^ 64) in R7, R11, R17.
  split; [exact (proj1 CELL)|].
  split.
  { unfold el_auxv_words, EL_AT_PHDR. apply bytes_at_u64s; [lia| cbn [length map]; lia|].
    intros j w Hn.
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 0%nat 3 (hx_table HT (0%nat, inl 3) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 1%nat 65600 (hx_table HT (1%nat, inl 65600) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 2%nat 4 (hx_table HT (2%nat, inl 4) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 3%nat 56 (hx_table HT (3%nat, inl 56) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 4%nat 5 (hx_table HT (4%nat, inl 5) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 5%nat 11 (hx_table HT (5%nat, inl 11) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 6%nat 16 (hx_table HT (6%nat, inl 16) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; rewrite Z_to_bv_bv_unsigned; exact W7|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 8%nat 6 (hx_table HT (8%nat, inl 6) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 9%nat 4096 (hx_table HT (9%nat, inl 4096) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 10%nat 11 (hx_table HT (10%nat, inl 11) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; rewrite Z_to_bv_bv_unsigned; exact W11|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 12%nat 12 (hx_table HT (12%nat, inl 12) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; rewrite Z_to_bv_bv_unsigned; exact W13|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 14%nat 23 (hx_table HT (14%nat, inl 23) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 15%nat 0 (hx_table HT (15%nat, inl 0) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 16%nat 25 (hx_table HT (16%nat, inl 25) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; rewrite Z_to_bv_bv_unsigned; exact W17|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 18%nat 0 (hx_table HT (18%nat, inl 0) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    destruct j as [|j]; [cbn [map nth_error] in Hn; injection Hn as <-; exact (hx_lit 19%nat 0 (hx_table HT (19%nat, inl 0) ltac:(tab_in)) ltac:(lia) ltac:(lia))|].
    cbn [map nth_error] in Hn. destruct j; discriminate Hn.
  }
  unfold USTACK_TOP. repeat (split; [lia|]). lia.
Qed.

End Aux.
