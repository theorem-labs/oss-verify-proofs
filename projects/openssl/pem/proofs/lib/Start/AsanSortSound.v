(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
  AsanAcct AsanAcctShape SpinAlg Hoare.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound
  AsanPlanSoundSums AsanNodesLib AsanNodesLibSound.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanSortModel AsanSort AsanHookKit AsanRehashSound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HSNS.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX. Import HSN. Import HKIT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation inr := LBNS.inr (only parsing).

Section Specs.
Variable SEGS : list Segment.
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).
#[local] Notation cell := (LBNS.cell SEGS) (only parsing).

Definition recs_at (M : word -> option byte) (tab n : Z) (es : list HSM.rec) : Prop :=
  forall j, 0 <= j < n -> cell M (tab + 16 * j) 8 (W (fst (HSM.get es j))) /\ cell M (tab + 16 * j + 8) 8 (W (snd (HSM.get es j))).

Definition isort_contract (entry : Z) : Prop :=
  forall regs M (tab n ra : Z) (es : list HSM.rec),
    getr regs 10%bv = W tab -> getr regs 11%bv = W n -> getr regs 1%bv = W ra ->
    Z.of_nat (length es) = n -> 2 <= n <= 2 ^ 16 ->
    Forall (fun e => 0 <= fst e < 2 ^ 64 /\ 0 <= snd e < 2 ^ 64) es ->
    recs_at M tab n es -> wr_ok M tab (16 * n) ->
    0 < tab -> tab + 16 * n <= 2 ^ 47 -> tab mod 8 = 0 -> 0 <= ra < 2 ^ 47 -> ra mod 2 = 0 ->
    (forall s, In s SEGS -> seg_writable s = false -> forall z, Z.of_N (seg_base s) <= z < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> M (W z) = None) ->
    exists regs' M',
      msteps SEGS (mkst regs (W entry) M (seg_rom SEGS)) (mkst regs' (W ra) M' (seg_rom SEGS))
      /\ (forall r : bv 5, ~ In (ridx r) hs_fresh -> getr regs' r = getr regs r)
      /\ recs_at M' tab n (HSM.hsort es)
      /\ (forall x, ~ inr x tab (16 * n) -> M' x = M x) /\ mem_grows M M'.
End Specs.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : AP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Variable entry : Z.

#[local] Notation cell := (LBNS.cell SEGS) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).

Hypothesis HSC : isort_contract SEGS entry.

Lemma hs_fresh_nodup : List.NoDup hs_fresh.
Proof.
  unfold hs_fresh. repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma lit1_w : forall E e z, lit1 e = Some z -> edenot E e = W z.
Proof. intros E e z H. destruct e; try discriminate. cbn [lit1] in H. injection H as <-. cbn [edenot]. symmetry. apply LBNS.W_mod. Qed.

(* [comment removed for export] *)
Lemma read_recs_sound : forall E (M : word -> option byte) k, know_ok SEGS E M k ->
  forall n a es, read_recs SEGS k a n = Some es -> 0 <= a -> a + 16 * Z.of_nat n <= 2 ^ 63 ->
  length es = n /\ recs_at SEGS M a (Z.of_nat n) es
  /\ Forall (fun e => 0 <= fst e < 2 ^ 64 /\ 0 <= snd e < 2 ^ 64) es.
Proof.
  intros E M k HK n. induction n as [|n IH]; intros a es H Ha Hn.
  - cbn [read_recs] in H. injection H as <-. split; [reflexivity|]. split; [intros j Hj; cbn in Hj; lia | constructor].
  - cbn [read_recs] in H. rewrite Nat2Z.inj_succ in Hn.
    destruct (kreadZ SEGS k (ELit 0) a 8) as [w0|] eqn:K0; [|discriminate]. destruct (kreadZ SEGS k (ELit 0) (a + 8) 8) as [w1|] eqn:K1; [|discriminate].
    destruct (read_recs SEGS k (a + 16) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (a + 16) r Hr ltac:(lia) ltac:(lia)) as (Hl & Hc & Hf).
    assert (R0 : 0 <= w0 < 2 ^ 64).
    { unfold kreadZ in K0. destruct (know_lookup SEGS k (ELit 0) a 8 false [] []) as [v scs hs|scs hs|]; try discriminate.
      destruct v; try discriminate. destruct scs; [|discriminate]. injection K0 as <-. apply Z.mod_pos_bound. unfold two64. lia. }
    assert (R1 : 0 <= w1 < 2 ^ 64).
    { unfold kreadZ in K1. destruct (know_lookup SEGS k (ELit 0) (a + 8) 8 false [] []) as [v scs hs|scs hs|]; try discriminate.
      destruct v; try discriminate. destruct scs; [|discriminate]. injection K1 as <-. apply Z.mod_pos_bound. unfold two64. lia. }
    split; [cbn [length]; rewrite Hl; reflexivity|]. split; [| constructor; [cbn [fst snd]; split; assumption | exact Hf]].
    intros j Hj. rewrite Nat2Z.inj_succ in Hj. destruct (Z.eq_dec j 0) as [->|Nj].
    + unfold HSM.get. change (Z.to_nat 0) with 0%nat. cbn [nth fst snd]. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact (RHNS.lit_cell SEGS E M k a 8 w0 HK ltac:(lia) K0 ltac:(lia) ltac:(lia))
             | exact (RHNS.lit_cell SEGS E M k (a + 8) 8 w1 HK ltac:(lia) K1 ltac:(lia) ltac:(lia))].
    + specialize (Hc (j - 1) ltac:(lia)). unfold HSM.get in *.
      replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia. cbn [nth].
      replace (a + 16 * j) with (a + 16 + 16 * (j - 1)) by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rec_facts_ok : forall E (M' : word -> option byte) es a n, 0 <= a -> a + 16 * Z.of_nat (length es) <= 2 ^ 63 -> Z.of_nat (length es) = n ->
  recs_at SEGS M' a n es -> Forall (kentry_ok SEGS E M') (rec_facts a es).
Proof.
  intros E M' es. induction es as [|e r IH]; intros a n Ha Hfit Hn Hc; cbn [rec_facts]; [constructor|].
  cbn [length] in Hfit, Hn. rewrite Nat2Z.inj_succ in Hfit, Hn.
  assert (Es : forall o, 0 <= o < 2 ^ 64 -> estart E (SA (ELit 0) o) = o) by (intros o Ho; unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  destruct (Hc 0 ltac:(lia)) as [C0 C1]. unfold HSM.get in C0, C1. change (Z.to_nat 0) with 0%nat in C0, C1. cbn [nth] in C0, C1. rewrite Z.mul_0_r, Z.add_0_r in C0, C1.
  constructor; [| constructor].
  - apply (kword_intro SEGS E M' (ELit 0) a 8 (ELit (fst e)) a (W (fst e))); [lia | apply Es; lia | lia | lia | lia | exact C0 | reflexivity].
  - apply (kword_intro SEGS E M' (ELit 0) (a + 8) 8 (ELit (snd e)) (a + 8) (W (snd e))); [lia | apply Es; lia | lia | lia | lia | exact C1 | reflexivity].
  - apply (IH (a + 16) (n - 1)); [lia | lia | lia |]. intros j Hj. specialize (Hc (j + 1) ltac:(lia)). unfold HSM.get in *.
    replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) in Hc by lia. cbn [nth] in Hc. replace (a + 16 * (j + 1)) with (a + 16 + 16 * j) in Hc by lia. exact Hc.
Qed.

Theorem node_isort_sound : node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => node_isort SEGS A nx0 entry cs).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold node_isort in Hn.
  destruct (negb (Z.eqb (pc cs) entry)) eqn:Hpc0; [discriminate|]. apply negb_false_iff in Hpc0. apply Z.eqb_eq in Hpc0.
  destruct (lit1 (reg cs 10)) as [tab|] eqn:L10; [|discriminate]. destruct (lit1 (reg cs 11)) as [n|] eqn:L11; [|discriminate].
  destruct (lit1 (reg cs 1)) as [ra|] eqn:L1; [|discriminate].
  destruct (read_recs SEGS (kn cs) tab (Z.to_nat n)) as [es|] eqn:Hrd; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  cbv zeta in Hn.
  match type of Hn with Some (with_ss cs (mk_ss _ ?sr ?kf _)) = _ => remember sr as srF eqn:HsrF; remember kf as kF eqn:HkF end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Cwr]. apply andb_prop in Hc as [Hc Crng]. apply andb_prop in Hc as [Hc Cra2]. apply andb_prop in Hc as [Hc Cra1].
  apply andb_prop in Hc as [Hc Cra0]. apply andb_prop in Hc as [Hc Ct8]. apply andb_prop in Hc as [Hc Chi]. apply andb_prop in Hc as [Hc Clo].
  apply andb_prop in Hc as [Hc Ct0]. apply andb_prop in Hc as [Hc Cn2]. apply andb_prop in Hc as [Hc Cn1]. apply andb_prop in Hc as [Hfresh Cro].
  apply Z.leb_le in Cn1, Cn2, Clo, Chi, Cra0. apply Z.ltb_lt in Ct0, Cra1. apply Z.eqb_eq in Ct8, Cra2.
  pose proof HULL_ok as (HU0 & _ & _ & HU3). unfold KHI in HU3.
  assert (Bt : 0 < tab /\ tab + 16 * n <= 2 ^ 47) by (clear - Ct0 Chi HU3; lia).
  destruct (read_recs_sound E M (kn cs) HKN (Z.to_nat n) tab es Hrd ltac:(clear - Bt; lia) ltac:(rewrite Z2Nat.id by (clear - Cn1; lia); clear - Bt Cn1; lia)) as (Hlen & Hrecs & Hrng).
  rewrite Z2Nat.id in Hrecs by (clear - Cn1; lia).
  assert (Rg : forall r, (0 < r < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat r)) = edenot E (reg cs r)).
  { intros r Hr. exact (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model r HC Hr). }
  assert (G10 : getr R 10%bv = W tab) by (change (getr R 10%bv) with (getr R (Z_to_bv 5 (Z.of_nat 10))); rewrite (Rg 10%nat) by (clear; lia); exact (lit1_w E _ _ L10)).
  assert (G11 : getr R 11%bv = W n) by (change (getr R 11%bv) with (getr R (Z_to_bv 5 (Z.of_nat 11))); rewrite (Rg 11%nat) by (clear; lia); exact (lit1_w E _ _ L11)).
  assert (G1 : getr R 1%bv = W ra) by (change (getr R 1%bv) with (getr R (Z_to_bv 5 (Z.of_nat 1))); rewrite (Rg 1%nat) by (clear; lia); exact (lit1_w E _ _ L1)).
  assert (Est : estart E (SA (ELit 0) tab) = tab) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by (clear - Bt Cn1; lia); clear; lia).
  destruct (kwr_wr_ok SEGS E M (kn cs) (ELit 0) tab (16 * n) HKN Cwr ltac:(clear - Cn1 Cn2; lia) ltac:(rewrite Est; clear - Bt Cn1; lia)) as (Wt & _ & _). rewrite Est in Wt.
  assert (RO : forall sg, In sg SEGS -> seg_writable sg = false -> forall z, Z.of_N (seg_base sg) <= z < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> M (W z) = None).
  { intros sg Hsg Hw z Hz. unfold ro_cov in Cro. rewrite forallb_forall in Cro. specialize (Cro sg Hsg). rewrite Hw in Cro. cbn [orb] in Cro.
    exact (img_cov_sound SEGS E M (kn cs) _ _ HKN Cro z Hz). }
  destruct (HSC R M tab n ra es G10 G11 G1 ltac:(rewrite Hlen; apply Z2Nat.id; clear - Cn1; lia) ltac:(clear - Cn1 Cn2; lia) Hrng Hrecs Wt
              (proj1 Bt) (proj2 Bt) Ct8 ltac:(clear - Cra0 Cra1; lia) Cra2 RO)
    as (regs' & M' & Hms & Kkept & Krecs & Hfr & Hg).
  set (nx := nxt cs) in *.
  set (E' := LBNS.ext_regs E nx hs_fresh regs').
  pose proof (LBNS.ext_regs_agree E nx hs_fresh regs') as Hag. fold E' in Hag.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle). fold nx in Fsr, Fkn, Fle.
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
            cs E E' R FULL model TT ra srF kF (nx + NHS)%nat regs' M' HC Hfresh Hag).
  - rewrite Hpc0. exact Hms.
  - rewrite HsrF. apply (LBNS.regs_after_region E (s_regs (a_ss cs)) R regs' nx hs_fresh (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr hs_fresh_nodup).
    intros r _ Hnin. exact (Kkept r Hnin).
  - rewrite HkF. apply Forall_app. split.
    + apply (rec_facts_ok E' M' (HSM.hsort es) tab n ltac:(clear - Bt; lia)); [| | exact Krecs].
      * rewrite HSM.hsort_length, Hlen, Z2Nat.id by (clear - Cn1; lia). clear - Bt Cn1. lia.
      * rewrite HSM.hsort_length, Hlen. apply Z2Nat.id. clear - Cn1. lia.
    + rewrite kn_havocM_eq.
      apply (w_know_ok_havoc SEGS E' M M' (kimg_cut (kn cs) tab (16 * n)) (ELit 0) tab (ELit (16 * n))).
      * apply kimg_cut_sound. exact (know_ok_agree' SEGS nx E E' M (kn cs) Hag Fkn HKN).
      * intros x Hx. apply Hfr. unfold LBNS.inr.
        assert (Est' : estart E' (SA (ELit 0) tab) = tab) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by (clear - Bt Cn1; lia); clear; lia).
        rewrite Est' in Hx. rewrite (elenZ_lit E' (16 * n) ltac:(clear - Cn1 Cn2; lia)) in Hx. clear - Hx. lia.
      * exact Hg.
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

End Sound.
End HSNS.
