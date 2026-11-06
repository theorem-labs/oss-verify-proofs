(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesPG AsanNodesPGSoundG AsanNodesK1SoundG AsanNodesUG AsanWordLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rd_ok (SEGS : list Segment) (mem : word -> option byte) (c : Z * nat * Z) : Prop :=
  let '(a, w, v) := c in rdn SEGS mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
(* [comment removed for export] *)
Definition ug_fill1 (m : word -> option byte) (f : Z * Z) : word -> option byte :=
  wbytes m (Z_to_bv 64 (fst f)) (repeat (Z_to_bv 8 0) (Z.to_nat (snd f))).
Definition ug_mem (T : UGN.ugtab) (m : word -> option byte) : word -> option byte := fold_left ug_fill1 (UGN.ug_fills T) m.

Definition ug_spec (SEGS : list Segment) (A : atable) (T : UGN.ugtab) : Prop :=
  forall (mem rom : word -> option byte) (regs : bvmap 5 word),
    Forall (rd_ok SEGS mem) (UGN.ug_reads T) ->
    (forall j, UGN.ug_hlo T <= j < UGN.ug_hhi T -> store_ok SEGS mem (Z_to_bv 64 j) 1 = true) ->
    getr regs 1%bv = Z_to_bv 64 (UGN.ug_ret T) -> getr regs 20%bv = Z_to_bv 64 (UGN.ug_tab T) -> getr regs 27%bv = Z_to_bv 64 (UGN.ug_n T) ->
    getr regs 10%bv = Z_to_bv 64 (fst (hd (0, 0) (UGN.ug_fills T))) -> getr regs 11%bv = Z_to_bv 64 0 ->
    getr regs 12%bv = Z_to_bv 64 (snd (hd (0, 0) (UGN.ug_fills T))) ->
    getr regs 8%bv = Z_to_bv 64 (fst (hd (0, 0) (UGN.ug_fills T)) + snd (hd (0, 0) (UGN.ug_fills T))) ->
    Forall (fun rv : nat * Z => getr regs (Z_to_bv 5 (Z.of_nat (fst rv))) = Z_to_bv 64 (snd rv)) (UGN.ug_regs T) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (x_memset A)) mem rom) (mkst regs' (Z_to_bv 64 (UGN.ug_exit T)) (ug_mem T mem) rom)
      /\ getr regs' 8%bv = Z_to_bv 64 (UGN.ug_s0x T) /\ getr regs' 20%bv = Z_to_bv 64 (UGN.ug_tab T + 64 * UGN.ug_n T)
      /\ getr regs' 27%bv = Z_to_bv 64 0
      /\ (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) (8%nat :: 20%nat :: 27%nat :: UGN.UG_REGS) -> getr regs' r = getr regs r).

(* [comment removed for export] *)
Definition ug_wf (T : UGN.ugtab) : bool :=
  forallb (fun b : bool => b)
  [ forallb (fun f : Z * Z => (Z.leb (UGN.ug_hlo T) (fst f) && Z.leb 0 (snd f) && Z.leb (fst f + snd f) (UGN.ug_hhi T))%bool) (UGN.ug_fills T)
  ; forallb (fun rv : nat * Z => (Nat.ltb 0 (fst rv) && Nat.ltb (fst rv) 32 && negb (existsb (Nat.eqb (fst rv)) (8%nat :: 20%nat :: 27%nat :: UGN.UG_REGS)))%bool) (UGN.ug_regs T)
  ; forallb (fun c : Z * nat * Z => let '(a, w, v) := c in forallb (fun b : bool => b) [Z.leb 0 a; Z.leb (a + Z.of_nat w) (2 ^ 64); Nat.leb 1 w; Nat.leb w 8; Z.leb 0 v; Z.ltb v (2 ^ 64)]) (UGN.ug_reads T)
  ; Z.leb 0 (UGN.ug_s0x T); Z.ltb (UGN.ug_s0x T) (2 ^ 64); Z.leb 0 (UGN.ug_tab T + 64 * UGN.ug_n T); Z.ltb (UGN.ug_tab T + 64 * UGN.ug_n T) (2 ^ 64) ].

(* [comment removed for export] *)
Lemma ug_mem_out : forall fills lo hi m (x : word),
  Forall (fun f : Z * Z => lo <= fst f /\ 0 <= snd f /\ fst f + snd f <= hi) fills -> 0 <= lo -> hi <= 2 ^ 64 ->
  bv_unsigned x < lo \/ hi <= bv_unsigned x ->
  fold_left ug_fill1 fills m x = m x.
Proof.
  induction fills as [|f fills IH]; intros lo hi m x Hf Hlo Hhi Hx; [reflexivity|].
  cbn [fold_left]. inversion Hf as [|? ? (F1 & F2 & F3) Hf']. subst.
  rewrite (IH lo hi _ x Hf' Hlo Hhi Hx). unfold ug_fill1.
  destruct (Z.eq_dec (snd f) 0) as [Z0|NZ]; [rewrite Z0; reflexivity|].
  apply wbytes_out; rewrite repeat_length, u64_lit by lia; rewrite Z2Nat.id by lia; lia.
Qed.
Lemma ug_mem_grows : forall fills m, mem_grows m (fold_left ug_fill1 fills m).
Proof.
  induction fills as [|f fills IH]; intros m; [apply mem_grows_refl|].
  cbn [fold_left]. eapply mem_grows_trans; [apply wbytes_grows | apply IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable T : UGN.ugtab.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Hypothesis UGSPEC : ug_spec SEGS A T.
Hypothesis UGWF : ug_wf T = true.

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
Lemma kreadZ_rd : forall E M k a w v,
  know_ok SEGS E M k -> (1 <= w <= 8)%nat -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  (match kreadZ SEGS k (ELit 0) a w with Some z => Z.eqb z v | None => false end) = true ->
  rd_ok SEGS M (a, w, v).
Proof.
  intros E M k a w v HK Hw Ha Haw Hv H. unfold kreadZ in H.
  destruct (know_lookup SEGS k (ELit 0) a w false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate].
  apply Z.eqb_eq in H.
  assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat w)).
  { unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  destruct (lookup_piece SEGS E M k (ELit 0) a w (ELit z0) hs HK Hw HL Hfl) as (bs & Hrd & Hlen & Hbs).
  unfold rd_ok. unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite u64_lit in Hrd by lia. rewrite Z.add_0_l in Hrd.
  rewrite Hrd. f_equal. rewrite <- Hbs. cbn [edenot]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold two64 in H. rewrite <- H. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma reg_test : forall E cs R FULL model n V,
  cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> (0 < n < 32)%nat ->
  (match reg_lit cs n with Some r => Z.eqb r V | None => false end) = true ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 V.
Proof.
  intros E cs R FULL model n V HC Hn H. destruct (reg_lit cs n) as [r|] eqn:Hr; [|discriminate].
  apply Z.eqb_eq in H. subst r.
  exact (proj1 (w_reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model n V HC Hn Hr)).
Qed.

Theorem node_unreg_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => UGN.node_unreg SEGS A nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold UGN.node_unreg in Hn. destruct args; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  injection Hn as <-.
  unfold UGN.ug_tests in Hall. cbn [forallb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hfresh Hw Hhi64 Hlohi Hlo0 Hn1 Hreads Hregs H8 H12 H11 H10 H27 H20 H1 Hpc. clear Hall.
  apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo0. apply Z.ltb_lt in Hlohi. apply Z.ltb_lt in Hhi64. unfold two64 in Hhi64.
  (* [comment removed for export] *)
  pose proof UGWF as WF. unfold ug_wf in WF. cbn [forallb] in WF.
  repeat match type of WF with (?a && ?b)%bool = true => apply andb_prop in WF; destruct WF as [?X WF]; revert X end.
  intros WFt1 WFt0 WFs1 WFs0 WFc WFr WFf. clear WF.
  apply Z.leb_le in WFs0. apply Z.ltb_lt in WFs1. apply Z.leb_le in WFt0. apply Z.ltb_lt in WFt1.
  (* [comment removed for export] *)
  pose proof (reg_test E cs R FULL model 1 _ HC ltac:(lia) H1) as R1.
  pose proof (reg_test E cs R FULL model 20 _ HC ltac:(lia) H20) as R20.
  pose proof (reg_test E cs R FULL model 27 _ HC ltac:(lia) H27) as R27.
  pose proof (reg_test E cs R FULL model 10 _ HC ltac:(lia) H10) as R10.
  pose proof (reg_test E cs R FULL model 11 _ HC ltac:(lia) H11) as R11.
  pose proof (reg_test E cs R FULL model 12 _ HC ltac:(lia) H12) as R12.
  pose proof (reg_test E cs R FULL model 8 _ HC ltac:(lia) H8) as R8.
  assert (RR : Forall (fun rv : nat * Z => getr R (Z_to_bv 5 (Z.of_nat (fst rv))) = Z_to_bv 64 (snd rv)) (UGN.ug_regs T)).
  { apply Forall_forall. intros rv Hin.
    pose proof (proj1 (forallb_forall _ _) Hregs rv Hin) as Hb. pose proof (proj1 (forallb_forall _ _) WFr rv Hin) as Hwf.
    cbn beta in Hb, Hwf. apply andb_prop in Hwf as [Hwf _]. apply andb_prop in Hwf as [W0 W32].
    apply Nat.ltb_lt in W0. apply Nat.ltb_lt in W32.
    exact (reg_test E cs R FULL model (fst rv) (snd rv) HC ltac:(lia) Hb). }
  (* [comment removed for export] *)
  assert (RD : Forall (rd_ok SEGS M) (UGN.ug_reads T)).
  { apply Forall_forall. intros [[a w] v] Hin.
    pose proof (proj1 (forallb_forall _ _) Hreads _ Hin) as Hb. pose proof (proj1 (forallb_forall _ _) WFc _ Hin) as Hwf.
    cbn beta iota in Hb, Hwf. cbn [forallb] in Hwf.
    repeat match type of Hwf with (?a && ?b)%bool = true => apply andb_prop in Hwf; destruct Hwf as [?X Hwf]; revert X end.
    intros C6 C5 C4 C3 C2 C1. apply Z.leb_le in C1. apply Z.leb_le in C2. apply Nat.leb_le in C3. apply Nat.leb_le in C4.
    apply Z.leb_le in C5. apply Z.ltb_lt in C6.
    eapply (kreadZ_rd E M (kn cs) a w v HKN); try lia. exact Hb. }
  (* [comment removed for export] *)
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) (ELit 0) (UGN.ug_hlo T) (UGN.ug_hlen T) HKN HKN Hw ltac:(unfold UGN.ug_hlen; lia)) as (SW & _ & _).
  assert (Hst : estart E (SA (ELit 0) (UGN.ug_hlo T)) = UGN.ug_hlo T).
  { unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  rewrite Hst in SW.
  assert (HokW : forall j, UGN.ug_hlo T <= j < UGN.ug_hhi T -> store_ok SEGS M (Z_to_bv 64 j) 1 = true).
  { intros j Hj.
    pose proof (store_ok_all SEGS M (Z.to_nat (UGN.ug_hlen T)) (Z_to_bv 64 (UGN.ug_hlo T))
                  ltac:(rewrite u64_lit by lia; unfold UGN.ug_hlen; rewrite Z2Nat.id by lia; lia) SW
                  (Z_to_bv 64 j) ltac:(rewrite !u64_lit by lia; unfold UGN.ug_hlen; rewrite Z2Nat.id by lia; lia)) as X.
    cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 j)); [reflexivity | exfalso; exact (X eq_refl)]. }
  (* [comment removed for export] *)
  assert (R10' : getr R 10%bv = Z_to_bv 64 (fst (hd (0, 0) (UGN.ug_fills T)))).
  { etransitivity; [exact R10|]. destruct (UGN.ug_fills T); reflexivity. }
  assert (R12' : getr R 12%bv = Z_to_bv 64 (snd (hd (0, 0) (UGN.ug_fills T)))).
  { etransitivity; [exact R12|]. destruct (UGN.ug_fills T); reflexivity. }
  assert (R8' : getr R 8%bv = Z_to_bv 64 (fst (hd (0, 0) (UGN.ug_fills T)) + snd (hd (0, 0) (UGN.ug_fills T)))).
  { etransitivity; [exact R8|]. destruct (UGN.ug_fills T); reflexivity. }
  destruct (UGSPEC M (seg_rom SEGS) R RD HokW R1 R20 R27 R10' R11 R12' R8' RR) as (regs' & Hms & Q8 & Q20 & Q27 & Hout).
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (nx := nxt cs) in *.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HREG.
  rewrite <- Hpc in Hms.
  set (E2 := ext_list E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) UGN.UG_REGS)).
  assert (Hag2 : env_agree nx E E2) by (unfold E2; apply ext_list_agree).
  (* [comment removed for export] *)
  set (regsF := regupd (regupd (regupd R 8%bv (getr regs' 8%bv)) 20%bv (getr regs' 20%bv)) 27%bv (getr regs' 27%bv)).
  assert (HRF : regs_ok E (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs)) 8 (ELit (UGN.ug_s0x T))) 20 (ELit (UGN.ug_tab T + 64 * UGN.ug_n T))) 27 (ELit 0)) regsF).
  { unfold regsF.
    apply (regs_ok_updn E _ _ 27%bv 27%nat); [discriminate | reflexivity | | cbn [edenot]; rewrite Q27; reflexivity].
    apply (regs_ok_updn E _ _ 20%bv 20%nat); [discriminate | reflexivity | | cbn [edenot]; rewrite Q20; reflexivity].
    apply (regs_ok_updn E _ _ 8%bv 8%nat); [discriminate | reflexivity | exact HREG | cbn [edenot]; rewrite Q8; reflexivity]. }
  assert (HR2 : regs_ok E2 (sr_fresh (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs)) 8 (ELit (UGN.ug_s0x T))) 20 (ELit (UGN.ug_tab T + 64 * UGN.ug_n T))) 27 (ELit 0)) UGN.UG_REGS nx) regs').
  { unfold E2. apply (regs_ok_region UGN.UG_REGS E _ regsF regs' nx HRF).
    - apply sr_vars_lt_upd; [apply sr_vars_lt_upd; [apply sr_vars_lt_upd; [exact Fsr|reflexivity]|reflexivity]|reflexivity].
    - unfold UGN.UG_REGS. repeat constructor; lia.
    - intros r Hr0 Hnot. unfold regsF.
      destruct (bv_eq_dec 5 r 27%bv) as [->|N27]; [rewrite getr_same by discriminate; reflexivity|].
      rewrite getr_other by exact N27.
      destruct (bv_eq_dec 5 r 20%bv) as [->|N20]; [rewrite getr_same by discriminate; reflexivity|].
      rewrite getr_other by exact N20.
      destruct (bv_eq_dec 5 r 8%bv) as [->|N8]; [rewrite getr_same by discriminate; reflexivity|].
      rewrite getr_other by exact N8.
      apply Hout; [exact Hr0|]. intros [J8|[H20'|[H27'|Hin]]].
      + apply N8. apply ridx_inj. rewrite <- J8. reflexivity.
      + apply N20. apply ridx_inj. rewrite <- H20'. reflexivity.
      + apply N27. apply ridx_inj. rewrite <- H27'. reflexivity.
      + exact (Hnot Hin). }
  (* [comment removed for export] *)
  assert (HFl : Forall (fun f : Z * Z => UGN.ug_hlo T <= fst f /\ 0 <= snd f /\ fst f + snd f <= UGN.ug_hhi T) (UGN.ug_fills T)).
  { apply Forall_forall. intros f Hin. pose proof (proj1 (forallb_forall _ _) WFf f Hin) as Hb. cbn beta in Hb.
    apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. lia. }
  assert (HK2 : know_ok SEGS E2 (ug_mem T M) (kn_havoc (kn cs) (ELit 0) (UGN.ug_hlo T) (ELit (UGN.ug_hlen T)))).
  { eapply (w_know_ok_havoc SEGS E2 M).
    - eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN].
    - intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx.
      rewrite !u64_lit in Hx by (unfold UGN.ug_hlen; lia). unfold UGN.ug_hlen in Hx.
      unfold ug_mem. apply (ug_mem_out (UGN.ug_fills T) (UGN.ug_hlo T) (UGN.ug_hhi T) M x HFl Hlo0 ltac:(lia)). lia.
    - apply ug_mem_grows. }
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs E E2 R FULL model TT (UGN.ug_exit T) _ _ (nx + 7)%N regs' (ug_mem T M) HC Hfresh Hag2 Hms HR2 HK2).
  intros R' FULL' model' HC' Hfs'. apply (Hk E2 R' FULL' model'); [| exact HC' | exact Hfs'].
  split; [eapply env_agree_le; [exact Hag2 | exact Fle] | exact Hag2].
Qed.

(* [comment removed for export] *)
Theorem ug_xn_sound : ext_stmt SEGS A nx0 LIMIT (UGN.xn SEGS A nx0 T) SINV argH FS0.
Proof.
  intros id args. unfold UGN.xn. destruct (Nat.eqb id 121).
  - intros cs cs' E R FULL model TT HC Hpre Hn Hk. rewrite UGN.node_unregB_eq in Hn.
    exact (node_unreg_sound args cs cs' E R FULL model TT HC Hpre Hn Hk).
  - intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Sound.
