(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.

Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_NOTHROW : Z := 0x107fa0.   (* [comment removed for export] *)
Definition ANOTHROW : Z := 0x2cb90.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shx (X : Z) : Z := Z.shiftr X 3 + ASHOFF.
(* [comment removed for export] *)
Definition shc (m : amem) (X : Z) : Prop := rw_cells asegs m (shx X) [C1 (Z_to_bv 8 0)].

Lemma shx_shad : forall X, shx X = shad X.
Proof. intros X. unfold shx, shad. lia. Qed.
Lemma shx_div : forall X, 0 <= X -> shx X = X / 8 + ASHOFF.
Proof. intros X H. unfold shx. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Section Blk.
  Variable AI : AMallocIface.
  (* [comment removed for export] *)
  Lemma blk_shc : forall L RNG st LB m p A n X,
    AHEAP AI L RNG st LB m -> In (HB p A n) LB -> A <= X -> X + 8 <= A + n ->
    shc m (X - X mod 8) /\ rng RNG (shx X) 1.
  Proof.
    intros L RNG st LB m p A n X AH HIN H1 H2.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (NR & (B1 & B2 & B3 & B4) & RD & RSD & BSH & _).
    pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). unfold AIMG_HI in B1a. atop_facts.
    assert (G : shx (X - X mod 8) = shad A + (X - A) / 8 /\ shx X = shad A + (X - A) / 8).
    { unfold shx, shad. rewrite !Z.shiftr_div_pow2 by (try lia; Z.div_mod_to_equations; lia). change (2 ^ 3) with 8.
      Z.div_mod_to_equations. lia. }
    destruct G as [G1 G2].
    split.
    - unfold shc. rewrite G1. apply rw_cells_C1_of_byte.
      + unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
      + unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
      + rewrite (BSH ((X - A) / 8)) by (Z.div_mod_to_equations; lia).
        replace (8 * ((X - A) / 8) + 8 <=? n) with true by (symmetry; apply Z.leb_le; Z.div_mod_to_equations; lia). reflexivity.
    - rewrite G2. eapply rng_sub'; [exact RSD|]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma blk_shc8 : forall L RNG st LB m p A n X,
    AHEAP AI L RNG st LB m -> In (HB p A n) LB -> A <= X -> X + 8 <= A + n -> X mod 8 = 0 ->
    rw_cells asegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)] /\ rng RNG (Z.shiftr X 3 + 2147450880) 1.
  Proof.
    intros L RNG st LB m p A n X AH HIN H1 H2 H3. destruct (blk_shc L RNG st LB m p A n X AH HIN H1 H2) as [S R].
    rewrite H3, Z.sub_0_r in S. unfold shc, shx, ASHOFF in S, R. split; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma blk_shx_bounds : forall X, 0 <= X -> X + 8 <= 2^47 ->
    0x7fff8000 <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + 1 <= 0x10007fff8000.
  Proof. intros X H1 H2. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Lemma hb_ids_in : forall p A n LB, In (HB p A n) LB -> In p (hb_ids LB).
  Proof.
    intros p A n LB H. induction LB as [|b LB IH]; [destruct H|]. destruct H as [E|H].
    - subst b. cbn. left. reflexivity.
    - cbn [hb_ids flat_map]. apply in_or_app. right. apply IH. exact H.
  Qed.
  Lemma new_blk_apart : forall L RNG st p A n LB m b, AHEAP AI L RNG st (HB p A n :: LB) m -> In b LB ->
    A + n <= ab_addr b \/ ab_addr b + ab_size b <= A.
  Proof.
    intros L RNG st p A n LB m b AH Hb.
    assert (NE : HB p A n <> b).
    { intros E. subst b. pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND. cbn [hb_ids flat_map ab_kind app] in ND.
      apply NoDup_cons_iff in ND as [NI _]. apply NI. exact (hb_ids_in p A n LB Hb). }
    exact (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (or_introl eq_refl) (or_intror Hb) NE).
  Qed.
  (* [comment removed for export] *)
  Lemma fresh_not_client : forall L RNG st p A n LB m SP a, AHEAP AI L RNG st (HB p A n :: LB) m -> ATOP <= SP ->
    aclient_addr (aci AI) LB SP a -> ~ (A <= a < A + n).
  Proof.
    intros L RNG st p A n LB m SP a AH HS Hc Ha.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH (or_introl eq_refl)) as (_ & (B1 & B2 & B3 & B4) & _).
    pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). atop_facts.
    destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    - pose proof (new_blk_apart _ _ _ _ _ _ _ _ _ AH Hb). lia.
    - assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (or_intror Hb')) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      pose proof (shad_band1 a' ltac:(lia) ltac:(unfold KEND; lia)) as SB.
      exact (ablk_clear_band _ _ _ B1 SB Ha).
  Qed.
  (* [comment removed for export] *)
  Lemma blk_window_facts : forall L RNG st LB m p A n D k,
    AHEAP AI L RNG st LB m -> In (HB p A n) LB -> A <= D -> D + k <= A + n -> 0 <= k ->
    app_blk D (D + k) /\ unpoisoned m D (D + k) /\ rng RNG D k
    /\ exists RLO RHI, (RLO <= D /\ D + k <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
       /\ wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
  Proof.
    intros L RNG st LB m p A n D k AH HIN H1 H2 Hk.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH HIN) as (NR & (B1 & B2 & B3 & B4) & RD & RSD & BSH & WR & _ & (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6)).
    pose proof (ablk_lin _ _ B1) as (B1a & B1b & B1c & B1d). unfold AIMG_HI in B1a. atop_facts.
    assert (SH : shad RHI - shad RLO = shlen (RHI - RLO)).
    { unfold shad, shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    split; [apply ablk_app_blk; [eapply ablk_sub; [exact B1| lia| lia]| lia]|].
    split; [eapply unpoisoned_sub; [apply (ablock_unpoisoned _ _ _ BSH); first [lia| Z.div_mod_to_equations; lia]| lia| lia]|].
    split; [eapply rng_sub'; [exact RD| lia]|].
    (* [comment removed for export] *)
    exists (D / 64 * 64), ((D + k + 63) / 64 * 64).
    assert (HL1 : RLO <= D / 64 * 64) by (Z.div_mod_to_equations; lia).
    assert (HL2 : (D + k + 63) / 64 * 64 <= RHI) by (Z.div_mod_to_equations; lia).
    assert (HL3 : D / 64 * 64 <= D < D / 64 * 64 + 64) by (Z.div_mod_to_equations; lia).
    assert (HL4 : D + k <= (D + k + 63) / 64 * 64 < D + k + 64) by (Z.div_mod_to_equations; lia).
    split; [split; [lia|]; split; [lia|]; split; [apply Z.mod_mul; lia|]; split; [apply Z.mod_mul; lia|]; split; [lia| unfold KEND; lia]|].
    assert (SM1 : shad RLO <= shad (D / 64 * 64)) by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    assert (SM2 : shad ((D + k + 63) / 64 * 64) <= shad RHI) by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    assert (SM3 : shad (D / 64 * 64) <= shad ((D + k + 63) / 64 * 64)) by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    rewrite <- SH in R5, R6.
    split.
    - destruct R6 as (W0 & W1 & W). split; [unfold shad in *; rewrite Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia|]. split; [lia|].
      intros i Hi. replace (shad (D / 64 * 64) + i) with (shad RLO + (shad (D / 64 * 64) - shad RLO + i)) by lia. apply W. lia.
    - eapply rng_sub'; [exact R5| lia].
  Qed.
  (* [comment removed for export] *)
  Lemma AHEAP_stack_frame : forall L RNG st LB m m' W,
    AHEAP AI L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= 2^47) W -> AHEAP AI L RNG st LB m'.
  Proof.
    intros L RNG st LB m m' W AH MU WM FW. eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [lo hi] [H1 H2]. cbn [fst snd] in *. left. left. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma got_nothrow_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> mem_inv asegs m ->
    rw_cells asegs m AGOT_NOTHROW [C8 (Z_to_bv 64 ANOTHROW)].
  Proof.
    intros L RNG st LB m AH MI. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold ARELRO_LO, ARELRO_HI in R.
    unfold AGOT_NOTHROW, ANOTHROW.
    eapply rw_cells_recast; [apply (rw_cells_image0 asegs _ 0x107fa0 (le8 (Z_to_bv 64 0x2cb90)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma aclient_lo_or_sp : forall L RNG st LB LB' m SP a, AHEAP AI L RNG st LB m -> (forall b, In b LB' -> In b LB) ->
    aclient_addr (aci AI) LB' SP a -> a < ATOP \/ SP <= a.
  Proof.
    intros L RNG st LB LB' m SP a AH HL Hc. atop_facts.
    destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - right; lia.
    - left. pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. lia.
    - left. pose proof (AI_block_bounds AI _ _ _ _ _ b AH (HL b Hb)). lia.
    - left. assert (A47 : a' < 2^47).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); unfold AIMG_HI in *; lia|].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (HL _ Hb')). cbn in *. lia. }
      assert (A0 : 0 <= a' \/ a' < 0) by lia.
      unfold shad, ASHOFF. destruct A0 as [A0|A0].
      + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
      + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
  Qed.
End Blk.

(* [comment removed for export] *)
Lemma client_sh_cell : forall m X, client_sh m -> In X client_sh_addrs ->
  rw_cells asegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros m X H HX. pose proof (H X HX) as HB. unfold shad, ASHOFF in HB.
  assert (XR : 0 <= X < 2^40) by (cbn in HX; repeat destruct HX as [<-|HX]; try lia; destruct HX).
  apply rw_cells_C1_of_byte; [rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia| rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia|].
  rewrite Z.add_comm. exact HB.
Qed.

(* [comment removed for export] *)
Section Pres.
  Variable CI : list (Z * Z).
  Definition aheap_pres_x (LB : list ablock) (SP X n : Z) (m m' : amem) : Prop :=
    forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> ~ (X <= a < X + n) ->
      m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
  Lemma aheap_pres_x_trans : forall LB SP X n m1 m2 m3,
    aheap_pres_x LB SP X n m1 m2 -> aheap_pres_x LB SP X n m2 m3 -> aheap_pres_x LB SP X n m1 m3.
  Proof.
    intros LB SP X n m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
    split; [congruence| auto].
  Qed.
  Lemma aheap_pres_x_of_munch : forall LB SP X n W m m', munch W m m' -> wmono asegs m m' ->
    (forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> ~ (X <= a < X + n) -> outside W a) -> aheap_pres_x LB SP X n m m'.
  Proof.
    intros LB SP X n W m m' MU WM OUT a Ha Hc Hx. split.
    - apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT; assumption.
    - intros Hv. apply WM. exact Hv.
  Qed.
  Lemma aheap_pres_x_of_pres : forall LB LB' SP SP' X n m m', aheap_pres CI LB' SP' m m' -> SP' <= SP ->
    (forall b, In b LB -> In b LB') -> aheap_pres_x LB SP X n m m'.
  Proof.
    intros LB LB' SP SP' X n m m' H HS HL a Ha Hc _.
    exact (aheap_pres_weaken CI LB' LB SP' SP m m' H HS HL a Ha Hc).
  Qed.
  Lemma aheap_pres_x_weaken : forall LB LB' SP SP' X n Y k m m', aheap_pres_x LB' SP' X n m m' -> SP' <= SP ->
    (forall b, In b LB -> In b LB') -> (forall a, aclient_addr CI LB SP a -> ~ (Y <= a < Y + k) -> ~ (X <= a < X + n)) ->
    aheap_pres_x LB SP Y k m m'.
  Proof.
    intros LB LB' SP SP' X n Y k m m' H HS HL HX a Ha Hc Hy. apply H; [exact Ha| | exact (HX a Hc Hy)].
    eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Hc| exact HL]| exact HS].
  Qed.
  Lemma aheap_pres_x_rw_cells : forall LB SP X n m m' A cs, aheap_pres_x LB SP X n m m' -> rw_cells asegs m A cs ->
    aclient_range CI LB SP A (Z.of_nat (cells_size cs)) -> (A + Z.of_nat (cells_size cs) <= X \/ X + n <= A) -> rw_cells asegs m' A cs.
  Proof.
    intros LB SP X n m m' A cs HP [[Hwf (H0 & H1 & HB)] (W0 & W1 & HW)] HR HD.
    assert (CL : Z.of_nat (length (cells_bytes cs)) = Z.of_nat (cells_size cs)) by (rewrite cells_bytes_length by assumption; reflexivity).
    split; [split; [exact Hwf|]|].
    - split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi). unfold mrd.
      destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR| lia]) ltac:(lia)) as [E _]. rewrite E. reflexivity.
    - split; [exact W0|]. split; [exact W1|]. intros i Hi.
      destruct (HP (A + i) ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR| lia]) ltac:(lia)) as [_ W]. apply W. apply HW. exact Hi.
  Qed.
  Lemma aheap_pres_x_stk : forall LB SP X n m m' lo hi, aheap_pres_x LB SP X n m m' -> stk asegs m lo hi -> SP <= lo -> hi <= 2^47 ->
    (hi <= X \/ X + n <= lo) -> stk asegs m' lo hi.
  Proof.
    intros LB SP X n m m' lo hi HP (H0 & H1 & HW) HS HH HD. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) ltac:(lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.
  (* [comment removed for export] *)
  Lemma aclient_range_fake : forall LB SP c FA FN A n, In (mkABlock (ABFake c) FA FN) LB -> FA <= A -> A + n <= FA + FN ->
    aclient_range CI LB SP A n.
  Proof. intros LB SP c FA FN A n H H1 H2. left. right. right. exists c, FA, FN. split; [exact H|]. lia. Qed.
  Lemma aclient_range_fake_sh : forall LB SP c FA FN X, In (mkABlock (ABFake c) FA FN) LB -> FA <= X -> X + 8 <= FA + FN -> X mod 8 = 0 -> 0 <= X ->
    aclient_range CI LB SP (Z.shiftr X 3 + 2147450880) 1.
  Proof.
    intros LB SP c FA FN X H H1 H2 H3 H4. right. right. right. right. exists c, FA, FN. split; [exact H|].
    unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
  Qed.
  Lemma aclient_range_stack : forall LB SP A n, SP <= A -> A + n <= 2^47 -> aclient_range CI LB SP A n.
  Proof. intros LB SP A n H1 H2. left. left. lia. Qed.
End Pres.

Lemma lb_remove_keep_fake : forall p c FA FN LB, In (mkABlock (ABFake c) FA FN) LB -> In (mkABlock (ABFake c) FA FN) (lb_remove p LB).
Proof.
  intros p c FA FN LB H. unfold lb_remove. apply list_elem_of_In. apply list_elem_of_filter. split; [cbn; exact I| apply list_elem_of_In; exact H].
Qed.
Lemma lb_remove_keep_heap : forall p q A n LB, In (HB q A n) LB -> q <> p -> In (HB q A n) (lb_remove p LB).
Proof.
  intros p q A n LB H NE. unfold lb_remove. apply list_elem_of_In. apply list_elem_of_filter. split; [| apply list_elem_of_In; exact H].
  cbn [ab_kind abkind_eqb]. destruct (N.eqb_spec q p); [contradiction| cbn; exact I].
Qed.
Lemma lb_remove_sub : forall p b LB, In b (lb_remove p LB) -> In b LB.
Proof. intros p b LB H. unfold lb_remove in H. apply list_elem_of_In in H. apply list_elem_of_filter in H. apply list_elem_of_In. tauto. Qed.


End CANSEC1.
