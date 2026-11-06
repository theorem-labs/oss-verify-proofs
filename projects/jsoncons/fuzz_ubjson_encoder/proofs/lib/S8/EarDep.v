(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
     MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac EatAllocG EatDepotA EatDepotB EatDepot EarDepA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require HeapIfaceAEr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r7fbdc_7fe80.
Import ListNotations.
Import HeapIfaceAEr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition dp_has (M : word -> option byte) (l2 : Z) (ws : list Z) : Prop :=
  exists v, cellA M (DEP + 4 * (mm2 ws mod 2 ^ 20)) 4 v /\ 0 <= v < 2 ^ 32 /\ dp_chain M l2 (mm2 ws) v.
Definition DInvK (l2 blk : Z) (k : nat) (D : list (list Z)) (M : word -> option byte) : Prop :=
  DInvD l2 blk k M /\ forall ws, In ws D -> dp_has M l2 ws.

Definition DPreK (blk : Z) (M : word -> option byte) (trp : Z) (ws : list Z) : Prop :=
  (1 <= length ws <= 30)%nat /\ trp mod 8 = 0 /\ 4096 <= trp /\ trp + 8 * Z.of_nat (length ws) < 2 ^ 64 /\ apart trp (8 * Z.of_nat (length ws)) blk (2 ^ 23)
  /\ Forall (fun w => 0 <= w < 2 ^ 64) ws
  /\ (forall i, (i < length ws)%nat -> cellA M (trp + 8 * Z.of_nat i) 8 (nth i ws 0)).

Lemma In_kin : forall (Kt : list Z) D, In Kt D -> HAR.kin Kt D = true.
Proof.
  intros Kt D H. unfold HAR.kin. apply existsb_exists. exists Kt. split; [exact H|].
  destruct (list_eq_dec Z.eq_dec Kt Kt) as [_|N]; [reflexivity | contradiction].
Qed.
Lemma mm2_bucket : forall ws, 0 <= mm2 ws mod 2 ^ 20 < 2 ^ 20.
Proof. intros. apply Z.mod_pos_bound. lia. Qed.

Lemma dp_has_agree : forall (M M' : word -> option byte) l2 N ws,
  dp_has M l2 ws -> 0 <= l2 -> l2 + 2 ^ 20 < 2 ^ 64 -> 0 <= N < 2 ^ 16 ->
  (forall b, 0 <= b < 2 ^ 20 -> exists v, cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N) ->
  (forall x : word, DEP + 4 * (mm2 ws mod 2 ^ 20) <= U x < DEP + 4 * (mm2 ws mod 2 ^ 20) + 4 -> M' x = M x) ->
  (forall x : word, l2 + 16 <= U x < l2 + 16 * N + 16 -> M' x = M x) ->
  dp_has M' l2 ws.
Proof.
  intros M M' l2 N ws (v & C & R & CH) Hl2 Hl2' HN BK AG1 AG2. pose proof (mm2_bucket ws) as Hb. unfold dp_has.
  set (b := mm2 ws mod 2 ^ 20) in *. clearbody b.
  destruct (BK _ Hb) as (v0 & C0 & R0). assert (E : v = v0) by (apply (dp_cell4_inj M _ _ _ C C0); lia). subst v0.
  unfold DEP in *. exists v. split; [|split; [exact R|]].
  - apply (cell_agree M M'); [intros x Hx; apply AG1; change (Z.of_nat 4) with 4 in Hx; lia | lia | change (Z.of_nat 4) with 4; lia | exact C].
  - apply (dp_chain_agree M M' l2 (mm2 ws) v N CH); [lia | lia | lia | exact AG2].
Qed.

Lemma dp_has_insert : forall (M TM : word -> option byte) l2 N b v ws,
  dp_has M l2 ws -> 0 <= l2 -> l2 + 2 ^ 20 < 2 ^ 64 -> 0 <= N -> N + 1 < 2 ^ 16 -> 0 <= b < 2 ^ 20 ->
  (forall b', 0 <= b' < 2 ^ 20 -> exists v', cellA M (DEP + 4 * b') 4 v' /\ 0 <= v' <= N) ->
  cellA M (DEP + 4 * b) 4 v -> 0 <= v <= N ->
  cellA TM (DEP + 4 * b) 4 (N + 1) -> cellA TM (l2 + 16 * (N + 1) + 8) 4 v ->
  (forall x : word, DEP <= U x < DEP + 4 * 2 ^ 20 -> ~ (DEP + 4 * b <= U x < DEP + 4 * b + 4) -> TM x = M x) ->
  (forall x : word, l2 + 16 <= U x < l2 + 16 * N + 16 -> TM x = M x) ->
  dp_has TM l2 ws.
Proof.
  intros M TM l2 N b v ws (v1 & C1 & R1 & CH1) Hl2 Hl2' HN HN' Hb BK Cv Rv CT1 CT2 AG1 AG2. pose proof (mm2_bucket ws) as Hb1. unfold dp_has.
  set (b1 := mm2 ws mod 2 ^ 20) in *. clearbody b1.
  destruct (BK _ Hb1) as (v0 & C0 & R0). assert (E : v1 = v0) by (apply (dp_cell4_inj M _ _ _ C1 C0); lia). subst v0.
  assert (CH1' : dp_chain TM l2 (mm2 ws) v1) by (apply (dp_chain_agree M TM l2 (mm2 ws) v1 N CH1); [lia | lia | lia | exact AG2]).
  destruct (Z.eq_dec b1 b) as [Eb|Nb].
  - subst b1. assert (E : v1 = v) by (apply (dp_cell4_inj M _ _ _ C1 Cv); lia). subst v1.
    exists (N + 1). split; [exact CT1|]. split; [lia|].
    apply (dpc_next TM l2 (mm2 ws) (N + 1) v); [lia | exact CT2 | lia | exact CH1'].
  - exists v1. split; [|split; [exact R1 | exact CH1']]. unfold DEP in *.
    apply (cell_agree M TM); [intros x Hx; apply AG1; change (Z.of_nat 4) with 4 in Hx; lia | lia | change (Z.of_nat 4) with 4; lia | exact C1].
Qed.

Lemma DInvK_D : forall l2 blk k D M, DInvK l2 blk k D M -> DInvD l2 blk k M.
Proof. intros l2 blk k D M [H _]. exact H. Qed.
Lemma DInvK_nil : forall l2 blk k M, DInvD l2 blk k M -> DInvK l2 blk k [] M.
Proof. intros l2 blk k M H. split; [exact H|]. intros ws []. Qed.
Lemma DInvK_incl : forall l2 blk k D0 D1 M, DInvK l2 blk k D1 M -> incl D0 D1 -> DInvK l2 blk k D0 M.
Proof. intros l2 blk k D0 D1 M [H1 H2] I. split; [exact H1|]. intros ws Hw. apply H2. apply I. exact Hw. Qed.
Lemma DInvK_weaken : forall l2 blk k D M, DInvK l2 blk (S k) D M -> DInvK l2 blk k D M.
Proof. intros l2 blk k D M [H1 H2]. split; [apply DInvD_weaken; exact H1 | exact H2]. Qed.
Lemma DInvK_pred : forall l2 blk k D M, DInvK l2 blk k D M -> DInvK l2 blk (pred k) D M.
Proof. intros l2 blk k D M H. destruct k as [|k]; [exact H | apply DInvK_weaken; exact H]. Qed.
Lemma DInvK_le : forall l2 blk k k' D M, DInvK l2 blk k D M -> (k' <= k)%nat -> DInvK l2 blk k' D M.
Proof.
  intros l2 blk k k' D M H L. induction k as [|k IH]; [replace k' with 0%nat by lia; exact H|].
  destruct (Nat.eq_dec k' (S k)) as [->|NE]; [exact H|]. apply IH; [apply DInvK_weaken; exact H | lia].
Qed.
Lemma DInvK_known : forall l2 blk k D M ws, DInvK l2 blk k D M -> In ws D -> DInvK l2 blk k (ws :: D) M.
Proof. intros l2 blk k D M ws H I. apply (DInvK_incl l2 blk k (ws :: D) D M H). intros x [<-|Hx]; assumption. Qed.

Lemma DInvK_post_plain : forall l2 blk k D (K : list Z) M, DInvK l2 blk (if HAR.kin K D then S k else pred (S k)) (K :: D) M -> DInvK l2 blk k D M.
Proof.
  intros l2 blk k D K M H. apply (DInvK_incl l2 blk k D (K :: D) M); [|intros x Hx; right; exact Hx].
  destruct (HAR.kin K D); [apply DInvK_weaken; exact H | exact H].
Qed.
Lemma DInvK_frame : forall l2 blk D, art_depot_frame (fun k => DInvK l2 blk k D) (dprivD l2 blk).
Proof.
  intros l2 blk D k M M' [H1 H2] AG. split; [apply (DInvD_frame l2 blk k M M' H1 AG)|].
  intros ws Hw. pose proof (H2 ws Hw) as HS. pose proof (mm2_bucket ws) as Hb.
  destruct H1 as (N & TF & ST & G1 & G2 & G3 & G4 & G5 & G6 & G7 & CN & RN & BN & CTF & RTF & BTF & CST & RST & BST & CM1 & CBL & BK & ND & W1 & W2 & W3 & W4).
  apply (dp_has_agree M M' l2 N ws HS); [lia | lia | lia | exact BK | |].
  - set (b := mm2 ws mod 2 ^ 20) in *. clearbody b. intros x Hx. apply AG. unfold dprivD. unfold DEP in Hx. lia.
  - intros x Hx. apply AG. unfold dprivD. lia.
Qed.

Lemma DPreK_D : forall blk M trp ws, DPreK blk M trp ws -> DPreD blk M trp (Z.of_nat (length ws)).
Proof.
  intros blk M trp ws (Hl & Ha & Ht & Ht' & AP & WR & WC). unfold DPreD. split; [lia|]. repeat (split; [assumption|]).
  intros i Hi. pose proof (WC (Z.to_nat i) ltac:(lia)) as C. rewrite Z2Nat.id in C by lia. eexists. exact C.
Qed.
Lemma DPreK_frame : forall blk M M' trp ws, DPreK blk M trp ws ->
  (forall x : word, trp <= U x < trp + 8 * Z.of_nat (length ws) -> M' x = M x) -> DPreK blk M' trp ws.
Proof.
  intros blk M M' trp ws (Hl & Ha & Ht & Ht' & AP & WR & WC) AG. repeat (split; [assumption|]).
  intros i Hi. apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | apply WC; exact Hi].
Qed.

Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
#[local] Ltac nlit := first [ let E := fresh in intros E; discriminate E | apply nrange_lit; vm_compute; reflexivity ].

Theorem dp_put_K : forall l2 blk (k0 : nat) (D : list (list Z)) (ws : list Z) regs (M rom : word -> option byte) (raw : word) (sp trp szt : Z),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 szt ->
    224 <= sp -> sp < 2 ^ 64 -> 0x698000 <= sp - 224 -> wrA M (sp - 224) 224 -> nodp (dprivD l2 blk) (sp - 224) 224 ->
    DInvK l2 blk k0 D M -> (In ws D \/ (1 <= k0)%nat) -> szt = Z.of_nat (length ws) -> apart (sp - 224) 224 trp (8 * szt) -> DPreK blk M trp ws -> DRoD M ->
    exists regs' M' id,
      msteps ASEGS (mkst regs (0x9a948 : word) M rom) (mkst regs' raw M' rom)
      /\ getr regs' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
      /\ (forall r : reg, art_depot_kept r -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, ~ dprivD l2 blk (bv_unsigned x) -> ~ (sp - 224 <= bv_unsigned x < sp) -> M' x = M x)
      /\ DInvK l2 blk (if HAR.kin ws D then k0 else pred k0) (ws :: D) M'.
Proof.
  intros l2 blk k0 D ws regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DIK HK Eszt ATF DPK DR.
  pose proof DIK as (DI & DHAS). pose proof (DPreK_D blk M trp ws DPK) as DP. rewrite <- Eszt in DP.
  pose proof DPK as (_ & _ & _ & _ & _ & WRG & WCL).
  pose proof DI as DI0.
  destruct DI as (N & TF & ST & G1 & G2 & G3 & G4 & G5 & G6 & G7 & CN & RN & BN & CTF & RTF & BTF & CST & RST & BST & CM1 & CBL & BK & NDS & W1 & W2 & W3 & W4).
  destruct DP as (Hsz & Hta & Ht4 & Ht' & AT & RC). destruct DR as (Cm & Ck1 & Ck2).
  unfold NID, STO, MAP1, DEP in *.
  assert (Al2 : apart (sp - 224) 224 l2 (2 ^ 20)) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
  assert (Ablk : apart (sp - 224) 224 blk (2 ^ 23)) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
  assert (Ast : apart (sp - 224) 224 0x2138c8 4381408) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).

  destruct (dp_pro_fn regs M rom raw sp trp szt 0xc6a4a7935bd1e995 0x35253c9ade8f4ca8 0x9747b28c9747b28c H2 H10 H11 H1 Hsp6 Hsp Ht4 Ht' Hsz
              ltac:(lia) ltac:(lia) ltac:(lia) Cm Ck1 Ck2 W) as (r1 & h0 & RUN1 & P11 & P14 & P10 & P12 & Rh0 & P13 & P8 & P9 & P2 & K1 & Fh0).
  set (F := dp_frame M sp trp szt raw regs) in RUN1.
  assert (GF : mem_grows M F) by (unfold F, dp_frame; repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl).
  assert (OF : forall x : word, ~ (sp - 104 <= U x < sp) -> F x = M x).
  { intros x Hx. pose proof (u64_range x). unfold F, dp_frame. rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }

  assert (RCF : forall j, 0 <= j < szt -> rcell F (trp + 8 * j)) by (intros j Hj; apply (rcell_grows M F _ GF); apply RC; exact Hj).
  replace (Z_to_bv 64 trp : word) with (Z_to_bv 64 (trp + 8 * 0) : word) in P11 by (f_equal; lia).
  assert (WCF : forall j, 0 <= j < szt -> cellA F (trp + 8 * j) 8 (nth (Z.to_nat j) ws 0)).
  { intros j Hj. pose proof (WCL (Z.to_nat j) ltac:(clear - Hj Eszt; Lia.lia)) as C. rewrite Z2Nat.id in C by (clear - Hj; Lia.lia).
    apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in ATF; cbn in Hx; clear - Hx Hj ATF; Lia.lia | lia | cbn; lia | exact C]. }
  assert (WRZ : forall j, 0 <= j < szt -> 0 <= nth (Z.to_nat j) ws 0 < 2 ^ 64).
  { intros j Hj. rewrite Forall_forall in WRG. apply WRG. apply nth_In. clear - Hj Eszt. Lia.lia. }
  destruct (dp_hash_fn (Z.to_nat (szt - 1)) r1 F rom trp szt 0xc6a4a7935bd1e995 0 h0 ws WCF WRZ Eszt ltac:(lia) ltac:(lia) ltac:(lia) Rh0 ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; lia) P11 P14 P10 P12) as (r2 & hN & RUN2 & Q11 & Q12 & RhN & K2 & FhN).

  unfold DEP, MAP1 in *.
  assert (X13 : getr r2 13 = Z_to_bv 64 0) by (rewrite (K2 13%bv) by (intros E; discriminate E); exact P13).
  assert (X10 : getr r2 10 = Z_to_bv 64 0xc6a4a7935bd1e995) by (rewrite (K2 10%bv) by (intros E; discriminate E); exact P10).
  assert (X9 : getr r2 9 = Z_to_bv 64 2242776) by (rewrite (K2 9%bv) by (intros E; discriminate E); exact P9).
  assert (BKF : forall b, 0 <= b < 2 ^ 20 -> exists v, cellA F (2242776 + 4 * b) 4 v /\ 0 <= v <= N).
  { intros b Hb. destruct (BK b Hb) as (v & Cv & Rv). exists v. split; [|exact Rv].
    apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact Cv]. }
  destruct (dp_mid_fn r2 F rom hN 0xc6a4a7935bd1e995 N Q12 X13 X10 X9 RhN ltac:(lia) ltac:(lia) BKF)
    as (r3 & h & b & v & RUN3 & Rh & Rb & Cv & Rv & T19 & T18 & T11 & T25 & T24 & T20 & T22 & T23 & T9 & K3 & Fh & Fb).
  assert (Eh : h = mm2 ws).
  { rewrite Fh, FhN, Fh0, Eszt. unfold mm2, mm2g, MM2.MC, MM2.K1, MM2.K2. change (Z.to_nat 0) with 0%nat. cbn [skipn]. reflexivity. }
  assert (Eb : mm2 ws mod 2 ^ 20 = b) by (rewrite <- Eh; symmetry; exact Fb).
  clear Fh FhN Fh0 Fb.

  assert (CM1F : cellA F 6437096 8 l2) by (apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CM1]).
  assert (NDSF : dp_nodes F l2 N).
  { intros id Hid. destruct (NDS id Hid) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk. split; [exact Rhv|]. split; [|split; [|exact Rlk]].
    - apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Al2; cbn in Hx; lia | lia | cbn; lia | exact Chv].
    - apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Al2; cbn in Hx; lia | lia | cbn; lia | exact Clk]. }
  assert (Hl16 : l2 mod 16 = 0).
  { apply (proj2 (Z.mod_divide l2 16 ltac:(lia))). apply (Z.divide_trans 16 4096 l2); [exists 256; reflexivity | apply (proj1 (Z.mod_divide l2 4096 ltac:(lia))); exact G3]. }
  destruct (dp_find_fn (Z.to_nat v) r3 F rom l2 N h v ltac:(lia) CM1F ltac:(lia) ltac:(lia) Hl16 ltac:(lia) NDSF ltac:(lia) Rh T11 T19 T24 T22)
    as (r4 & ALT & K4).
  assert (Y2 : getr r4 2 = Z_to_bv 64 (sp - 112)).
  { rewrite (K4 2%bv) by nlit. rewrite (K3 2%bv) by nlit. rewrite (K2 2%bv) by nlit. exact P2. }

  assert (L1 : cellA F (sp - 8) 8 (U raw)) by (unfold F, dp_frame; zcell).
  assert (L2 : cellA F (sp - 16) 8 (U (getr regs 8))) by (unfold F, dp_frame; zcell).
  assert (L3 : cellA F (sp - 24) 8 (U (getr regs 9))) by (unfold F, dp_frame; zcell).
  assert (L4 : cellA F (sp - 32) 8 (U (getr regs 18))) by (unfold F, dp_frame; zcell).
  assert (L5 : cellA F (sp - 40) 8 (U (getr regs 19))) by (unfold F, dp_frame; zcell).
  assert (L6 : cellA F (sp - 48) 8 (U (getr regs 20))) by (unfold F, dp_frame; zcell).
  assert (L7 : cellA F (sp - 56) 8 (U (getr regs 21))) by (unfold F, dp_frame; zcell).
  assert (L8 : cellA F (sp - 64) 8 (U (getr regs 22))) by (unfold F, dp_frame; zcell).
  assert (L9 : cellA F (sp - 72) 8 (U (getr regs 23))) by (unfold F, dp_frame; zcell).
  assert (L10 : cellA F (sp - 80) 8 (U (getr regs 24))) by (unfold F, dp_frame; zcell).
  assert (L11 : cellA F (sp - 88) 8 (U (getr regs 25))) by (unfold F, dp_frame; zcell).

  assert (KF : forall r : reg, r = 3%bv \/ r = 4%bv \/ r = 26%bv \/ r = 27%bv -> getr r4 r = getr regs r).
  { intros r Hr. destruct Hr as [->|[->|[->| ->]]];
      (rewrite (K4 _) by nlit; rewrite (K3 _) by nlit; rewrite (K2 _) by nlit; apply K1; nlit). }
  assert (AGF : forall x : word, dprivD l2 blk (U x) -> F x = M x).
  { intros x Dx. apply OF. intros Wx. exact (ND (U x) ltac:(lia) Dx). }
  assert (DKF : DInvK l2 blk k0 D F) by (exact (DInvK_frame l2 blk D k0 M F DIK AGF)).
  destruct ALT as [(RUN4 & Z11 & NCH) | (RUN4 & (id & Rid & Z10) & YCH)].
  2: {
    destruct (dp_epi_run regs r4 F rom raw sp Y2 Hret ltac:(lia) Hsp L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11)
      as (r5 & RUN5 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K5).
    exists r5, F, id. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. exact RUN5.
    - rewrite E10. exact Z10.
    - lia.
    - intros r Hk. unfold art_depot_kept in Hk.
      destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [rewrite E2, H2; reflexivity | | | exact E8 | exact E9 |].
      + rewrite (K5 3%bv) by nlit. apply KF. tauto.
      + rewrite (K5 4%bv) by nlit. apply KF. tauto.
      + destruct (reg_cases_18_27 r Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; try assumption;
          (rewrite (K5 _) by nlit; apply KF; tauto).
    - exact GF.
    - intros x NDx NWx. apply OF. lia.
    - assert (DKF' : DInvK l2 blk k0 (ws :: D) F).
      { split; [exact (proj1 DKF)|]. intros ws' [<-|Hw']; [|exact (proj2 DKF ws' Hw')].
        exists v. rewrite Eb, <- Eh. split; [exact Cv|]. split; [clear - Rv BN; Lia.lia | exact YCH]. }
      destruct (HAR.kin ws D); [exact DKF' | apply DInvK_pred; exact DKF']. }

  assert (NIN : ~ In ws D).
  { intros IN. destruct (proj2 DKF ws IN) as (v' & Cv' & Rv' & CH'). rewrite Eb in Cv'. rewrite <- Eh in CH'.
    apply NCH. replace v with v'; [exact CH' | exact (dp_cell4_inj F _ _ _ Cv' Cv Rv' ltac:(clear - Rv BN; Lia.lia))]. }
  destruct HK as [IN|HK1]; [contradiction|].
  destruct k0 as [|k]; [exfalso; clear - HK1; Lia.lia|].
  replace (HAR.kin ws D) with false by (destruct (HAR.kin ws D) eqn:E; [apply HAR.kin_In in E; contradiction | reflexivity]).
  cbn [pred].
  rewrite Nat2Z.inj_succ in BN, BTF, BST.

  assert (SL : exists r5, msteps ASEGS (mkst r4 (0x9aae0 : word) F rom) (mkst r5 (0x9b0dc : word) F rom)
            /\ (getr r5 10 = Z_to_bv 64 (2242776 + 4 * b) /\ getr r5 1 = Z_to_bv 64 0x9aae8 /\ getr r5 2 = Z_to_bv 64 (sp - 112)
                /\ (forall r : reg, r <> 1%bv -> r <> 10%bv -> getr r5 r = getr r4 r))).
  { assert (Y18 : getr r4 18 = Z_to_bv 64 (2242776 + 4 * b)) by (rewrite (K4 18%bv) by nlit; exact T18).
    eexists. split.
    - zstep F_9aa90 D_9aa90.
      stepn F_9aa94 D_9aa94.
      apply mst_refl.
    - split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N1 N10. kept_solve. }
  destruct SL as (r5 & RUN5 & U10 & U1 & U2 & K5).

  assert (WFv : wrA F (2242776 + 4 * b) 4) by (apply (wr_grows _ M F _ _ GF); apply (wr_sub _ _ _ _ _ _ W1); lia).
  assert (WFf : wrA F (sp - 112 - 48) 48) by (apply (wr_grows _ M F _ _ GF); apply (wr_sub _ _ _ _ _ _ W); lia).
  assert (AM4 : (2242776 + 4 * b) mod 4 = 0) by (replace (2242776 + 4 * b) with ((560694 + b) * 4) by lia; apply Z_mod_mult).
  assert (U1' : getr r5 1 = (0x9aae8 : word)%bv) by (rewrite U1; apply bv_eq; vm_compute; reflexivity).
  destruct (dp_lock_run r5 F rom (0x9aae8 : word)%bv (sp - 112) (2242776 + 4 * b) v U2 U10 U1'
              ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AM4 ltac:(lia)
              Cv WFv WFf ltac:(unfold apart in Ast |- *; lia)) as (r6 & RUN6 & V10 & V2 & K6).
  set (LM := dp_lock_mem F (sp - 112) (2242776 + 4 * b) v (0x9aae8 : word)%bv (getr r5 8) (getr r5 9) (getr r5 18) (getr r5 19)) in RUN6.
  assert (GLM : mem_grows M LM) by (unfold LM, dp_lock_mem; do 6 (eapply mem_grows_trans; [|apply Wn_grows]); exact GF).
  assert (OLM : forall x : word, ~ (sp - 160 <= U x < sp) -> ~ (2242776 + 4 * b <= U x < 2242776 + 4 * b + 4) -> LM x = M x).
  { intros x Hx1 Hx2. pose proof (u64_range x). unfold LM, dp_lock_mem. rewrite !Wn_outside by (first [lia | cbn; lia]). apply OF. lia. }

  #[local] Ltac chase K := rewrite (K _) by nlit.
  assert (V25 : getr r6 25 = Z_to_bv 64 v) by (chase K6; chase K5; chase K4; exact T25).
  assert (V9 : getr r6 9 = Z_to_bv 64 2242776) by (chase K6; chase K5; chase K4; exact T9).
  assert (V24 : getr r6 24 = Z_to_bv 64 6437096) by (chase K6; chase K5; chase K4; exact T24).
  assert (V22 : getr r6 22 = Z_to_bv 64 65535) by (chase K6; chase K5; chase K4; exact T22).
  assert (V19 : getr r6 19 = Z_to_bv 64 h) by (chase K6; chase K5; chase K4; exact T19).
  assert (CNL : cellA LM 6437080 4 N) by (apply (cell_agree M LM); [intros x Hx; apply OLM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CN]).
  assert (CML : cellA LM 6437096 8 l2) by (apply (cell_agree M LM); [intros x Hx; apply OLM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CM1]).
  assert (WNL : wokA LM 6437080 4) by (apply (wr_wok _ _ _ _ (wr_grows _ M LM _ _ GLM W1)); lia).
  pose proof (dp_ins_run r6 LM rom sp v h N l2 V10 V25 V9 V24 V22 V19 V2 ltac:(lia) Hsp ltac:(lia) ltac:(lia) ltac:(lia) Rh G1 G2 CNL CML WNL)
    as (r7 & RUN7 & I10 & I11 & I12 & I13 & I1 & I2 & I23 & I9 & I21 & I8 & I18 & K7).
  set (IM := Wn 4 LM 6437080 (N + 1)) in RUN7.
  assert (GIM : mem_grows M IM) by (unfold IM; eapply mem_grows_trans; [exact GLM | apply Wn_grows]).
  assert (OIM : forall x : word, ~ (sp - 160 <= U x < sp) -> ~ (2242776 + 4 * b <= U x < 2242776 + 4 * b + 4) -> ~ (6437080 <= U x < 6437084) -> IM x = M x).
  { intros x Hx1 Hx2 Hx3. pose proof (u64_range x). unfold IM. rewrite Wn_outside by (first [lia | cbn; lia]). apply OLM; assumption. }

  set (nd := l2 + 16 * (N + 1)) in *. assert (End : nd = l2 + 16 * (N + 1)) by reflexivity.
  assert (HND : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0).
  { subst nd. split; [lia|]. split; [lia|]. apply (proj2 (Z.mod_divide _ 16 ltac:(lia))).
    apply Z.divide_add_r; [| exists (N + 1); lia]. apply (proj1 (Z.mod_divide l2 16 ltac:(lia))). exact Hl16. }
  assert (HBLK : 0x698000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0).
  { split; [lia|]. split; [lia|]. apply (proj2 (Z.mod_divide blk 8 ltac:(lia))).
    apply (Z.divide_trans 8 4096 blk); [exists 512; reflexivity | apply (proj1 (Z.mod_divide blk 4096 ltac:(lia))); exact G6]. }
  assert (CI1 : cellA IM (sp - 104) 8 trp) by (unfold IM, LM, dp_lock_mem, F, dp_frame; zcell).
  assert (CI2 : cellA IM (sp - 96) 8 szt) by (unfold IM, LM, dp_lock_mem, F, dp_frame; zcell).
  assert (CI3 : cellA IM 2177224 8 TF) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CTF]).
  assert (CI4 : cellA IM (2177224 + 16) 8 blk) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CBL]).
  assert (CI5 : cellA IM (2177224 + 24) 4 ST) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CST]).
  assert (RCI : forall i, 0 <= i < szt -> rcell IM (trp + 8 * i)) by (intros i Hi; apply (rcell_grows M IM _ GIM); apply RC; exact Hi).
  assert (WI1 : wrA IM (sp - 224) 112) by (apply (wr_grows _ M IM _ _ GIM); apply (wr_sub _ _ _ _ _ _ W); lia).
  assert (WI2 : wrA IM nd 16) by (apply (wr_grows _ M IM _ _ GIM); apply (wr_sub _ _ _ _ _ _ W3); lia).
  assert (WI3 : wrA IM blk (2 ^ 23)) by (apply (wr_grows _ M IM _ _ GIM); exact W4).
  assert (WI4 : wrA IM 2177224 32) by (apply (wr_grows _ M IM _ _ GIM); exact W2).
  pose proof (dp_store_run IM rom sp nd h trp szt TF ST blk l2) as ST8.
  repeat lazymatch type of ST8 with
    | forall rg : bvmap 5 word, _ => fail
    | ?P -> _ => let HP := fresh in assert (HP : P) by (first [eassumption | lia]); specialize (ST8 HP); clear HP
    end.
  fold nd in I10, I9.
  destruct (ST8 r7 I10 I11 I12 I13 I1 I2) as (r8 & SM & RUN8 & S2' & K8 & G8 & O8 & C1 & C2 & C3 & C4 & C5). clear ST8.

  assert (J9 : getr r8 9 = Z_to_bv 64 nd) by (rewrite (K8 9%bv) by (cbv; tauto); exact I9).
  assert (J21 : getr r8 21 = Z_to_bv 64 v) by (rewrite (K8 21%bv) by (cbv; tauto); exact I21).
  assert (J23 : getr r8 23 = Z_to_bv 64 (N + 1)) by (rewrite (K8 23%bv) by (cbv; tauto); exact I23).
  assert (J18 : getr r8 18 = Z_to_bv 64 (2242776 + 4 * b)).
  { rewrite (K8 18%bv) by (cbv; tauto). rewrite I18. chase K6. chase K5. chase K4. exact T18. }
  assert (J8 : getr r8 8 = Z_to_bv 64 0).
  { rewrite (K8 8%bv) by (cbv; tauto). rewrite I8. chase K6. chase K5. chase K4. chase K3. chase K2. exact P8. }
  assert (GSM : mem_grows M SM) by (eapply mem_grows_trans; [exact GIM | exact G8]).
  destruct (dp_tail_run r8 SM rom sp nd v (N + 1) (2242776 + 4 * b) J9 J21 J23 J18 J8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply (wr_wok _ _ _ _ (wr_grows _ M SM _ _ GSM W3)); lia) ltac:(apply (wr_wok _ _ _ _ (wr_grows _ M SM _ _ GSM W1)); lia))
    as (r9 & RUN9 & J10 & K9).
  set (TM := Wn 4 (Wn 4 SM (nd + 8) v) (2242776 + 4 * b) (N + 1)) in RUN9.

  unfold apart in Ast, Al2, Ablk, G7.
  assert (AG : forall x : word, ~ (sp - 224 <= U x < sp) -> ~ (2242776 + 4 * b <= U x < 2242776 + 4 * b + 4) -> ~ (6437080 <= U x < 6437084) ->
               ~ (nd <= U x < nd + 16) -> ~ (2177224 <= U x < 2177232) -> ~ (2177248 <= U x < 2177252) ->
               ~ (blk + 8 * TF <= U x < blk + 8 * TF + 8 * (szt + 1)) -> TM x = M x).
  { intros x X1 X2 X3 X4 X5 X6 X7. pose proof (u64_range x). unfold TM. rewrite !Wn_outside by (first [lia | cbn; lia]).
    rewrite (O8 x) by (unfold dp_store_out, STO; repeat split; lia). apply OIM; lia. }

  assert (SLOT : forall a u, sp - 88 <= a -> a + 8 <= sp -> cellA F a 8 u -> cellA TM a 8 u).
  { intros a u Ha1 Ha2 C. unfold TM. apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |].
    apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |].
    apply (cell_agree IM SM); [intros x Hx; apply O8; unfold dp_store_out, STO; cbn in Hx; repeat split; lia | lia | cbn; lia |].
    unfold IM, LM, dp_lock_mem. do 7 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C. }
  assert (Z2 : getr r9 2 = Z_to_bv 64 (sp - 112)) by (rewrite (K9 2%bv) by nlit; exact S2').
  destruct (dp_epi_run regs r9 TM rom raw sp Z2 Hret ltac:(lia) Hsp
              (SLOT (sp - 8) _ ltac:(lia) ltac:(lia) L1) (SLOT (sp - 16) _ ltac:(lia) ltac:(lia) L2) (SLOT (sp - 24) _ ltac:(lia) ltac:(lia) L3) (SLOT (sp - 32) _ ltac:(lia) ltac:(lia) L4) (SLOT (sp - 40) _ ltac:(lia) ltac:(lia) L5) (SLOT (sp - 48) _ ltac:(lia) ltac:(lia) L6) (SLOT (sp - 56) _ ltac:(lia) ltac:(lia) L7) (SLOT (sp - 64) _ ltac:(lia) ltac:(lia) L8) (SLOT (sp - 72) _ ltac:(lia) ltac:(lia) L9) (SLOT (sp - 80) _ ltac:(lia) ltac:(lia) L10) (SLOT (sp - 88) _ ltac:(lia) ltac:(lia) L11))
    as (r10 & RUN10 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K10).
  exists r10, TM, (N + 1). split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
    eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
    eapply msteps_trans; [exact RUN9|]. exact RUN10.
  - rewrite E10. exact J10.
  - lia.
  -
    assert (KALL : forall r : reg, r = 3%bv \/ r = 4%bv \/ r = 26%bv \/ r = 27%bv -> getr r10 r = getr regs r).
    { intros r Hr. rewrite <- (KF r Hr). destruct Hr as [->|[->|[->| ->]]];
        (chase K10; chase K9; rewrite (K8 _) by (cbv; tauto); chase K7; chase K6; chase K5; reflexivity). }
    intros r Hk. unfold art_depot_kept in Hk.
    destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [rewrite E2, H2; reflexivity | apply KALL; tauto | apply KALL; tauto | exact E8 | exact E9 |].
    destruct (reg_cases_18_27 r Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; try assumption; (apply KALL; tauto).
  - unfold TM. do 2 (eapply mem_grows_trans; [|apply Wn_grows]). exact GSM.
  - intros x NDx NWx. apply AG; try lia; intros BAD; apply NDx; unfold dprivD; lia.
  -
    split.
    2:{ assert (CT1 : cellA TM (2242776 + 4 * b) 4 (N + 1)) by (unfold TM; apply cell_Wn_hit; cbn; lia).
        assert (CT2 : cellA TM (l2 + 16 * (N + 1) + 8) 4 v).
        { unfold TM. apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]. fold nd. apply cell_Wn_hit; cbn; lia. }
        intros ws' [<-|Hw'].
        - exists (N + 1). rewrite Eb, <- Eh. split; [exact CT1|]. split; [lia|].
          apply dpc_here; [lia|]. unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). fold nd. exact C4.
        - apply (dp_has_insert M TM l2 N b v ws' (DHAS ws' Hw')); unfold DEP; try lia; try assumption.
          + apply (cell_agree F M); [intros x Hx; symmetry; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact Cv].
          + intros x Hx1 Hx2. apply AG; lia.
          + intros x Hx. apply AG; lia. }
    exists (N + 1), (TF + szt + 1), (ST + szt + 1). unfold NID, STO, MAP1, DEP.
    assert (WT : forall a n, wrA M a n -> wrA TM a n).
    { intros a n Wa. unfold TM. apply wr_Wn. apply wr_Wn. apply (wr_grows _ M SM _ _ GSM). exact Wa. }
    zsplit; try assumption; try lia.
    +   unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]).
      apply (cell_agree IM SM); [intros x Hx; apply O8; unfold dp_store_out, STO; cbn in Hx; repeat split; lia | lia | cbn; lia |].
      unfold IM. apply cell_Wn_hit; cbn; lia.
    +   unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]).
      replace (TF + szt + 1) with (TF + szt + 1) by lia. exact C1.
    +   unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C2.
    +   apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CM1].
    +   unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C3.
    +   intros b' Hb'. destruct (Z.eq_dec b' b) as [->|NE].
      * exists (N + 1). split; [|lia]. unfold TM. apply cell_Wn_hit; cbn; lia.
      * destruct (BK b' Hb') as (v' & Cv' & Rv'). exists v'. split; [|lia].
        apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cv'].
    +   intros id Hid. destruct (Z.eq_dec id (N + 1)) as [->|NE].
      * exists h, v. split; [exact Rh|]. split; [|split; [|lia]].
        -- unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). fold nd. exact C4.
        -- unfold TM. apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]. fold nd. apply cell_Wn_hit; cbn; lia.
      * destruct (NDS id ltac:(lia)) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk. split; [exact Rhv|]. split; [|split; [|exact Rlk]].
        -- apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Chv].
        -- apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Clk].
    + apply WT. exact W1.
    + apply WT. exact W2.
    + apply WT. exact W3.
    + apply WT. exact W4.
Qed.

Theorem dp_put_learn : forall l2 blk (k : nat) (D : list (list Z)) (ws : list Z) regs (M rom : word -> option byte) (raw : word) (sp trp szt : Z),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 szt ->
    224 <= sp -> sp < 2 ^ 64 -> 0x698000 <= sp - 224 -> wrA M (sp - 224) 224 -> nodp (dprivD l2 blk) (sp - 224) 224 ->
    DInvK l2 blk (S k) D M -> szt = Z.of_nat (length ws) -> apart (sp - 224) 224 trp (8 * szt) -> DPreK blk M trp ws -> DRoD M ->
    exists regs' M' id,
      msteps ASEGS (mkst regs (0x9a948 : word) M rom) (mkst regs' raw M' rom)
      /\ getr regs' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
      /\ (forall r : reg, art_depot_kept r -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, ~ dprivD l2 blk (bv_unsigned x) -> ~ (sp - 224 <= bv_unsigned x < sp) -> M' x = M x)
      /\ DInvK l2 blk k (ws :: D) M'.
Proof.
  intros l2 blk k D ws regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DIK Eszt ATF DPK DR.
  destruct (dp_put_K l2 blk (S k) D ws regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DIK ltac:(right; clear; Lia.lia) Eszt ATF DPK DR)
    as (regs' & M' & id & RUN & P10 & Rid & KP & G & AG & DI').
  exists regs', M', id. repeat (split; [assumption|]).
  destruct (HAR.kin ws D); [apply DInvK_weaken; exact DI' | exact DI'].
Qed.

Theorem dp_put_warm : forall l2 blk (k : nat) (D : list (list Z)) (ws : list Z) regs (M rom : word -> option byte) (raw : word) (sp trp szt : Z),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 szt ->
    224 <= sp -> sp < 2 ^ 64 -> 0x698000 <= sp - 224 -> wrA M (sp - 224) 224 -> nodp (dprivD l2 blk) (sp - 224) 224 ->
    DInvK l2 blk k D M -> In ws D -> szt = Z.of_nat (length ws) -> apart (sp - 224) 224 trp (8 * szt) -> DPreK blk M trp ws -> DRoD M ->
    exists regs' M' id,
      msteps ASEGS (mkst regs (0x9a948 : word) M rom) (mkst regs' raw M' rom)
      /\ getr regs' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
      /\ (forall r : reg, art_depot_kept r -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, ~ dprivD l2 blk (bv_unsigned x) -> ~ (sp - 224 <= bv_unsigned x < sp) -> M' x = M x)
      /\ DInvK l2 blk k D M'.
Proof.
  intros l2 blk k D ws regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DIK IN Eszt ATF DPK DR.
  destruct (dp_put_K l2 blk k D ws regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DIK (or_introl IN) Eszt ATF DPK DR)
    as (regs' & M' & id & RUN & P10 & Rid & KP & G & AG & DI').
  exists regs', M', id. repeat (split; [assumption|]).
  rewrite (In_kin ws D IN) in DI'. apply (DInvK_incl l2 blk k D (ws :: D) M' DI'). intros x Hx. right. exact Hx.
Qed.
End FPX.
