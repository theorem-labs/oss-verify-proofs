(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
     MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocG_b BatDepotA_b BatDepotB_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r7fbdc_7fe80_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dprivD (l2 blk x : Z) : Prop := 0x211b08 <= x < 0x661b28 \/ l2 <= x < l2 + 2 ^ 20 \/ blk <= x < blk + 2 ^ 23.

(* [comment removed for export] *)
Definition DRoD (M : word -> option byte) : Prop :=
  cellA M 0x102e8 8 0xc6a4a7935bd1e995 /\ cellA M 0x10320 8 0x35253c9ade8f4ca8 /\ cellA M 0x10418 8 0x9747b28c9747b28c.

(* [comment removed for export] *)
Definition DPreD (blk : Z) (M : word -> option byte) (trp szt : Z) : Prop :=
  1 <= szt <= 30 /\ trp mod 8 = 0 /\ 4096 <= trp /\ trp + 8 * szt < 2 ^ 64 /\ apart trp (8 * szt) blk (2 ^ 23)
  /\ (forall i, 0 <= i < szt -> rcell M (trp + 8 * i)).

(* [comment removed for export] *)
Definition DInvD (l2 blk : Z) (k : nat) (M : word -> option byte) : Prop :=
  exists N TF ST,
    0x696000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 47 /\ l2 mod 4096 = 0 /\ 0x696000 <= blk /\ blk + 2 ^ 23 < 2 ^ 47 /\ blk mod 4096 = 0 /\ apart l2 (2 ^ 20) blk (2 ^ 23)
    /\ cellA M NID 4 N /\ 0 <= N /\ N + Z.of_nat k < 2 ^ 16 - 1
    /\ cellA M STO 8 TF /\ 0 <= TF /\ TF + 31 * Z.of_nat k <= 2 ^ 20 - 64
    /\ cellA M (STO + 24) 4 ST /\ 0 <= ST /\ ST + 31 * Z.of_nat k < 2 ^ 20
    /\ cellA M MAP1 8 l2 /\ cellA M (STO + 16) 8 blk
    /\ (forall b, 0 <= b < 2 ^ 20 -> exists v, cellA M (DEP + 4 * b) 4 v /\ 0 <= v <= N)
    /\ dp_nodes M l2 N
    /\ wrA M DEP 4194308 /\ wrA M STO 32 /\ wrA M l2 (2 ^ 20) /\ wrA M blk (2 ^ 23).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma store_ok_agree : forall (k : nat) (M M' : word -> option byte) (w : word),
  U w + Z.of_nat k <= 2 ^ 64 ->
  (forall x : word, U w <= U x < U w + Z.of_nat k -> M' x = M x) ->
  store_ok ASEGS M w k = true -> store_ok ASEGS M' w k = true.
Proof.
  induction k as [|k IH]; intros M M' w Hnw AGw S; [reflexivity|]. cbn [store_ok] in S |- *.
  unfold wview in S |- *. rewrite (AGw w) by lia.
  assert (NEXT : store_ok ASEGS M (w + 1)%bv k = true -> store_ok ASEGS M' (w + 1)%bv k = true).
  { intros S1. destruct k as [|k']; [reflexivity|].
    pose proof (u64_range w). assert (U1 : U (w + 1)%bv = U w + 1) by (apply u_add1; lia).
    apply (IH M M'); [rewrite U1; lia | | exact S1]. intros x Hx. apply AGw. rewrite U1 in Hx. lia. }
  destruct (M w) as [b|].
  - apply NEXT. exact S.
  - destruct (find_segment _ _ _) as [seg|]; [|discriminate]. destruct (seg_writable seg); [|discriminate].
    destruct (segment_byte_at _ _); [|discriminate]. apply NEXT. exact S.
Qed.
Lemma wr_agree : forall (M M' : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 ->
  (forall x : word, a <= U x < a + n -> M' x = M x) -> wrA M a n -> wrA M' a n.
Proof.
  intros M M' a n Ha Han AG W d k Hd Hk. specialize (W d k Hd Hk). destruct k as [|k]; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hk.
  apply (store_ok_agree (S k) M M'); [rewrite art_u_lit by lia; rewrite Nat2Z.inj_succ; lia | | exact W].
  intros x Hx. rewrite art_u_lit in Hx by lia. rewrite Nat2Z.inj_succ in Hx. apply AG. lia.
Qed.

Lemma DInvD_frame : forall l2 blk, art_depot_frame (DInvD l2 blk) (dprivD l2 blk).
Proof.
  intros l2 blk k M M' (N & TF & ST & G1 & G2 & G3 & G4 & G5 & G6 & G7 & CN & RN & BN & CTF & RTF & BTF & CST & RST & BST & CM1 & CBL & BK & ND & W1 & W2 & W3 & W4) AG.
  unfold dprivD in AG. exists N, TF, ST. unfold NID, STO, MAP1, DEP in *.
  zsplit; try assumption.
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CN].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CTF].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CST].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CM1].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CBL].
  - intros b Hb. destruct (BK b Hb) as (v & Cv & Rv). exists v. split; [|exact Rv].
    apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cv].
  - intros id Hid. destruct (ND id Hid) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk.
    split; [exact Rhv|]. split; [|split; [|exact Rlk]].
    + apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Chv].
    + apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Clk].
  - apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W1].
  - apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W2].
  - apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W3].
  - apply (wr_agree M M'); [lia | lia | intros x Hx; apply AG; lia | exact W4].
Qed.

Lemma DPreD_frame : forall blk, art_dpre_frame (DPreD blk).
Proof.
  intros blk M M' trp szt (Hs & Ha & Ht & Ht' & AP & RC) AG. repeat (split; [assumption|]).
  intros i Hi. destruct (RC i Hi) as (bs & R). exists bs.
  rewrite <- R. apply rdn_ext; [rewrite art_u_lit by lia; cbn; lia|]. intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. cbn in Hx. lia.
Qed.

Lemma DPreD_intro : forall blk M trp szt,
  1 <= szt <= 30 -> trp mod 8 = 0 -> 4096 <= trp -> trp + 8 * szt < 2 ^ 64 -> apart trp (8 * szt) blk (2 ^ 23) ->
  (forall i, 0 <= i < szt -> exists w : word, cellA M (trp + 8 * i) 8 (U w)) -> DPreD blk M trp szt.
Proof.
  intros blk M trp szt Hs Ha Ht Ht' AP CW. repeat (split; [assumption|]).
  intros i Hi. destruct (CW i Hi) as [w C]. eexists. exact C.
Qed.

Lemma DRoD_frame : forall M M', DRoD M -> (forall x : word, 0x10000 <= U x < 0x211b08 -> M' x = M x) -> DRoD M'.
Proof.
  intros M M' (C1 & C2 & C3) AG. unfold DRoD.
  repeat split; (apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | assumption]).
Qed.

Lemma DInvD_weaken : forall l2 blk k M, DInvD l2 blk (S k) M -> DInvD l2 blk k M.
Proof.
  intros l2 blk k M (N & TF & ST & H). exists N, TF, ST. rewrite Nat2Z.inj_succ in H. zsplit; try tauto; lia.
Qed.

(* [comment removed for export] *)
Lemma nodp_apart : forall (P : Z -> Prop) a n b m, nodp P a n -> (forall i, b <= i < b + m -> P i) -> 0 < n -> 0 < m -> apart a n b m.
Proof.
  intros P a n b m NP PB Hn Hm. unfold apart. destruct (Z_lt_le_dec b (a + n)) as [L|G]; [|left; lia].
  destruct (Z_lt_le_dec a (b + m)) as [L'|G']; [|right; lia].
  destruct (Z_lt_le_dec a b) as [L''|G''].
  - exfalso. apply (NP b ltac:(lia)). apply PB. lia.
  - exfalso. apply (NP a ltac:(lia)). apply PB. lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma dp_ins_run : forall regs (X rom : word -> option byte) (s v h N l2 : Z),
  getr regs 10 = Z_to_bv 64 v -> getr regs 25 = Z_to_bv 64 v -> getr regs 9 = Z_to_bv 64 DEP -> getr regs 24 = Z_to_bv 64 MAP1 ->
  getr regs 22 = Z_to_bv 64 65535 -> getr regs 19 = Z_to_bv 64 h -> getr regs 2 = Z_to_bv 64 (s - 112) ->
  4096 <= s - 224 -> s < 2 ^ 64 -> 0 <= v <= N -> 0 <= N -> N + 1 < 2 ^ 16 -> 0 <= h < 2 ^ 64 -> 0x696000 <= l2 -> l2 + 2 ^ 20 < 2 ^ 47 ->
  cellA X NID 4 N -> cellA X MAP1 8 l2 -> wokA X NID 4 ->
  exists regs',
    msteps ASEGS (mkst regs (0x9a164 : word) X rom) (mkst regs' (0x99cdc : word) (Wn 4 X NID (N + 1)) rom)
    /\ getr regs' 10 = Z_to_bv 64 (l2 + 16 * (N + 1)) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 104) /\ getr regs' 13 = Z_to_bv 64 h
    /\ getr regs' 1 = (0x9a1ec : word)%bv /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 23 = Z_to_bv 64 (N + 1) /\ getr regs' 9 = Z_to_bv 64 (l2 + 16 * (N + 1))
    /\ getr regs' 21 = Z_to_bv 64 v /\ getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18
    /\ (forall r : reg, r <> 1%bv -> r <> 9%bv -> r <> 21%bv -> r <> 23%bv -> ~ (10 <= U r <= 13) -> getr regs' r = getr regs r).
Proof.
  intros regs X rom s v h N l2 H10 H25 H9 H24 H22 H19 H2 Hs Hs' Hv HN HN' Hh Hl2 Hl2' CN CM WN. unfold NID, MAP1, DEP in *.
  pose proof (Z.div_small (N + 1) (2 ^ 16) ltac:(lia)) as D16.
  eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
  - zstep F_99d4c D_99d4c.                                                       (* [comment removed for export] *)
    zbtk F_99d50 D_99d50.                                                        (* [comment removed for export] *)
    stepn F_99d7c D_99d7c.                                                       (* [comment removed for export] *)
    zstep F_99d80 D_99d80.                                                       (* [comment removed for export] *)
    zstep F_99d84 D_99d84.                                                       (* [comment removed for export] *)
    replace (2235160 + 4194304) with 6429464 by lia.
    chain_step; [reflexivity
      | eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 6429464) (Z_to_bv 64 1) (Z_to_bv 64 N));
        [ exact F_99d88 | reflexivity | exact D_99d88 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
        | exact CN | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WN ]
      | ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.                (* [comment removed for export] *)
    change (wbytes ?M0 (Z_to_bv 64 6429464) (word_to_le_bytes 4 (Z_to_bv 64 (N + 1)))) with (Wn 4 M0 6429464 (N + 1)).
    stepn F_99d8c D_99d8c. rwH. unfold v_addiw. rewrite art_u_lit by lia.
    replace (bv_swrap 32 (N + 1)) with (N + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).   (* [comment removed for export] *)
    zstep F_99d90 D_99d90.                                                       (* [comment removed for export] *)
    stepn F_99d94 D_99d94. rwH. rewrite (art_zb_srli_exact ((N + 1) * 2 ^ 32) 32 (N + 1)) by lia.   (* [comment removed for export] *)
    stepb_ft F_99d98 D_99d98 ltac:(zconds).                                      (* [comment removed for export] *)
    zstep F_99d9c D_99d9c.                                                       (* [comment removed for export] *)
    stepn F_99da0 D_99da0. rwH. rewrite art_zb_srli by lia. rewrite D16.         (* [comment removed for export] *)
    zstep F_99da4 D_99da4.                                                       (* [comment removed for export] *)
    zstep F_99da8 D_99da8.                                                       (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?Y _) _ => assert (CM' : cellA Y 6429480 8 l2) by zcell end.
    zld F_99dac D_99dac 6429480 CM'.                                             (* [comment removed for export] *)
    zbft F_99db0 D_99db0.                                                        (* [comment removed for export] *)
    stepn F_99db4 D_99db4. rwH. rewrite art_zb_and by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    rewrite (Z.mod_small (N + 1) (2 ^ 16)) by lia.                               (* [comment removed for export] *)
    zstep F_99db8 D_99db8.                                                       (* [comment removed for export] *)
    zstep F_99dbc D_99dbc.                                                       (* [comment removed for export] *)
    zstep F_99dc0 D_99dc0.                                                       (* [comment removed for export] *)
    zstep F_99dc4 D_99dc4.                                                       (* [comment removed for export] *)
    zstep F_99dc8 D_99dc8.                                                       (* [comment removed for export] *)
    zstep F_99dcc D_99dcc.                                                       (* [comment removed for export] *)
    stepn F_99dd0 D_99dd0.                                                       (* [comment removed for export] *)
    replace (l2 + (N + 1) * 2 ^ 4) with (l2 + 16 * (N + 1)) by lia. replace (s - 112 + 8) with (s - 104) by lia.
    apply mst_refl.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - gres. apply bv_eq. vm_compute. reflexivity.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - kept_solve.
  - intros r N1 N9 N21 N23 NR.
    destruct (decide (r = 10%bv)) as [->|N10]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 11%bv)) as [->|N11]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 12%bv)) as [->|N12]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    destruct (decide (r = 13%bv)) as [->|N13]; [exfalso; apply NR; clear; vm_compute; split; discriminate|].
    kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma dp_tail_run : forall regs (X rom : word -> option byte) (s nd v id adr : Z),
  getr regs 9 = Z_to_bv 64 nd -> getr regs 21 = Z_to_bv 64 v -> getr regs 23 = Z_to_bv 64 id -> getr regs 18 = Z_to_bv 64 adr ->
  getr regs 8 = Z_to_bv 64 0 ->
  0 <= nd -> nd + 16 < 2 ^ 64 -> 0 <= adr -> adr + 4 < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= id < 2 ^ 64 ->
  wokA X (nd + 8) 4 -> wokA X adr 4 ->
  exists regs',
    msteps ASEGS (mkst regs (0x9a1ec : word) X rom) (mkst regs' (0x9a208 : word) (Wn 4 (Wn 4 X (nd + 8) v) adr id) rom)
    /\ getr regs' 10 = Z_to_bv 64 id /\ (forall r : reg, r <> 10%bv -> getr regs' r = getr regs r).
Proof.
  intros regs X rom s nd v id adr H9 H21 H23 H18 H8 Hn Hn' Ha Ha' Hv Hid W1 W2.
  eexists. split; [|split].
  - zsw F_99dd4 D_99dd4 (nd + 8) v ltac:(exact W1).                               (* [comment removed for export] *)
    stepfence F_99dd8 D_99dd8.                                                   (* [comment removed for export] *)
    zstep F_99ddc D_99ddc.                                                       (* [comment removed for export] *)
    zsw F_99de0 D_99de0 adr id ltac:(apply wok_Wn; exact W2).                       (* [comment removed for export] *)
    zbtk F_99de4 D_99de4.                                                        (* [comment removed for export] *)
    apply mst_refl.
  - kept_solve.
  - intros r N10. kept_solve.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma nrange_lit : forall a b c, (c <? a) || (b <? c) = true -> ~ (a <= c <= b).
Proof. intros a b c H [L1 L2]. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.ltb_lt in H; lia. Qed.
(* [comment removed for export] *)
Ltac nlit := first [ let E := fresh in intros E; discriminate E | apply nrange_lit; vm_compute; reflexivity ].

#[using="Type"] Lemma reg_cases_18_27 : forall r : reg, 18 <= U r <= 27 ->
  r = 18%bv \/ r = 19%bv \/ r = 20%bv \/ r = 21%bv \/ r = 22%bv \/ r = 23%bv \/ r = 24%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv.
Proof.
  intros r Hr.
  assert (E : U r = 18 \/ U r = 19 \/ U r = 20 \/ U r = 21 \/ U r = 22 \/ U r = 23 \/ U r = 24 \/ U r = 25 \/ U r = 26 \/ U r = 27) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]];
  [left|right;left|do 2 right;left|do 3 right;left|do 4 right;left|do 5 right;left|do 6 right;left|do 7 right;left|do 8 right;left|do 9 right];
  apply bv_eq; exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem art_depot_spec_holds : forall l2 blk, art_depot_spec (DInvD l2 blk) (DPreD blk) (dprivD l2 blk) DRoD 224.
Proof.
  intros l2 blk k regs M rom raw sp trp szt H1 Hret H2 H10 H11 HDK Hsp Hsp6 W ND DI DP DR.
  pose proof DI as DI0.
  destruct DI as (N & TF & ST & G1 & G2 & G3 & G4 & G5 & G6 & G7 & CN & RN & BN & CTF & RTF & BTF & CST & RST & BST & CM1 & CBL & BK & NDS & W1 & W2 & W3 & W4).
  rewrite Nat2Z.inj_succ in BN, BTF, BST.
  destruct DP as (Hsz & Hta & Ht4 & Ht' & AT & RC). destruct DR as (Cm & Ck1 & Ck2).
  unfold NID, STO, MAP1, DEP in *.
  assert (Al2 : apart (sp - 224) 224 l2 (2 ^ 20)) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
  assert (Ablk : apart (sp - 224) 224 blk (2 ^ 23)) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
  assert (Ast : apart (sp - 224) 224 0x211b08 4468256) by (apply (nodp_apart _ _ _ _ _ ND); [intros i Hi; unfold dprivD; lia | lia | lia]).
  (* [comment removed for export] *)
  destruct (dp_pro_run regs M rom raw sp trp szt 0xc6a4a7935bd1e995 0x35253c9ade8f4ca8 0x9747b28c9747b28c H2 H10 H11 H1 Hsp6 Hsp Ht4 Ht' Hsz
              ltac:(lia) ltac:(lia) ltac:(lia) Cm Ck1 Ck2 W) as (r1 & h0 & RUN1 & P11 & P14 & P10 & P12 & Rh0 & P13 & P8 & P9 & P2 & K1).
  set (F := dp_frame M sp trp szt raw regs) in RUN1.
  assert (GF : mem_grows M F) by (unfold F, dp_frame; repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl).
  assert (OF : forall x : word, ~ (sp - 104 <= U x < sp) -> F x = M x).
  { intros x Hx. pose proof (u64_range x). unfold F, dp_frame. rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }
  (* [comment removed for export] *)
  assert (RCF : forall j, 0 <= j < szt -> rcell F (trp + 8 * j)) by (intros j Hj; apply (rcell_grows M F _ GF); apply RC; exact Hj).
  replace (Z_to_bv 64 trp : word) with (Z_to_bv 64 (trp + 8 * 0) : word) in P11 by (f_equal; lia).
  destruct (dp_hash_loop (Z.to_nat (szt - 1)) r1 F rom trp szt 0xc6a4a7935bd1e995 0 h0 RCF ltac:(lia) ltac:(lia) ltac:(lia) Rh0 ltac:(lia)
              ltac:(rewrite Z2Nat.id by lia; lia) P11 P14 P10 P12) as (r2 & hN & RUN2 & Q11 & Q12 & RhN & K2).
  (* [comment removed for export] *)
  unfold DEP, MAP1 in *.
  assert (X13 : getr r2 13 = Z_to_bv 64 0) by (rewrite (K2 13%bv) by (intros E; discriminate E); exact P13).
  assert (X10 : getr r2 10 = Z_to_bv 64 0xc6a4a7935bd1e995) by (rewrite (K2 10%bv) by (intros E; discriminate E); exact P10).
  assert (X9 : getr r2 9 = Z_to_bv 64 2235160) by (rewrite (K2 9%bv) by (intros E; discriminate E); exact P9).
  assert (BKF : forall b, 0 <= b < 2 ^ 20 -> exists v, cellA F (2235160 + 4 * b) 4 v /\ 0 <= v <= N).
  { intros b Hb. destruct (BK b Hb) as (v & Cv & Rv). exists v. split; [|exact Rv].
    apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact Cv]. }
  destruct (dp_mid_run r2 F rom hN 0xc6a4a7935bd1e995 N Q12 X13 X10 X9 RhN ltac:(lia) ltac:(lia) BKF)
    as (r3 & h & b & v & RUN3 & Rh & Rb & Cv & Rv & T19 & T18 & T11 & T25 & T24 & T20 & T22 & T23 & T9 & K3).
  (* [comment removed for export] *)
  assert (CM1F : cellA F 6429480 8 l2) by (apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CM1]).
  assert (NDSF : dp_nodes F l2 N).
  { intros id Hid. destruct (NDS id Hid) as (hv & lk & Rhv & Chv & Clk & Rlk). exists hv, lk. split; [exact Rhv|]. split; [|split; [|exact Rlk]].
    - apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Al2; cbn in Hx; lia | lia | cbn; lia | exact Chv].
    - apply (cell_agree M F); [intros x Hx; apply OF; unfold apart in Al2; cbn in Hx; lia | lia | cbn; lia | exact Clk]. }
  assert (Hl16 : l2 mod 16 = 0).
  { apply (proj2 (Z.mod_divide l2 16 ltac:(lia))). apply (Z.divide_trans 16 4096 l2); [exists 256; reflexivity | apply (proj1 (Z.mod_divide l2 4096 ltac:(lia))); exact G3]. }
  destruct (dp_find_loop (Z.to_nat v) r3 F rom l2 N h v ltac:(lia) CM1F ltac:(lia) ltac:(lia) Hl16 ltac:(lia) NDSF ltac:(lia) Rh T11 T19 T24 T22)
    as (r4 & ALT & K4).
  assert (Y2 : getr r4 2 = Z_to_bv 64 (sp - 112)).
  { rewrite (K4 2%bv) by nlit. rewrite (K3 2%bv) by nlit. rewrite (K2 2%bv) by nlit. exact P2. }
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (KF : forall r : reg, r = 3%bv \/ r = 4%bv \/ r = 26%bv \/ r = 27%bv -> getr r4 r = getr regs r).
  { intros r Hr. destruct Hr as [->|[->|[->| ->]]];
      (rewrite (K4 _) by nlit; rewrite (K3 _) by nlit; rewrite (K2 _) by nlit; apply K1; nlit). }
  destruct ALT as [[RUN4 Z11] | [RUN4 (id & Rid & Z10)]].
  2: { (* [comment removed for export] *)
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
    - apply DInvD_weaken. apply (DInvD_frame l2 blk (S k) M F DI0). intros x Dx. apply OF.
      intros Wx. exact (ND (U x) ltac:(lia) Dx). }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (SL : exists r5, msteps ASEGS (mkst r4 (0x9a15c : word) F rom) (mkst r5 (0x9a758 : word) F rom)
            /\ (getr r5 10 = Z_to_bv 64 (2235160 + 4 * b) /\ getr r5 1 = Z_to_bv 64 0x9a164 /\ getr r5 2 = Z_to_bv 64 (sp - 112)
                /\ (forall r : reg, r <> 1%bv -> r <> 10%bv -> getr r5 r = getr r4 r))).
  { assert (Y18 : getr r4 18 = Z_to_bv 64 (2235160 + 4 * b)) by (rewrite (K4 18%bv) by nlit; exact T18).
    eexists. split.
    - zstep F_99d44 D_99d44.                                                     (* [comment removed for export] *)
      stepn F_99d48 D_99d48.                                                     (* [comment removed for export] *)
      apply mst_refl.
    - split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. intros r N1 N10. kept_solve. }
  destruct SL as (r5 & RUN5 & U10 & U1 & U2 & K5).
  (* [comment removed for export] *)
  assert (WFv : wrA F (2235160 + 4 * b) 4) by (apply (wr_grows _ M F _ _ GF); apply (wr_sub _ _ _ _ _ _ W1); lia).
  assert (WFf : wrA F (sp - 112 - 48) 48) by (apply (wr_grows _ M F _ _ GF); apply (wr_sub _ _ _ _ _ _ W); lia).
  assert (AM4 : (2235160 + 4 * b) mod 4 = 0) by (replace (2235160 + 4 * b) with ((558790 + b) * 4) by lia; apply Z_mod_mult).
  assert (U1' : getr r5 1 = (0x9a164 : word)%bv) by (rewrite U1; apply bv_eq; vm_compute; reflexivity).
  destruct (dp_lock_run r5 F rom (0x9a164 : word)%bv (sp - 112) (2235160 + 4 * b) v U2 U10 U1'
              ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AM4 ltac:(lia)
              Cv WFv WFf ltac:(unfold apart in Ast |- *; lia)) as (r6 & RUN6 & V10 & V2 & K6).
  set (LM := dp_lock_mem F (sp - 112) (2235160 + 4 * b) v (0x9a164 : word)%bv (getr r5 8) (getr r5 9) (getr r5 18) (getr r5 19)) in RUN6.
  assert (GLM : mem_grows M LM) by (unfold LM, dp_lock_mem; do 6 (eapply mem_grows_trans; [|apply Wn_grows]); exact GF).
  assert (OLM : forall x : word, ~ (sp - 160 <= U x < sp) -> ~ (2235160 + 4 * b <= U x < 2235160 + 4 * b + 4) -> LM x = M x).
  { intros x Hx1 Hx2. pose proof (u64_range x). unfold LM, dp_lock_mem. rewrite !Wn_outside by (first [lia | cbn; lia]). apply OF. lia. }
  (* [comment removed for export] *)
  #[local] Ltac chase K := rewrite (K _) by nlit.
  assert (V25 : getr r6 25 = Z_to_bv 64 v) by (chase K6; chase K5; chase K4; exact T25).
  assert (V9 : getr r6 9 = Z_to_bv 64 2235160) by (chase K6; chase K5; chase K4; exact T9).
  assert (V24 : getr r6 24 = Z_to_bv 64 6429480) by (chase K6; chase K5; chase K4; exact T24).
  assert (V22 : getr r6 22 = Z_to_bv 64 65535) by (chase K6; chase K5; chase K4; exact T22).
  assert (V19 : getr r6 19 = Z_to_bv 64 h) by (chase K6; chase K5; chase K4; exact T19).
  assert (CNL : cellA LM 6429464 4 N) by (apply (cell_agree M LM); [intros x Hx; apply OLM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CN]).
  assert (CML : cellA LM 6429480 8 l2) by (apply (cell_agree M LM); [intros x Hx; apply OLM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CM1]).
  assert (WNL : wokA LM 6429464 4) by (apply (wr_wok _ _ _ _ (wr_grows _ M LM _ _ GLM W1)); lia).
  pose proof (dp_ins_run r6 LM rom sp v h N l2 V10 V25 V9 V24 V22 V19 V2 ltac:(lia) Hsp ltac:(lia) ltac:(lia) ltac:(lia) Rh G1 G2 CNL CML WNL)
    as (r7 & RUN7 & I10 & I11 & I12 & I13 & I1 & I2 & I23 & I9 & I21 & I8 & I18 & K7).
  set (IM := Wn 4 LM 6429464 (N + 1)) in RUN7.
  assert (GIM : mem_grows M IM) by (unfold IM; eapply mem_grows_trans; [exact GLM | apply Wn_grows]).
  assert (OIM : forall x : word, ~ (sp - 160 <= U x < sp) -> ~ (2235160 + 4 * b <= U x < 2235160 + 4 * b + 4) -> ~ (6429464 <= U x < 6429468) -> IM x = M x).
  { intros x Hx1 Hx2 Hx3. pose proof (u64_range x). unfold IM. rewrite Wn_outside by (first [lia | cbn; lia]). apply OLM; assumption. }
  (* [comment removed for export] *)
  set (nd := l2 + 16 * (N + 1)) in *. assert (End : nd = l2 + 16 * (N + 1)) by reflexivity.
  assert (HND : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0).
  { subst nd. split; [lia|]. split; [lia|]. apply (proj2 (Z.mod_divide _ 16 ltac:(lia))).
    apply Z.divide_add_r; [| exists (N + 1); lia]. apply (proj1 (Z.mod_divide l2 16 ltac:(lia))). exact Hl16. }
  assert (HBLK : 0x696000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0).
  { split; [lia|]. split; [lia|]. apply (proj2 (Z.mod_divide blk 8 ltac:(lia))).
    apply (Z.divide_trans 8 4096 blk); [exists 512; reflexivity | apply (proj1 (Z.mod_divide blk 4096 ltac:(lia))); exact G6]. }
  assert (CI1 : cellA IM (sp - 104) 8 trp) by (unfold IM, LM, dp_lock_mem, F, dp_frame; zcell).
  assert (CI2 : cellA IM (sp - 96) 8 szt) by (unfold IM, LM, dp_lock_mem, F, dp_frame; zcell).
  assert (CI3 : cellA IM 2169608 8 TF) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CTF]).
  assert (CI4 : cellA IM (2169608 + 16) 8 blk) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CBL]).
  assert (CI5 : cellA IM (2169608 + 24) 4 ST) by (apply (cell_agree M IM); [intros x Hx; apply OIM; unfold apart in Ast; cbn in Hx; lia | lia | cbn; lia | exact CST]).
  assert (RCI : forall i, 0 <= i < szt -> rcell IM (trp + 8 * i)) by (intros i Hi; apply (rcell_grows M IM _ GIM); apply RC; exact Hi).
  assert (WI1 : wrA IM (sp - 224) 112) by (apply (wr_grows _ M IM _ _ GIM); apply (wr_sub _ _ _ _ _ _ W); lia).
  assert (WI2 : wrA IM nd 16) by (apply (wr_grows _ M IM _ _ GIM); apply (wr_sub _ _ _ _ _ _ W3); lia).
  assert (WI3 : wrA IM blk (2 ^ 23)) by (apply (wr_grows _ M IM _ _ GIM); exact W4).
  assert (WI4 : wrA IM 2169608 32) by (apply (wr_grows _ M IM _ _ GIM); exact W2).
  pose proof (dp_store_run IM rom sp nd h trp szt TF ST blk l2) as ST8.
  repeat lazymatch type of ST8 with
    | forall rg : bvmap 5 word, _ => fail
    | ?P -> _ => let HP := fresh in assert (HP : P) by (first [eassumption | lia]); specialize (ST8 HP); clear HP
    end.
  fold nd in I10, I9.
  destruct (ST8 r7 I10 I11 I12 I13 I1 I2) as (r8 & SM & RUN8 & S2' & K8 & G8 & O8 & C1 & C2 & C3 & C4 & C5). clear ST8.
  (* [comment removed for export] *)
  assert (J9 : getr r8 9 = Z_to_bv 64 nd) by (rewrite (K8 9%bv) by (cbv; tauto); exact I9).
  assert (J21 : getr r8 21 = Z_to_bv 64 v) by (rewrite (K8 21%bv) by (cbv; tauto); exact I21).
  assert (J23 : getr r8 23 = Z_to_bv 64 (N + 1)) by (rewrite (K8 23%bv) by (cbv; tauto); exact I23).
  assert (J18 : getr r8 18 = Z_to_bv 64 (2235160 + 4 * b)).
  { rewrite (K8 18%bv) by (cbv; tauto). rewrite I18. chase K6. chase K5. chase K4. exact T18. }
  assert (J8 : getr r8 8 = Z_to_bv 64 0).
  { rewrite (K8 8%bv) by (cbv; tauto). rewrite I8. chase K6. chase K5. chase K4. chase K3. chase K2. exact P8. }
  assert (GSM : mem_grows M SM) by (eapply mem_grows_trans; [exact GIM | exact G8]).
  destruct (dp_tail_run r8 SM rom sp nd v (N + 1) (2235160 + 4 * b) J9 J21 J23 J18 J8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply (wr_wok _ _ _ _ (wr_grows _ M SM _ _ GSM W3)); lia) ltac:(apply (wr_wok _ _ _ _ (wr_grows _ M SM _ _ GSM W1)); lia))
    as (r9 & RUN9 & J10 & K9).
  set (TM := Wn 4 (Wn 4 SM (nd + 8) v) (2235160 + 4 * b) (N + 1)) in RUN9.
  (* [comment removed for export] *)
  unfold apart in Ast, Al2, Ablk, G7.
  assert (AG : forall x : word, ~ (sp - 224 <= U x < sp) -> ~ (2235160 + 4 * b <= U x < 2235160 + 4 * b + 4) -> ~ (6429464 <= U x < 6429468) ->
               ~ (nd <= U x < nd + 16) -> ~ (2169608 <= U x < 2169616) -> ~ (2169632 <= U x < 2169636) ->
               ~ (blk + 8 * TF <= U x < blk + 8 * TF + 8 * (szt + 1)) -> TM x = M x).
  { intros x X1 X2 X3 X4 X5 X6 X7. pose proof (u64_range x). unfold TM. rewrite !Wn_outside by (first [lia | cbn; lia]).
    rewrite (O8 x) by (unfold dp_store_out, STO; repeat split; lia). apply OIM; lia. }
  (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    assert (KALL : forall r : reg, r = 3%bv \/ r = 4%bv \/ r = 26%bv \/ r = 27%bv -> getr r10 r = getr regs r).
    { intros r Hr. rewrite <- (KF r Hr). destruct Hr as [->|[->|[->| ->]]];
        (chase K10; chase K9; rewrite (K8 _) by (cbv; tauto); chase K7; chase K6; chase K5; reflexivity). }
    intros r Hk. unfold art_depot_kept in Hk.
    destruct Hk as [->|[->|[->|[->|[->|Hk]]]]]; [rewrite E2, H2; reflexivity | apply KALL; tauto | apply KALL; tauto | exact E8 | exact E9 |].
    destruct (reg_cases_18_27 r Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; try assumption; (apply KALL; tauto).
  - unfold TM. do 2 (eapply mem_grows_trans; [|apply Wn_grows]). exact GSM.
  - intros x NDx NWx. apply AG; try lia; intros BAD; apply NDx; unfold dprivD; lia.
  - (* [comment removed for export] *)
    exists (N + 1), (TF + szt + 1), (ST + szt + 1). unfold NID, STO, MAP1, DEP.
    assert (WT : forall a n, wrA M a n -> wrA TM a n).
    { intros a n Wa. unfold TM. apply wr_Wn. apply wr_Wn. apply (wr_grows _ M SM _ _ GSM). exact Wa. }
    zsplit; try assumption; try lia.
    + (* [comment removed for export] *) unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]).
      apply (cell_agree IM SM); [intros x Hx; apply O8; unfold dp_store_out, STO; cbn in Hx; repeat split; lia | lia | cbn; lia |].
      unfold IM. apply cell_Wn_hit; cbn; lia.
    + (* [comment removed for export] *) unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]).
      replace (TF + szt + 1) with (TF + szt + 1) by lia. exact C1.
    + (* [comment removed for export] *) unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C2.
    + (* [comment removed for export] *) apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact CM1].
    + (* [comment removed for export] *) unfold TM. do 2 (apply cell_Wn_other; [lia | cbn; lia | lia | cbn; lia | unfold apart; cbn; lia |]). exact C3.
    + (* [comment removed for export] *) intros b' Hb'. destruct (Z.eq_dec b' b) as [->|NE].
      * exists (N + 1). split; [|lia]. unfold TM. apply cell_Wn_hit; cbn; lia.
      * destruct (BK b' Hb') as (v' & Cv' & Rv'). exists v'. split; [|lia].
        apply (cell_agree M TM); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cv'].
    + (* [comment removed for export] *) intros id Hid. destruct (Z.eq_dec id (N + 1)) as [->|NE].
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
End FPX.
