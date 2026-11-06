(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMuslStrLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanTls_code VAsanIcStrcmp_code VAsanMemsetWalk VAsanTlsWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Abbreviation B0 := (Z_to_bv 8 0).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_64ae8 : v_addi (0x4483c : word) 4 = Z_to_bv 64 0x44840. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_64bf0 : v_addi (0x44944 : word) 4 = Z_to_bv 64 0x44948. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_64de0 : v_addi (0x44b34 : word) 4 = (0x44b38 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_64ec0 : v_addi (0x44c14 : word) 4 = (0x44c18 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_64de4 : ret_ok (0x44b38 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_64ec4 : ret_ok (0x44c18 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_64ae8 : v_jalr (Z_to_bv 64 0x44840) 0 = (0x44840 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_64bf0 : v_jalr (Z_to_bv 64 0x44948) 0 = (0x44948 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Definition ISC_FRAME : Z := 2264.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition isc_cells (m : word -> option byte) : Prop :=
  cells m
  /\ rdn SEGS m (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xaae70 0x145128                                     (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0x145222) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0x14521d) 1 = Some [Z_to_bv 8 0].     (* [comment removed for export] *)

(* [comment removed for export] *)
Record shfacts (mem : word -> option byte) (x K usp : Z) : Prop := {
  sf_zg   : forall g, (x / 8 <= g < (x + K) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  sf_last : exists b1 : byte, mem (Z_to_bv 64 (SB + (x + K) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((x + K) mod 8 < bv_unsigned b1 < 8)%Z);
  sf_words : forall a, ((SB + x / 8) / 8 * 8 <= a)%Z -> (a <= (SB + (x + K) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
               exists w : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w);
  sf_shd  : (SB + (x + K) / 8 + 8 < usp - ISC_FRAME)%Z;
  sf_rng  : (x + K + 1 <= kLowEnd)%Z \/ (kHighBeg <= x /\ x + K + 1 <= kHighEnd)%Z;
  sf_sap  : (usp <= x \/ x + K + 1 <= usp - ISC_FRAME)%Z
}.

(* [comment removed for export] *)
Record iscH (mem : word -> option byte) (a b usp : Z) (bufa bufb : list byte) (K : Z) : Prop := {
  ic_bufa : rdn SEGS mem (Z_to_bv 64 a) (length bufa) = Some bufa;
  ic_bufb : rdn SEGS mem (Z_to_bv 64 b) (length bufb) = Some bufb;
  ic_lena : (K + 1 <= Z.of_nat (length bufa))%Z;
  ic_lenb : (K + 1 <= Z.of_nat (length bufb))%Z;
  ic_nwa  : (a + Z.of_nat (length bufa) < 2 ^ 64)%Z;
  ic_nwb  : (b + Z.of_nat (length bufb) < 2 ^ 64)%Z;
  ic_a    : (0 <= a)%Z;
  ic_b    : (0 <= b)%Z;
  ic_K    : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z;
  ic_zero_K : bv_unsigned (nth (Z.to_nat K) bufb B0) = 0%Z;
  ic_sp   : (SB + ISC_FRAME + 16 <= usp < 2 ^ 64)%Z;
  ic_sha  : shfacts mem a K usp;
  ic_shb  : shfacts mem b K usp;
  ic_stk  : forall x, (usp - ISC_FRAME <= x < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 x) 1 = true;
  ic_cel  : isc_cells mem
}.

(* [comment removed for export] *)
Definition isc_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.
(* [comment removed for export] *)
Definition ekeep (r : reg) : bool :=
  (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21
   || bv_eqb r 22 || bv_eqb r 23 || bv_eqb r 24 || bv_eqb r 25 || bv_eqb r 26 || bv_eqb r 27)%bool.

(* [comment removed for export] *)
Definition cmpx (ca cb : Z) : Z := (if ca <? cb then 2 ^ 64 - 1 else if cb <? ca then 1 else 0)%Z.

Section ISC.
  Variables (mem rom : word -> option byte) (a b usp : Z) (bufa bufb : list byte) (K : Z).
  Hypothesis H : iscH mem a b usp bufa bufb K.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 a.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 b.

  #[local] Notation BA j := (nth (Z.to_nat j) bufa B0).
  #[local] Notation BB j := (nth (Z.to_nat j) bufb B0).

  #[using="mem a b bufa bufb K H"] Lemma Hsp : (0x7fff8000 + 2280 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (ic_sp _ _ _ _ _ _ _ H). unfold ISC_FRAME, SB in *. lia. Qed.
  #[using="mem b usp bufa bufb H"] Lemma Ha64 : (0 <= a)%Z /\ (a + K + 1 < 2 ^ 64)%Z.
  Proof. pose proof (ic_nwa _ _ _ _ _ _ _ H). pose proof (ic_a _ _ _ _ _ _ _ H). pose proof (ic_lena _ _ _ _ _ _ _ H). lia. Qed.
  #[using="mem a usp bufa bufb H"] Lemma Hb64 : (0 <= b)%Z /\ (b + K + 1 < 2 ^ 64)%Z.
  Proof. pose proof (ic_nwb _ _ _ _ _ _ _ H). pose proof (ic_b _ _ _ _ _ _ _ H). pose proof (ic_lenb _ _ _ _ _ _ _ H). lia. Qed.
  #[using="mem a b usp bufa bufb H"] Lemma HK64 : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z.
  Proof. exact (ic_K _ _ _ _ _ _ _ H). Qed.

  (* [comment removed for export] *)
  #[using="b bufb H"] Lemma rd_a : forall m j, (forall x : word, (bv_unsigned x < usp - ISC_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x) ->
    (0 <= j <= K)%Z -> rdn SEGS m (Z_to_bv 64 (a + j)) 1 = Some [BA j].
  Proof.
    intros m j AG Hj. pose proof Ha64. pose proof Hsp. pose proof (ic_lena _ _ _ _ _ _ _ H). pose proof (ic_nwa _ _ _ _ _ _ _ H).
    pose proof (sf_sap _ _ _ _ (ic_sha _ _ _ _ _ _ _ H)) as AP. unfold ISC_FRAME in *.
    pose proof (VAsanMuslStrLib.rdn_nth1 SEGS mem (Z_to_bv 64 a) (length bufa) bufa (Z.to_nat j) (ic_bufa _ _ _ _ _ _ _ H) ltac:(lia)) as R.
    unfold at_ in R. rewrite zbv_u, Z2Nat.id in R by lia.
    rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx. apply AG. lia.
  Qed.
  #[using="a bufa H"] Lemma rd_b : forall m j, (forall x : word, (bv_unsigned x < usp - ISC_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x) ->
    (0 <= j <= K)%Z -> rdn SEGS m (Z_to_bv 64 (b + j)) 1 = Some [BB j].
  Proof.
    intros m j AG Hj. pose proof Hb64. pose proof Hsp. pose proof (ic_lenb _ _ _ _ _ _ _ H). pose proof (ic_nwb _ _ _ _ _ _ _ H).
    pose proof (sf_sap _ _ _ _ (ic_shb _ _ _ _ _ _ _ H)) as AP. unfold ISC_FRAME in *.
    pose proof (VAsanMuslStrLib.rdn_nth1 SEGS mem (Z_to_bv 64 b) (length bufb) bufb (Z.to_nat j) (ic_bufb _ _ _ _ _ _ _ H) ltac:(lia)) as R.
    unfold at_ in R. rewrite zbv_u, Z2Nat.id in R by lia.
    rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx. apply AG. lia.
  Qed.

  (* [comment removed for export] *)
  Definition p13 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 104%Z (getr regs0 27) (w 96%Z (getr regs0 26) (w 88%Z (getr regs0 25) (w 80%Z (getr regs0 24) (w 72%Z (getr regs0 23)
      (w 64%Z (getr regs0 22) (w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
      (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem)))))))))))).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.
  Ltac adr c := match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with c by lia end.

  (* [comment removed for export] *)
  Definition sfr (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - ISC_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x)
    /\ (forall x : word, (usp - 104 <= bv_unsigned x < usp)%Z -> m x = p13 x)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true)
    /\ (forall x, mem x <> None -> m x <> None).

  #[using="a b bufa bufb K H"] Lemma p13_out : forall x : word, (bv_unsigned x < usp - 104 \/ usp <= bv_unsigned x)%Z -> p13 x = mem x.
  Proof.
    intros x [Hx|Hx]; unfold p13; pose proof Hsp.
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  #[using="a b bufa bufb K H"] Lemma sfr_p13 : sfr p13.
  Proof.
    split; [|split; [intros; reflexivity|split]].
    - intros x Hx. apply p13_out. unfold ISC_FRAME in Hx. lia.
    - intros x Hx. unfold p13. repeat apply store_ok1_wbytes. exact Hx.
    - intros x Hx. unfold p13. repeat apply wbytes_keep. exact Hx.
  Qed.
  #[using="a b bufa bufb K H"] Lemma sfr_w8 : forall m (x : Z) (v : word), sfr m -> (usp - ISC_FRAME <= x)%Z -> (x + 8 <= usp - 104)%Z ->
    sfr (wbytes m (Z_to_bv 64 x) (word_to_le_bytes 8 v)).
  Proof.
    intros m x v (F1 & F2 & F3 & F4) Hx1 Hx2. pose proof Hsp. unfold ISC_FRAME in *. split; [|split; [|split]].
    - intros y Hy. rewrite <- (F1 y Hy). unfold ISC_FRAME in Hy. destruct Hy as [Hy|Hy].
      + apply wbytes_below; len8; rewrite ?zbv_u by lia; lia.
      + apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros y Hy. rewrite <- (F2 y Hy). apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros y Hy. apply store_ok1_wbytes. apply F3. exact Hy.
    - intros y Hy. apply wbytes_keep. apply F4. exact Hy.
  Qed.
  #[using="a b bufa bufb K H"] Lemma sfr_rp : forall m (rra s0 s1 s2 s3 s4 s5 : word), sfr m -> sfr (rp_frame m (usp - 2192) rra s0 s1 s2 s3 s4 s5).
  Proof. intros. unfold rp_frame. repeat (apply sfr_w8; [|unfold ISC_FRAME; lia|lia]). assumption. Qed.
  #[using="Type"] Lemma sfr_below : forall m (x : word), sfr m -> (bv_unsigned x < usp - ISC_FRAME)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. exact (F1 x (or_introl Hx)). Qed.
  #[using="Type"] Lemma sfr_out : forall m, sfr m -> forall x : word, (bv_unsigned x < usp - ISC_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x.
  Proof. intros m (F1 & _). exact F1. Qed.
  #[using="a b bufa bufb K H"] Lemma rdn_sfr_below : forall m (x : Z) k, sfr m -> (0 <= x)%Z -> (x + Z.of_nat k <= usp - ISC_FRAME)%Z ->
    rdn SEGS m (Z_to_bv 64 x) k = rdn SEGS mem (Z_to_bv 64 x) k.
  Proof.
    intros m x k F Hx Hk. pose proof Hsp. unfold ISC_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros y Hy. rewrite zbv_u in Hy by lia. apply (sfr_below m y F). unfold ISC_FRAME. lia.
  Qed.
  #[using="a b bufa bufb K H"] Lemma cells_sfr : forall m, sfr m -> isc_cells m.
  Proof.
    intros m F. pose proof (ic_cel _ _ _ _ _ _ _ H) as (C & C1 & C2 & C3 & C4). pose proof Hsp. pose proof SB_val. unfold ISC_FRAME in *.
    unfold isc_cells, cells, cell in *. rewrite !(rdn_sfr_below m) by (first [exact F | cbn; unfold ISC_FRAME; lia]).
    split; [exact C|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|exact C4].
  Qed.
  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp; unfold p13;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
  #[using="a b bufa bufb K H"] Lemma rd_ra : rdn SEGS p13 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).               Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s0 : rdn SEGS p13 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)).   Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s1 : rdn SEGS p13 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)).   Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s2 : rdn SEGS p13 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s3 : rdn SEGS p13 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s4 : rdn SEGS p13 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s5 : rdn SEGS p13 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s6 : rdn SEGS p13 (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 (getr regs0 22)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s7 : rdn SEGS p13 (Z_to_bv 64 (usp - 72)) 8 = Some (word_to_le_bytes 8 (getr regs0 23)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s8 : rdn SEGS p13 (Z_to_bv 64 (usp - 80)) 8 = Some (word_to_le_bytes 8 (getr regs0 24)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s9 : rdn SEGS p13 (Z_to_bv 64 (usp - 88)) 8 = Some (word_to_le_bytes 8 (getr regs0 25)).  Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s10 : rdn SEGS p13 (Z_to_bv 64 (usp - 96)) 8 = Some (word_to_le_bytes 8 (getr regs0 26)). Proof. rd_slot. Qed.
  #[using="a b bufa bufb K H"] Lemma rd_s11 : rdn SEGS p13 (Z_to_bv 64 (usp - 104)) 8 = Some (word_to_le_bytes 8 (getr regs0 27)). Proof. rd_slot. Qed.

  #[using="a b bufa bufb K H"] Lemma stk8 : forall m x, sfr m -> (usp - ISC_FRAME <= x)%Z -> (x + 8 <= usp)%Z -> store_ok SEGS m (Z_to_bv 64 x) 8 = true.
  Proof.
    intros m x (_ & _ & F3 & _) H1 H2. unfold ISC_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F3. apply (ic_stk _ _ _ _ _ _ _ H). unfold ISC_FRAME. lia.
  Qed.

  (* [comment removed for export] *)
  Definition p15 : word -> option byte :=
    wbytes (wbytes p13 (Z_to_bv 64 (usp - 2200)) (word_to_le_bytes 8 (Z_to_bv 64 0x44840)))
           (Z_to_bv 64 (usp - 2208)) (word_to_le_bytes 8 (Z_to_bv 64 usp)).
  #[using="a b bufa bufb K H"] Lemma sfr_p15 : sfr p15.
  Proof. unfold p15. apply sfr_w8; [apply sfr_w8; [exact sfr_p13|unfold ISC_FRAME; lia|lia]|unfold ISC_FRAME; lia|lia]. Qed.

  Ltac msd F D x v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 x) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                 | apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold p15, p13; repeat apply store_ok1_wbytes;
                   apply (ic_stk _ _ _ _ _ _ _ H); unfold ISC_FRAME; lia ]).

  (* [comment removed for export] *)
  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r : reg, isc_clob r = false -> ekeep r = false -> getr regs r = getr regs0 r.
  Ltac keep_tac Hr He := repeat (rewrite getr_other by (intros ->; cbn in Hr, He; first [discriminate Hr | discriminate He])).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="bufa bufb K H H01 H02 H010 H011"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x447f0 : word) mem rom) (mkst regs (0x44844 : word) p15 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 2192) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 9 = Z_to_bv 64 b
      /\ getr regs 18 = Z_to_bv 64 a /\ getr regs 19 = ra /\ keep regs.
  Proof.
    pose proof Hsp. pose proof Ha64. pose proof Hb64. pose proof HK64.
    assert (AI : rdn SEGS p15 (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_sfr p15 sfr_p15))).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_447f0 eq_refl D_447f0)). rewrite H02. zn.
      msd F_447f4 D_447f4 (usp - 8)%Z ra H02.
      msd F_447f8 D_447f8 (usp - 16)%Z (getr regs0 8) H02.
      msd F_447fc D_447fc (usp - 24)%Z (getr regs0 9) H02.
      msd F_44800 D_44800 (usp - 32)%Z (getr regs0 18) H02.
      msd F_44804 D_44804 (usp - 40)%Z (getr regs0 19) H02.
      msd F_44808 D_44808 (usp - 48)%Z (getr regs0 20) H02.
      msd F_4480c D_4480c (usp - 56)%Z (getr regs0 21) H02.
      msd F_44810 D_44810 (usp - 64)%Z (getr regs0 22) H02.
      msd F_44814 D_44814 (usp - 72)%Z (getr regs0 23) H02.
      msd F_44818 D_44818 (usp - 80)%Z (getr regs0 24) H02.
      msd F_4481c D_4481c (usp - 88)%Z (getr regs0 25) H02.
      msd F_44820 D_44820 (usp - 96)%Z (getr regs0 26) H02.
      msd F_44824 D_44824 (usp - 104)%Z (getr regs0 27) H02.
      change (wbytes _ _ _) with p13.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44828 eq_refl D_44828)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4482c eq_refl D_4482c)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44830 eq_refl D_44830)). gr. rewrite H01.
      replace (v_addi ra 0) with ra by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44834 eq_refl D_44834)). gr. rewrite H011. zn. rewrite ?Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44838 eq_refl D_44838)). gr. rewrite H010. zn. rewrite ?Z.add_0_r.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_4483c eq_refl D_4483c)). rewrite lit_64ae8.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be40 eq_refl D_5be40)). gr. zn.
      msd F_5be44 D_5be44 (usp - 2200)%Z (Z_to_bv 64 0x44840) H02.
      msd F_5be48 D_5be48 (usp - 2208)%Z (Z_to_bv 64 usp) H02.
      change (wbytes _ _ _) with p15.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3e4c) F_5be4c eq_refl D_5be4c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be50 eq_refl D_5be50)). gr. zn.
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5be54 eq_refl D_5be54);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI).
      rewrite v_lb_1.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be58 eq_refl D_5be58)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5be5c eq_refl D_5be5c)).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5be60 eq_refl D_5be60); gr; br_eq).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0x44840) F_5be64 eq_refl D_5be64);
                   [ gr; imm_norm; zn; adr (usp - 2200)%Z;
                     unfold p15; rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia| len8; rewrite !zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia]
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 usp) F_5be68 eq_refl D_5be68);
                   [ gr; imm_norm; zn; adr (usp - 2208)%Z;
                     unfold p15; apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be6c eq_refl D_5be6c)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x44840) F_5be70 eq_refl D_5be70); gr; reflexivity |].
      imm_norm. rewrite ret_64ae8. replace (usp - 2192 + -16 + 16)%Z with (usp - 2192)%Z by lia.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44840 eq_refl D_44840); gr; rewrite ?getr_zero; br_eq).
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr He. keep_tac Hr He. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition base (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (usp - 2192) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 9 = Z_to_bv 64 b
    /\ getr regs 18 = Z_to_bv 64 a /\ getr regs 19 = ra /\ keep regs.
  (* [comment removed for export] *)
  Ltac base_tac B :=
    let HB := fresh in pose proof B as HB;
    destruct HB as (?B2 & ?B8 & ?B9 & ?B18 & ?B19 & ?BK);
    repeat split;
    [ gr; exact B2 | gr; exact B8 | gr; exact B9 | gr; exact B18 | gr; exact B19
    | intros r Hr He; keep_tac Hr He; apply BK; assumption ].

  #[using="Type"] Lemma byte_range (x : byte) : (0 <= bv_unsigned x < 256)%Z.
  Proof. pose proof (bv_unsigned_in_range 8 x) as X. change (bv_modulus 8) with 256%Z in X. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="bufa bufb K H"] Lemma blk_L0 : forall regs, base regs ->
    exists regs',
      msteps SEGS (mkst regs (0x44844 : word) p15 rom) (mkst regs' (0x44850 : word) p15 rom)
      /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 27 = Z_to_bv 64 (usp - 2176) /\ base regs'.
  Proof.
    intros regs B. pose proof Hsp. pose proof B as (B2 & B8 & B9 & B18 & B19 & BK).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44844 eq_refl D_44844)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44848 eq_refl D_44848)). gr. rewrite B8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4484c eq_refl D_4484c)). gr. zn.
      apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; apply (f_equal (Z_to_bv 64)); lia|]. base_tac B.
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma loop_body : forall regs (i : Z) m, sfr m -> base regs ->
    getr regs 20 = Z_to_bv 64 i -> (0 <= i <= K)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x44850 : word) m rom) (mkst regs' (0x44864 : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 (i + 1) /\ getr regs' 25 = Z_to_bv 64 (bv_unsigned (BA i)) /\ getr regs' 26 = Z_to_bv 64 (bv_unsigned (BB i))
      /\ getr regs' 27 = getr regs 27 /\ base regs'.
  Proof.
    intros regs i m F B H20 Hi. pose proof Hsp. pose proof Ha64. pose proof Hb64. pose proof HK64. pose proof B as (B2 & B8 & B9 & B18 & B19 & BK).
    pose proof (rd_a m i (sfr_out m F) Hi) as RA. pose proof (rd_b m i (sfr_out m F) Hi) as RB.
    eexists. split.
    - mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_44850 eq_refl D_44850)). gr. rewrite B18, H20, v_add_zbv by lia.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (BA i) F_44854 eq_refl D_44854); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact RA).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_44858 eq_refl D_44858)). gr. rewrite B9, H20, v_add_zbv by lia.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (BB i) F_4485c eq_refl D_4485c); gr; imm_norm; zn; rewrite ?Z.add_0_r; exact RB).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44860 eq_refl D_44860)). gr. rewrite H20. zn.
      apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B.
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma isc_loop : forall (n : nat) regs (i : Z) m, sfr m -> base regs ->
    getr regs 20 = Z_to_bv 64 i -> (0 <= i <= K)%Z -> Z.of_nat n = (K - i)%Z ->
    (forall j, (0 <= j < i)%Z -> bv_unsigned (BA j) = bv_unsigned (BB j) /\ bv_unsigned (BA j) <> 0%Z) ->
    exists regs' (I : Z),
      msteps SEGS (mkst regs (0x44850 : word) m rom) (mkst regs' (0x4486c : word) m rom)
      /\ (i <= I <= K)%Z
      /\ getr regs' 20 = Z_to_bv 64 (I + 1) /\ getr regs' 25 = Z_to_bv 64 (bv_unsigned (BA I)) /\ getr regs' 26 = Z_to_bv 64 (bv_unsigned (BB I))
      /\ (bv_unsigned (BA I) = 0%Z \/ bv_unsigned (BA I) <> bv_unsigned (BB I))
      /\ (forall j, (0 <= j < I)%Z -> bv_unsigned (BA j) = bv_unsigned (BB j) /\ bv_unsigned (BA j) <> 0%Z)
      /\ getr regs' 27 = getr regs 27 /\ base regs'.
  Proof.
    pose proof Hsp as HU. pose proof HK64. pose proof (ic_zero_K _ _ _ _ _ _ _ H) as ZK.
    induction n as [|n IH]; intros regs i m F B H20 Hi Hn INV.
    - (* [comment removed for export] *)
      assert (EK : i = K) by lia. subst i.
      destruct (loop_body regs K m F B H20 Hi) as (r1 & M1 & R20 & R25 & R26 & R27 & B1).
      pose proof (byte_range (BA K)). pose proof (byte_range (BB K)).
      exists r1, K. split.
      + eapply msteps_trans; [exact M1|].
        destruct (Z.eq_dec (bv_unsigned (BA K)) 0) as [Z0|NZ].
        * mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44864 eq_refl D_44864); gr; rewrite ?R25, ?getr_zero; br_eq).
          apply mst_refl.
        * mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44864 eq_refl D_44864); gr; rewrite ?R25, ?getr_zero; br_eq).
          mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44868 eq_refl D_44868); gr; rewrite ?R25, ?R26; br_eq).
          apply mst_refl.
      + split; [lia|]. split; [exact R20|]. split; [exact R25|]. split; [exact R26|].
        split; [destruct (Z.eq_dec (bv_unsigned (BA K)) 0); [left; assumption|right; lia]|].
        split; [exact INV|]. split; [exact R27|exact B1].
    - destruct (loop_body regs i m F B H20 Hi) as (r1 & M1 & R20 & R25 & R26 & R27 & B1).
      pose proof (byte_range (BA i)). pose proof (byte_range (BB i)).
      destruct (Z.eq_dec (bv_unsigned (BA i)) 0) as [Z0|NZ].
      + exists r1, i. split.
        * eapply msteps_trans; [exact M1|].
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44864 eq_refl D_44864); gr; rewrite ?R25, ?getr_zero; br_eq).
          apply mst_refl.
        * split; [lia|]. split; [exact R20|]. split; [exact R25|]. split; [exact R26|]. split; [left; exact Z0|].
          split; [exact INV|]. split; [exact R27|exact B1].
      + destruct (Z.eq_dec (bv_unsigned (BA i)) (bv_unsigned (BB i))) as [EQ|NE].
        * (* [comment removed for export] *)
          assert (LT : (i < K)%Z) by (destruct (Z.eq_dec i K) as [->|]; [exfalso; apply NZ; rewrite EQ; exact ZK|lia]).
          destruct (IH r1 (i + 1)%Z m F B1 R20 ltac:(lia) ltac:(lia)) as (r2 & I & M2 & HI & S20 & S25 & S26 & EX & INV2 & S27 & B2').
          { intros j Hj. destruct (Z.eq_dec j i) as [->|]; [split; [exact EQ|exact NZ]|]. apply INV. lia. }
          exists r2, I. split.
          -- eapply msteps_trans; [exact M1|].
             mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44864 eq_refl D_44864); gr; rewrite ?R25, ?getr_zero; br_eq).
             mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44868 eq_refl D_44868); gr; rewrite ?R25, ?R26; br_eq).
             exact M2.
          -- split; [lia|]. split; [exact S20|]. split; [exact S25|]. split; [exact S26|]. split; [exact EX|].
             split; [exact INV2|]. split; [rewrite S27; exact R27|exact B2'].
        * exists r1, i. split.
          -- eapply msteps_trans; [exact M1|].
             mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44864 eq_refl D_44864); gr; rewrite ?R25, ?getr_zero; br_eq).
             mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44868 eq_refl D_44868); gr; rewrite ?R25, ?R26; br_eq).
             apply mst_refl.
          -- split; [lia|]. split; [exact R20|]. split; [exact R25|]. split; [exact R26|]. split; [right; exact NE|].
             split; [exact INV|]. split; [exact R27|exact B1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition base2 (regs : bvmap 5 word) (I : Z) : Prop :=
    base regs /\ getr regs 20 = Z_to_bv 64 (I + 1) /\ getr regs 22 = Z_to_bv 64 (I + 1) /\ getr regs 24 = Z_to_bv 64 0x145128
    /\ getr regs 25 = Z_to_bv 64 (bv_unsigned (BA I)) /\ getr regs 26 = Z_to_bv 64 (bv_unsigned (BB I)).
  Ltac base2_tac B :=
    let HB := fresh in pose proof B as HB;
    destruct HB as ((?B2 & ?B8 & ?B9 & ?B18 & ?B19 & ?BK) & ?B20 & ?B22 & ?B24 & ?B25 & ?B26);
    repeat split;
    [ gr; exact B2 | gr; exact B8 | gr; exact B9 | gr; exact B18 | gr; exact B19
    | intros r Hr He; keep_tac Hr He; apply BK; assumption
    | gr; exact B20 | gr; exact B22 | gr; exact B24 | gr; exact B25 | gr; exact B26 ].

  #[using="H"] Lemma blk_F : forall regs (I : Z) m, sfr m -> base regs -> (0 <= I <= K)%Z ->
    getr regs 20 = Z_to_bv 64 (I + 1) -> getr regs 25 = Z_to_bv 64 (bv_unsigned (BA I)) -> getr regs 26 = Z_to_bv 64 (bv_unsigned (BB I)) ->
    exists regs',
      msteps SEGS (mkst regs (0x4486c : word) m rom) (mkst regs' (0x44898 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 I /\ getr regs' 21 = Z_to_bv 64 I /\ base2 regs' I.
  Proof.
    intros regs I m F B HI H20 H25 H26. pose proof Hsp. pose proof Ha64. pose proof HK64. pose proof B as (B2 & B8 & B9 & B18 & B19 & BK).
    pose proof (cells_sfr m F) as (_ & _ & G1 & IS & SS).
    eexists. split.
    - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaa86c) F_4486c eq_refl D_4486c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_44870 D_44870 0x145128%Z G1 B8.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_44874 eq_refl D_44874);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; first [exact IS | adr 0x145222%Z; exact IS]).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_44878 eq_refl D_44878); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_4487c eq_refl D_4487c);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; first [exact SS | adr 0x14521d%Z; exact SS]).
      change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44880 eq_refl D_44880)). gr. rewrite H20. zn.
      replace (I + 1 + -1)%Z with I by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44884 eq_refl D_44884)). gr. rewrite H20. zn. rewrite ?Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44888 eq_refl D_44888)). gr. zn. rewrite ?Z.add_0_r.
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_4488c eq_refl D_4488c); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44890 eq_refl D_44890)). gr. rewrite B18. rewrite v_not_zbv by lia.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_44894 eq_refl D_44894); gr; br_lt).
      apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; reflexivity|].
      split; [base_tac B|]. gr. repeat split; try assumption; try reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section SH.
    Variable x : Z.
    Hypothesis SHx : shfacts mem x K usp.
    Hypothesis Hx64 : (0 <= x)%Z /\ (x + K + 1 < 2 ^ 64)%Z.

    #[using="a b usp bufa bufb H SHx Hx64"] Lemma last_I : forall I, (0 <= I <= K)%Z ->
      exists b1 : byte, mem (Z_to_bv 64 (SB + (x + I) / 8)) = Some b1
                        /\ (bv_unsigned b1 = 0%Z \/ ((x + I) mod 8 < bv_unsigned b1 < 8)%Z).
    Proof.
      intros I HI. pose proof Hx64. pose proof HK64.
      pose proof (Z.div_le_mono (x + I) (x + K) 8 ltac:(lia) ltac:(lia)) as LE.
      destruct (Z.lt_ge_cases ((x + I) / 8) ((x + K) / 8)) as [LT|GE].
      - exists (Z_to_bv 8 0). split; [|left; reflexivity]. apply (sf_zg _ _ _ _ SHx). split; [apply Z.div_le_mono; lia|exact LT].
      - assert (E : ((x + I) / 8 = (x + K) / 8)%Z) by lia.
        destruct (sf_last _ _ _ _ SHx) as (b1 & M & B). exists b1. rewrite E. split; [exact M|].
        destruct B as [B|B]; [left; exact B|right].
        pose proof (Z.div_mod (x + I) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + I) 8 ltac:(lia)).
        pose proof (Z.div_mod (x + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + K) 8 ltac:(lia)). lia.
    Qed.
    #[using="usp SHx Hx64"] Lemma zero_I : forall I g, (0 <= I <= K)%Z -> (x / 8 <= g < (x + I) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
    Proof.
      intros I g HI Hg. pose proof Hx64. pose proof (Z.div_le_mono (x + I) (x + K) 8 ltac:(lia) ltac:(lia)).
      apply (sf_zg _ _ _ _ SHx). lia.
    Qed.
    #[using="mem a b bufa bufb H SHx Hx64"] Lemma qfacts : forall I, (0 <= I <= K)%Z ->
      (8 * (x / 8) <= x < 8 * (x / 8) + 8)%Z /\ (8 * ((x + I) / 8) <= x + I < 8 * ((x + I) / 8) + 8)%Z
      /\ ((x + I) mod 8 = x + I - 8 * ((x + I) / 8))%Z
      /\ (SB + (x + I) / 8 + 8 < usp - 2264)%Z /\ (x / 8 <= (x + I) / 8 <= (x + K) / 8)%Z /\ SB = 0x7fff8000%Z
      /\ (x + K + 1 < 2 ^ 47)%Z.
    Proof.
      intros I HI. pose proof (sf_shd _ _ _ _ SHx) as Hshd. unfold ISC_FRAME in Hshd. pose proof SB_val. pose proof Hx64. pose proof HK64.
      pose proof (sf_rng _ _ _ _ SHx) as RNG. unfold kLowEnd, kHighBeg, kHighEnd in RNG.
      pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
      pose proof (Z.div_mod (x + I) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + I) 8 ltac:(lia)).
      pose proof (Z.div_le_mono x (x + I) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono (x + I) (x + K) 8 ltac:(lia) ltac:(lia)).
      lia.
    Qed.
    (* [comment removed for export] *)
    #[using="a b bufa bufb H SHx Hx64"] Lemma qwords : forall m I, sfr m -> (0 <= I <= K)%Z ->
      exists w1 w2 : word, cell m ((SB + x / 8) / 8 * 8) (bv_unsigned w1) /\ cell m ((SB + (x + I) / 8) / 8 * 8) (bv_unsigned w2).
    Proof.
      intros m I F HI. pose proof Hx64. destruct (qfacts I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (Z.div_mod (SB + x / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + x / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SB + (x + I) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (x + I) / 8) 8 ltac:(lia)).
      pose proof (Z.div_le_mono (SB + x / 8) (SB + (x + I) / 8) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono (SB + (x + I) / 8) (SB + (x + K) / 8) 8 ltac:(lia) ltac:(lia)).
      destruct (sf_words _ _ _ _ SHx ((SB + x / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@Hx64; @HI; @H0; @D0; @D1; @D01; @HSB; @H1; @H3; @H4; @H5; @H6]); lia)) ltac:((ltac2:(LK.k [@Hx64; @HI; @H0; @D0; @D1; @D01; @HSB; @H1; @H3; @H4; @H5; @H6]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w1 W1].
      destruct (sf_words _ _ _ _ SHx ((SB + (x + I) / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@Hx64; @HI; @H0; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:((ltac2:(LK.k [@Hx64; @HI; @H0; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w2 W2].
      exists w1, w2. split.
      - unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISC_FRAME; (ltac2:(LK.k [@Hx64; @HI; @H0; @D0; @D1; @D01; @HSB; @H1; @H2; @Dshd]); lia)]). exact W1.
      - unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact F | cbn; unfold ISC_FRAME; (ltac2:(LK.k [@Hx64; @HI; @H0; @D0; @D1; @D01; @HSB; @H3; @H4; @Dshd]); lia)]). exact W2.
    Qed.
    (* [comment removed for export] *)
    #[using="a b bufa bufb H SHx Hx64"] Lemma rp_pre : forall m (I : Z) b1, sfr m -> (64 <= I <= K)%Z ->
      mem (Z_to_bv 64 (SB + (x + I) / 8)) = Some b1 ->
      (bv_unsigned b1 = 0%Z \/ ((x + I) mod 8 < bv_unsigned b1 < 8)%Z) ->
      rpH m x (I + 1) (usp - 2192) b1.
    Proof.
      intros m I b1 F HI L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof Hx64. pose proof HK64.
      destruct (qfacts I ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof F as (F1 & F2 & F3 & F4).
      constructor; rewrite ?Z.add_assoc; replace (x + I + 1 - 1)%Z with (x + I)%Z by lia.
      - lia.
      - lia.
      - pose proof (sf_rng _ _ _ _ SHx). lia.
      - lia.
      - lia.
      - intros g Hg. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISC_FRAME; lia]). apply (zero_I I); lia.
      - rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISC_FRAME; lia]). exact L1.
      - exact Hb1.
      - intros y Hy. apply F3. apply (ic_stk _ _ _ _ _ _ _ H). unfold ISC_FRAME. lia.
      - exact (proj1 (cells_sfr m F)).
    Qed.
  End SH.

  #[using="Type"] Lemma rp_clob_isc : forall r : reg, isc_clob r = false -> rp_clob r = false.
  Proof.
    intros r Hr. unfold isc_clob in Hr. unfold rp_clob.
    repeat match type of Hr with (?u || ?v)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
    repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="H"] Lemma blk_QA1 : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> (I <= 63)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 I ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x44898 : word) m rom) (mkst regs' (0x448d4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (SB + a / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (a + I) / 8)
      /\ getr regs' 12 = Z_to_bv 64 (a + I) /\ getr regs' 13 = w /\ getr regs' 21 = getr regs 21 /\ base2 regs' I.
  Proof.
    intros regs m I F HI HI63 B H10. pose proof Hsp as HU. pose proof Ha64 as Hx64. pose proof HK64.
    pose proof B as ((B2 & B8 & B9 & B18 & B19 & BK) & B20 & B22 & B24 & B25 & B26).
    pose proof (ic_sha _ _ _ _ _ _ _ H) as SHx.
    destruct (qfacts a SHx Hx64 I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
    destruct (qwords a SHx Hx64 m I F HI) as (w1 & w2 & W1c & W2c).
    pose proof (Z.div_mod (SB + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + a / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + (a + I) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (a + I) / 8) 8 ltac:(lia)).
    eexists. eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44898 eq_refl D_44898)). rewrite getr_zero. zn.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_4489c eq_refl D_4489c); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaa8a0) F_448a0 eq_refl D_448a0);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_448a4 D_448a4 0xb35f8%Z C1 B18.
      mld F_448a8 D_448a8 SB C2 B18.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_448ac eq_refl D_448ac)). gr. rewrite H10, B18, v_add_zbv by lia.
      replace (I + a)%Z with (a + I)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_448b0 eq_refl D_448b0)). gr. rewrite B18, (v_srli_3 a) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_448b4 eq_refl D_448b4)). gr. rewrite (v_srli_3 (a + I)) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_448b8 eq_refl D_448b8)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_448bc eq_refl D_448bc)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hx64; @HSB; @HI; @D0; @D1; @DM; @HxK]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_448c0 eq_refl D_448c0)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_448c4 eq_refl D_448c4)). gr. rewrite v_andi_m8 by lia.
      mld F_448c8 D_448c8 (bv_unsigned w1) W1c B18.
      mld F_448cc D_448cc (bv_unsigned w2) W2c B18.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_448d0 eq_refl D_448d0)). gr.
      apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
      split; [gr; reflexivity|]. base2_tac B.
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma qa_loop : forall (n : nat) regs m (I g : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 (SB + g) -> getr regs 11 = Z_to_bv 64 (SB + (a + I) / 8) -> getr regs 12 = Z_to_bv 64 0 ->
    (a / 8 <= g < (a + I) / 8)%Z -> Z.of_nat n = ((a + I) / 8 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x44b14 : word) m rom) (mkst regs' (0x44b24 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 21 = getr regs 21 /\ base2 regs' I.
  Proof.
    pose proof Hsp as HU. pose proof Ha64 as Hx64. pose proof HK64. pose proof (ic_sha _ _ _ _ _ _ _ H) as SHx.
    induction n as [|n IH]; intros regs m I g F HI B H10 H11 H12 Hg Hn; [lia|].
    destruct (qfacts a SHx Hx64 I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISC_FRAME; lia]). apply (zero_I a SHx Hx64 I); lia. }
    destruct (Z.eq_dec (g + 1) ((a + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_44b14 eq_refl D_44b14);
                     gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44b18 eq_refl D_44b18)). gr. rewrite H10. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_44b1c eq_refl D_44b1c)). gr. rewrite H12, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_44b20 eq_refl D_44b20); gr; rewrite ?H11; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity.
      + base2_tac B.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m I (g + 1)%Z F HI) as (r2 & M2 & R12 & R21 & B2'); cycle -1.
      { exists r2. split; [|split; [|split]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_44b14 eq_refl D_44b14);
                       gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44b18 eq_refl D_44b18)). gr. rewrite H10. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_44b1c eq_refl D_44b1c)). gr. rewrite H12, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44b20 eq_refl D_44b20); gr; rewrite ?H11; br_eq).
          subst rr. exact M2.
        + exact R12.
        + rewrite R21. subst rr. gr. reflexivity.
        + exact B2'. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      { base2_tac B. }
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  #[using="H"] Lemma blk_QA2 : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 (SB + a / 8) -> getr regs 11 = Z_to_bv 64 (SB + (a + I) / 8) -> getr regs 12 = Z_to_bv 64 (a + I) ->
    exists regs',
      msteps SEGS (mkst regs (0x44af8 : word) m rom) (mkst regs' (0x448d8 : word) m rom)
      /\ getr regs' 21 = getr regs 21 /\ base2 regs' I.
  Proof.
    intros regs m I F HI B H10 H11 H12. pose proof Hsp as HU. pose proof Ha64 as Hx64. pose proof HK64.
    pose proof (ic_sha _ _ _ _ _ _ _ H) as SHx.
    destruct (qfacts a SHx Hx64 I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
    destruct (last_I a SHx Hx64 I HI) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (a + I) / 8)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISC_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    (* [comment removed for export] *)
    assert (T : exists regs1, msteps SEGS (mkst regs (0x44af8 : word) m rom) (mkst regs1 (0x44b10 : word) m rom)
                 /\ getr regs1 12 = Z_to_bv 64 0 /\ getr regs1 10 = getr regs 10 /\ getr regs1 11 = getr regs 11
                 /\ getr regs1 21 = getr regs 21 /\ base2 regs1 I).
    { destruct Hb1 as [Hz | Hpart].
      - eexists. split.
        + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_44af8 eq_refl D_44af8);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
          unfold v_lb. rewrite Hsg, Hz.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44afc eq_refl D_44afc)). gr. rewrite H12, v_andi_7 by lia.
          mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44b00 eq_refl D_44b00)). gr. rewrite getr_zero.
          unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
          mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_44b04 eq_refl D_44b04)). gr.
          unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44b08 eq_refl D_44b08)). gr.
          mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_44b0c eq_refl D_44b0c)). gr. rewrite AND0.
          apply mst_refl.
        + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base2_tac B.
      - eexists. split.
        + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_44af8 eq_refl D_44af8);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
          unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44afc eq_refl D_44afc)). gr. rewrite H12, v_andi_7 by lia.
          mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44b00 eq_refl D_44b00)). gr. rewrite getr_zero.
          unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
          mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_44b04 eq_refl D_44b04)). gr.
          unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44b08 eq_refl D_44b08)). gr.
          mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_44b0c eq_refl D_44b0c)). gr. rewrite AND1.
          apply mst_refl.
        + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base2_tac B. }
    destruct T as (q1 & M1 & A12 & A10 & A11 & A21 & B1).
    destruct (Z.eq_dec (a / 8) ((a + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split].
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_44b10 eq_refl D_44b10); gr; rewrite ?A10, ?A11, ?H10, ?H11; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44b24 eq_refl D_44b24)). gr. rewrite A12, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44b28 eq_refl D_44b28); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + gr. exact A21.
      + base2_tac B1.
    - evar (rr : bvmap 5 word).
      edestruct (qa_loop (Z.to_nat ((a + I) / 8 - a / 8)) rr m I (a / 8) F HI) as (r2 & M2 & R12 & R21 & B2'); cycle -1.
      { eexists. split; [|split].
        + eapply msteps_trans; [exact M1|].
          mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_44b10 eq_refl D_44b10); gr; rewrite ?A10, ?A11, ?H10, ?H11; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44b24 eq_refl D_44b24)). rewrite R12, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44b28 eq_refl D_44b28); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + gr. rewrite R21. subst rr. exact A21.
        + base2_tac B2'. }
      all: subst rr; try assumption; try lia.
      { rewrite A10. exact H10. } { rewrite A11. exact H11. }
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma blk_LA : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> (64 <= I)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 I -> getr regs 21 = Z_to_bv 64 I ->
    exists regs' m',
      msteps SEGS (mkst regs (0x44898 : word) m rom) (mkst regs' (0x448d8 : word) m' rom)
      /\ sfr m' /\ getr regs' 21 = Z_to_bv 64 I /\ base2 regs' I.
  Proof.
    intros regs m I F HI HI64 B H10 H21. pose proof Hsp. pose proof Ha64 as Hx64. pose proof HK64.
    pose proof B as ((B2 & B8 & B9 & B18 & B19 & BK) & B20 & B22 & B24 & B25 & B26).
    pose proof (ic_sha _ _ _ _ _ _ _ H) as SHx.
    destruct (last_I a SHx Hx64 I HI) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom a (I + 1) (usp - 2192) b1 (rp_pre a SHx Hx64 m I b1 F ltac:(lia) L1 Hb1) rr (0x44b38 : word) ret_ok_64de4)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split]].
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44898 eq_refl D_44898)). rewrite getr_zero. zn.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_4489c eq_refl D_4489c); gr; rewrite ?H10; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44a6c eq_refl D_44a6c); gr; rewrite ?B22, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44b2c eq_refl D_44b2c)). gr. rewrite B18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44b30 eq_refl D_44b30)). gr. rewrite B22. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_44b34 eq_refl D_44b34)). rewrite lit_64de0.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44b38 eq_refl D_44b38); gr; rewrite ?R10, ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - rewrite (K1 21) by reflexivity. subst rr. gr. exact H21.
      - subst rr. split; [split; [exact R2|]|].
        + split; [rewrite (K1 8) by reflexivity; gr; exact B8|]. split; [rewrite (K1 9) by reflexivity; gr; exact B9|].
          split; [rewrite (K1 18) by reflexivity; gr; exact B18|]. split; [rewrite (K1 19) by reflexivity; gr; exact B19|].
          intros r Hr He. rewrite (K1 r (rp_clob_isc r Hr)). keep_tac Hr He. apply BK; assumption.
        + rewrite !K1 by reflexivity. gr. repeat split; assumption. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma blk_CA : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 I -> getr regs 21 = Z_to_bv 64 I ->
    exists regs' m',
      msteps SEGS (mkst regs (0x44898 : word) m rom) (mkst regs' (0x448d8 : word) m' rom)
      /\ sfr m' /\ getr regs' 21 = Z_to_bv 64 I /\ base2 regs' I.
  Proof.
    intros regs m I F HI B H10 H21.
    destruct (Z.lt_ge_cases I 64) as [Hsmall | Hbig]; [|exact (blk_LA regs m I F HI Hbig B H10 H21)].
    destruct (blk_QA1 regs m I F HI ltac:(lia) B H10) as (q1 & w & M1 & A10 & A11 & A12 & A13 & A21 & B1).
    pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
    destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
    - exists q1, m. split; [|split; [exact F|split; [rewrite A21; exact H21|exact B1]]].
      eapply msteps_trans; [exact M1|].
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_448d4 eq_refl D_448d4); gr; rewrite ?A13, ?getr_zero; br_eq).
      apply mst_refl.
    - assert (NZu : bv_unsigned w <> 0%Z) by (intros E0; apply NZ; rewrite <- (zbv_self w), E0; reflexivity).
      destruct (blk_QA2 q1 m I F HI B1 A10 A11 A12) as (q2 & M2 & C21 & B2').
      exists q2, m. split; [|split; [exact F|split; [rewrite C21, A21; exact H21|exact B2']]].
      eapply msteps_trans; [exact M1|].
      mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_448d4 eq_refl D_448d4); gr; rewrite ?A13, ?getr_zero;
                   rewrite <- (zbv_self w); br_eq).
      exact M2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="H"] Lemma blk_Bpre : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    exists regs',
      msteps SEGS (mkst regs (0x448d8 : word) m rom) (mkst regs' (0x448e8 : word) m rom)
      /\ getr regs' 21 = getr regs 21 /\ base2 regs' I.
  Proof.
    intros regs m I F HI B. pose proof Hsp. pose proof Hb64. pose proof HK64.
    pose proof B as ((B2 & B8 & B9 & B18 & B19 & BK) & B20 & B22 & B24 & B25 & B26).
    pose proof (cells_sfr m F) as (_ & _ & _ & _ & SS).
    eexists. split.
    - mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_448d8 eq_refl D_448d8);
                   gr; rewrite ?B24; imm_norm; zn; rewrite ?Z.add_0_r; first [exact SS | adr 0x14521d%Z; exact SS]).
      change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_448dc eq_refl D_448dc); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_448e0 eq_refl D_448e0)). gr. rewrite B9. rewrite v_not_zbv by lia.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_448e4 eq_refl D_448e4); gr; rewrite ?B20; br_lt).
      apply mst_refl.
    - split; [gr; reflexivity|]. base2_tac B.
  Qed.

  #[using="H"] Lemma blk_QB1 : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> (I <= 63)%Z -> base2 regs I ->
    getr regs 21 = Z_to_bv 64 I ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x448e8 : word) m rom) (mkst regs' (0x44924 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (SB + b / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (b + I) / 8)
      /\ getr regs' 21 = Z_to_bv 64 (b + I) /\ getr regs' 12 = w /\ base2 regs' I.
  Proof.
    intros regs m I F HI HI63 B H21. pose proof Hsp as HU. pose proof Hb64 as Hx64. pose proof HK64.
    pose proof B as ((B2 & B8 & B9 & B18 & B19 & BK) & B20 & B22 & B24 & B25 & B26).
    pose proof (ic_shb _ _ _ _ _ _ _ H) as SHx.
    destruct (qfacts b SHx Hx64 I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
    pose proof (cells_sfr m F) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
    destruct (qwords b SHx Hx64 m I F HI) as (w1 & w2 & W1c & W2c).
    pose proof (Z.div_mod (SB + b / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + b / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + (b + I) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (b + I) / 8) 8 ltac:(lia)).
    eexists. eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_448e8 eq_refl D_448e8)). rewrite getr_zero. zn.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_448ec eq_refl D_448ec); gr; rewrite ?H21; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaa8f0) F_448f0 eq_refl D_448f0);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_448f4 D_448f4 0xb35f8%Z C1 B18.
      mld F_448f8 D_448f8 SB C2 B18.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_448fc eq_refl D_448fc)). gr. rewrite H21, B9, v_add_zbv by lia.
      replace (I + b)%Z with (b + I)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_44900 eq_refl D_44900)). gr. rewrite B9, (v_srli_3 b) by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_44904 eq_refl D_44904)). gr. rewrite (v_srli_3 (b + I)) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_44908 eq_refl D_44908)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hx64; @HSB; @HI; @D0; @HxK]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_4490c eq_refl D_4490c)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hx64; @HSB; @HI; @D0; @D1; @DM; @HxK]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44910 eq_refl D_44910)). gr. rewrite v_andi_m8 by lia.
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44914 eq_refl D_44914)). gr. rewrite v_andi_m8 by lia.
      mld F_44918 D_44918 (bv_unsigned w1) W1c B18.
      mld F_4491c D_4491c (bv_unsigned w2) W2c B18.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_44920 eq_refl D_44920)). gr.
      apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base2_tac B.
  Qed.

  #[using="H"] Lemma qb_loop : forall (n : nat) regs m (I g : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 (SB + g) -> getr regs 11 = Z_to_bv 64 (SB + (b + I) / 8) -> getr regs 12 = Z_to_bv 64 0 ->
    (b / 8 <= g < (b + I) / 8)%Z -> Z.of_nat n = ((b + I) / 8 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x44bf4 : word) m rom) (mkst regs' (0x44c04 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 0 /\ base2 regs' I.
  Proof.
    pose proof Hsp as HU. pose proof Hb64 as Hx64. pose proof HK64. pose proof (ic_shb _ _ _ _ _ _ _ H) as SHx.
    induction n as [|n IH]; intros regs m I g F HI B H10 H11 H12 Hg Hn; [lia|].
    destruct (qfacts b SHx Hx64 I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISC_FRAME; lia]). apply (zero_I b SHx Hx64 I); lia. }
    destruct (Z.eq_dec (g + 1) ((b + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_44bf4 eq_refl D_44bf4);
                     gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44bf8 eq_refl D_44bf8)). gr. rewrite H10. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_44bfc eq_refl D_44bfc)). gr. rewrite H12, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_44c00 eq_refl D_44c00); gr; rewrite ?H11; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + base2_tac B.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m I (g + 1)%Z F HI) as (r2 & M2 & R12 & B2'); cycle -1.
      { exists r2. split; [|split].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_44bf4 eq_refl D_44bf4);
                       gr; rewrite ?H10; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44bf8 eq_refl D_44bf8)). gr. rewrite H10. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_44bfc eq_refl D_44bfc)). gr. rewrite H12, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44c00 eq_refl D_44c00); gr; rewrite ?H11; br_eq).
          subst rr. exact M2.
        + exact R12.
        + exact B2'. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      { base2_tac B. }
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  #[using="H"] Lemma blk_QB2 : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    getr regs 10 = Z_to_bv 64 (SB + b / 8) -> getr regs 11 = Z_to_bv 64 (SB + (b + I) / 8) -> getr regs 21 = Z_to_bv 64 (b + I) ->
    exists regs',
      msteps SEGS (mkst regs (0x44bd8 : word) m rom) (mkst regs' (0x44928 : word) m rom)
      /\ base2 regs' I.
  Proof.
    intros regs m I F HI B H10 H11 H21. pose proof Hsp as HU. pose proof Hb64 as Hx64. pose proof HK64.
    pose proof (ic_shb _ _ _ _ _ _ _ H) as SHx.
    destruct (qfacts b SHx Hx64 I HI) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
    destruct (last_I b SHx Hx64 I HI) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (b + I) / 8)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact F | rewrite zbv_u by lia; unfold ISC_FRAME; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (T : exists regs1, msteps SEGS (mkst regs (0x44bd8 : word) m rom) (mkst regs1 (0x44bf0 : word) m rom)
                 /\ getr regs1 12 = Z_to_bv 64 0 /\ getr regs1 10 = getr regs 10 /\ getr regs1 11 = getr regs 11 /\ base2 regs1 I).
    { destruct Hb1 as [Hz | Hpart].
      - eexists. split.
        + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_44bd8 eq_refl D_44bd8);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
          unfold v_lb. rewrite Hsg, Hz.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44bdc eq_refl D_44bdc)). gr. rewrite H21, v_andi_7 by lia.
          mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44be0 eq_refl D_44be0)). gr. rewrite getr_zero.
          unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
          mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_44be4 eq_refl D_44be4)). gr.
          unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44be8 eq_refl D_44be8)). gr.
          mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_44bec eq_refl D_44bec)). gr. rewrite AND0.
          apply mst_refl.
        + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base2_tac B.
      - eexists. split.
        + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_44bd8 eq_refl D_44bd8);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
          unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44bdc eq_refl D_44bdc)). gr. rewrite H21, v_andi_7 by lia.
          mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44be0 eq_refl D_44be0)). gr. rewrite getr_zero.
          unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
          mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_44be4 eq_refl D_44be4)). gr.
          unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
          mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_44be8 eq_refl D_44be8)). gr.
          mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_44bec eq_refl D_44bec)). gr. rewrite AND1.
          apply mst_refl.
        + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base2_tac B. }
    destruct T as (q1 & M1 & A12 & A10 & A11 & B1).
    destruct (Z.eq_dec (b / 8) ((b + I) / 8)) as [Heq | Hne].
    - eexists. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_44bf0 eq_refl D_44bf0); gr; rewrite ?A10, ?A11, ?H10, ?H11; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44c04 eq_refl D_44c04)). gr. rewrite A12, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44c08 eq_refl D_44c08); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + base2_tac B1.
    - evar (rr : bvmap 5 word).
      edestruct (qb_loop (Z.to_nat ((b + I) / 8 - b / 8)) rr m I (b / 8) F HI) as (r2 & M2 & R12 & B2'); cycle -1.
      { eexists. split.
        + eapply msteps_trans; [exact M1|].
          mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_44bf0 eq_refl D_44bf0); gr; rewrite ?A10, ?A11, ?H10, ?H11; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_44c04 eq_refl D_44c04)). rewrite R12, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44c08 eq_refl D_44c08); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + base2_tac B2'. }
      all: subst rr; try assumption; try lia.
      { rewrite A10. exact H10. } { rewrite A11. exact H11. }
  Qed.

  #[using="H"] Lemma blk_LB : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> (64 <= I)%Z -> base2 regs I ->
    getr regs 21 = Z_to_bv 64 I ->
    exists regs' m',
      msteps SEGS (mkst regs (0x448e8 : word) m rom) (mkst regs' (0x44928 : word) m' rom)
      /\ sfr m' /\ base2 regs' I.
  Proof.
    intros regs m I F HI HI64 B H21. pose proof Hsp. pose proof Hb64 as Hx64. pose proof HK64.
    pose proof B as ((B2 & B8 & B9 & B18 & B19 & BK) & B20 & B22 & B24 & B25 & B26).
    pose proof (ic_shb _ _ _ _ _ _ _ H) as SHx.
    destruct (last_I b SHx Hx64 I HI) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom b (I + 1) (usp - 2192) b1 (rp_pre b SHx Hx64 m I b1 F ltac:(lia) L1 Hb1) rr (0x44c18 : word) ret_ok_64ec4)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split].
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_448e8 eq_refl D_448e8)). rewrite getr_zero. zn.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_448ec eq_refl D_448ec); gr; rewrite ?H21; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44af0 eq_refl D_44af0); gr; rewrite ?B20, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44c0c eq_refl D_44c0c)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44c10 eq_refl D_44c10)). gr. rewrite B20. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_44c14 eq_refl D_44c14)). rewrite lit_64ec0.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_44c18 eq_refl D_44c18); gr; rewrite ?R10, ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact F.
      - subst rr. split; [split; [exact R2|]|].
        + split; [rewrite (K1 8) by reflexivity; gr; exact B8|]. split; [rewrite (K1 9) by reflexivity; gr; exact B9|].
          split; [rewrite (K1 18) by reflexivity; gr; exact B18|]. split; [rewrite (K1 19) by reflexivity; gr; exact B19|].
          intros r Hr He. rewrite (K1 r (rp_clob_isc r Hr)). keep_tac Hr He. apply BK; assumption.
        + rewrite !K1 by reflexivity. gr. repeat split; assumption. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="H"] Lemma blk_CB : forall regs m (I : Z), sfr m -> (0 <= I <= K)%Z -> base2 regs I ->
    getr regs 21 = Z_to_bv 64 I ->
    exists regs' m',
      msteps SEGS (mkst regs (0x448e8 : word) m rom) (mkst regs' (0x44928 : word) m' rom)
      /\ sfr m' /\ base2 regs' I.
  Proof.
    intros regs m I F HI B H21.
    destruct (Z.lt_ge_cases I 64) as [Hsmall | Hbig]; [|exact (blk_LB regs m I F HI Hbig B H21)].
    destruct (blk_QB1 regs m I F HI ltac:(lia) B H21) as (q1 & w & M1 & A10 & A11 & A21 & A12 & B1).
    pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
    destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
    - exists q1, m. split; [|split; [exact F|exact B1]].
      eapply msteps_trans; [exact M1|].
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_44924 eq_refl D_44924); gr; rewrite ?A12, ?getr_zero; br_eq).
      apply mst_refl.
    - assert (NZu : bv_unsigned w <> 0%Z) by (intros E0; apply NZ; rewrite <- (zbv_self w), E0; reflexivity).
      destruct (blk_QB2 q1 m I F HI B1 A10 A11 A21) as (q2 & M2 & B2').
      exists q2, m. split; [|split; [exact F|exact B2']].
      eapply msteps_trans; [exact M1|].
      mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_44924 eq_refl D_44924); gr; rewrite ?A12, ?getr_zero;
                   rewrite <- (zbv_self w); br_eq).
      exact M2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma cmpx_word (ua ub : Z) : (0 <= ua < 256)%Z -> (0 <= ub < 256)%Z ->
    v_sub (v_sltu (Z_to_bv 64 ub) (Z_to_bv 64 ua)) (v_sltu (Z_to_bv 64 ua) (Z_to_bv 64 ub)) = Z_to_bv 64 (cmpx ua ub).
  Proof.
    intros Ha Hb. unfold v_sltu, cmpx. rewrite !c_ltu_zbv by lia.
    destruct (Z.ltb_spec ua ub); destruct (Z.ltb_spec ub ua); try lia; apply bv_eq; vm_compute; reflexivity.
  Qed.

  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?x) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace x with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  #[using="H Hret H01 H02"] Lemma blk_E : forall regs mF (I : Z), sfr mF -> (0 <= I <= K)%Z -> base2 regs I ->
    exists regs',
      msteps SEGS (mkst regs (0x44928 : word) mF rom) (mkst regs' ra mF rom)
      /\ getr regs' 10 = Z_to_bv 64 (cmpx (bv_unsigned (BA I)) (bv_unsigned (BB I)))
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, isc_clob r = false -> getr regs' r = getr regs0 r).
  Proof.
    intros regs mF I F HI B. pose proof Hsp. pose proof Ha64. pose proof Hb64. pose proof HK64.
    pose proof B as ((B2 & B8 & B9 & B18 & B19 & BK) & B20 & B22 & B24 & B25 & B26).
    pose proof (byte_range (BA I)) as RA8. pose proof (byte_range (BB I)) as RB8.
    pose proof F as (F1 & F2 & F3 & F4).
    assert (HF : forall x, (usp - 104 <= x)%Z -> (x + 8 <= usp)%Z -> rdn SEGS mF (Z_to_bv 64 x) 8 = rdn SEGS p13 (Z_to_bv 64 x) 8).
    { intros x Hx1 Hx2. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros y Hy. rewrite zbv_u in Hy by lia. cbn in Hy. apply F2. lia. }
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18. pose proof rd_s3 as RD19.
    pose proof rd_s4 as RD20. pose proof rd_s5 as RD21. pose proof rd_s6 as RD22. pose proof rd_s7 as RD23. pose proof rd_s8 as RD24.
    pose proof rd_s9 as RD25. pose proof rd_s10 as RD26. pose proof rd_s11 as RD27.
    rewrite <- HF in RD1, RD8, RD9, RD18, RD19, RD20, RD21, RD22, RD23, RD24, RD25, RD26, RD27 by lia.
    eexists. split.
    - mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_44928 eq_refl D_44928)). gr. rewrite B25, B26.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_4492c eq_refl D_4492c)). gr. rewrite B25, B26.
      mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_44930 eq_refl D_44930)). gr. rewrite cmpx_word by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44934 eq_refl D_44934)). gr. rewrite B19.
      replace (v_addi ra 0) with ra by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44938 eq_refl D_44938)). gr. rewrite B18. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4493c eq_refl D_4493c)). gr. rewrite B9. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44940 eq_refl D_44940)). gr.
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_44944 eq_refl D_44944)). rewrite lit_64bf0.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x44948) F_447ec eq_refl D_447ec); gr; reflexivity |].
      imm_norm. rewrite ret_64bf0.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44948 eq_refl D_44948)). gr.
      rewrite (v_addi_zbv (cmpx _ _)) by (unfold cmpx; destruct (_ <? _); [lia|destruct (_ <? _); lia]). rewrite Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4494c eq_refl D_4494c)). gr. rewrite B2. zn.
      mld2 F_44950 D_44950 ra RD1 B2.
      mld2 F_44954 D_44954 (getr regs0 8) RD8 B2.
      mld2 F_44958 D_44958 (getr regs0 9) RD9 B2.
      mld2 F_4495c D_4495c (getr regs0 18) RD18 B2.
      mld2 F_44960 D_44960 (getr regs0 19) RD19 B2.
      mld2 F_44964 D_44964 (getr regs0 20) RD20 B2.
      mld2 F_44968 D_44968 (getr regs0 21) RD21 B2.
      mld2 F_4496c D_4496c (getr regs0 22) RD22 B2.
      mld2 F_44970 D_44970 (getr regs0 23) RD23 B2.
      mld2 F_44974 D_44974 (getr regs0 24) RD24 B2.
      mld2 F_44978 D_44978 (getr regs0 25) RD25 B2.
      mld2 F_4497c D_4497c (getr regs0 26) RD26 B2.
      mld2 F_44980 D_44980 (getr regs0 27) RD27 B2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44984 eq_refl D_44984)). gr. zn.
      replace (usp - 2192 + 160 + 2032)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_44988 eq_refl D_44988); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
      intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [gr; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [gr; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 22) as [-> | N22]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 23) as [-> | N23]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 24) as [-> | N24]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 25) as [-> | N25]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 26) as [-> | N26]; [gr; reflexivity|].
      destruct (bv_eq_dec _ r 27) as [-> | N27]; [gr; reflexivity|].
      assert (He : ekeep r = false).
      { unfold ekeep. rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8), (bv_eqb_neq _ _ N9),
          (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N22),
          (bv_eqb_neq _ _ N23), (bv_eqb_neq _ _ N24), (bv_eqb_neq _ _ N25), (bv_eqb_neq _ _ N26), (bv_eqb_neq _ _ N27). reflexivity. }
      keep_tac Hr He. apply BK; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="a b H Hret H01 H02 H010 H011"] Theorem isc_body :
    exists regs' (I : Z) m',
      msteps SEGS (mkst regs0 (0x447f0 : word) mem rom) (mkst regs' ra m' rom)
      /\ (0 <= I <= K)%Z
      /\ (forall j, (0 <= j < I)%Z -> bv_unsigned (BA j) = bv_unsigned (BB j) /\ bv_unsigned (BA j) <> 0%Z)
      /\ (bv_unsigned (BA I) = 0%Z \/ bv_unsigned (BA I) <> bv_unsigned (BB I))
      /\ getr regs' 10 = Z_to_bv 64 (cmpx (bv_unsigned (BA I)) (bv_unsigned (BB I)))
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, isc_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - ISC_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
  Proof.
    pose proof Hsp as HU. pose proof HK64.
    destruct blk_P as (q1 & MP & P2 & P8 & P9 & P18 & P19 & PK).
    assert (B1 : base q1) by (repeat split; assumption).
    destruct (blk_L0 q1 B1) as (q2 & ML0 & L20 & L27 & B2).
    destruct (isc_loop (Z.to_nat K) q2 0 p15 sfr_p15 B2 L20 ltac:(lia) ltac:(lia) ltac:(intros; lia)) as (q3 & I & ML & HI & R20 & R25 & R26 & EX & INV & R27 & B3).
    destruct (blk_F q3 I p15 sfr_p15 B3 ltac:(lia) R20 R25 R26) as (q4 & MF & F10 & F21 & B4).
    destruct (blk_CA q4 p15 I sfr_p15 ltac:(lia) B4 F10 F21) as (q5 & m5 & MA & S5 & A21 & B5).
    destruct (blk_Bpre q5 m5 I S5 ltac:(lia) B5) as (q6 & MB0 & C21 & B6).
    destruct (blk_CB q6 m5 I S5 ltac:(lia) B6 ltac:(rewrite C21; exact A21)) as (q7 & m7 & MB & S7 & B7).
    destruct (blk_E q7 m7 I S7 ltac:(lia) B7) as (q8 & ME & E10 & E2 & E1 & EK).
    pose proof S7 as (G1 & G2 & G3 & G4).
    exists q8, I, m7. split.
    { eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact ML0|]. eapply msteps_trans; [exact ML|].
      eapply msteps_trans; [exact MF|]. eapply msteps_trans; [exact MA|]. eapply msteps_trans; [exact MB0|].
      eapply msteps_trans; [exact MB|]. exact ME. }
    split; [lia|]. split; [exact INV|]. split; [exact EX|]. split; [exact E10|]. split; [exact E2|]. split; [exact E1|].
    split; [exact EK|]. split; [exact G1|]. split; [exact G4|exact G3].
  Qed.
End ISC.

(* [comment removed for export] *)
Theorem isc_run :
  forall (mem rom : word -> option byte) (a b usp : Z) (bufa bufb : list byte) (K : Z),
  iscH mem a b usp bufa bufb K ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b ->
  exists regs' (I : Z) m',
    msteps SEGS (mkst regs (0x44238 : word) mem rom) (mkst regs' ra m' rom)
    /\ (0 <= I <= K)%Z
    /\ (forall j, (0 <= j < I)%Z -> bv_unsigned (nth (Z.to_nat j) bufa B0) = bv_unsigned (nth (Z.to_nat j) bufb B0)
                                   /\ bv_unsigned (nth (Z.to_nat j) bufa B0) <> 0%Z)
    /\ (bv_unsigned (nth (Z.to_nat I) bufa B0) = 0%Z \/ bv_unsigned (nth (Z.to_nat I) bufa B0) <> bv_unsigned (nth (Z.to_nat I) bufb B0))
    /\ getr regs' 10 = Z_to_bv 64 (cmpx (bv_unsigned (nth (Z.to_nat I) bufa B0)) (bv_unsigned (nth (Z.to_nat I) bufb B0)))
    /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, isc_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - ISC_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
Proof.
  intros mem rom a b usp bufa bufb K H regs ra Hret H1 H2 H10 H11.
  destruct (isc_body mem rom a b usp bufa bufb K H regs ra Hret H1 H2 H10 H11) as (regs' & I & m' & M & REST).
  exists regs', I, m'. split; [|exact REST].
  mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44238 eq_refl D_44238)).
  exact M.
Qed.
