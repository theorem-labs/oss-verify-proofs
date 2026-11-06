(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VBothMuslStrLib VBothMuslMemcmp.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothTls_code VBothIcStrlen_code VBothIcBcmp_code VBothMemsetWalk VBothTlsWalk.
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
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Abbreviation B0 := (Z_to_bv 8 0).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_68cc8 : v_addi (0x45110 : word) 4 = (0x45114 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_68dc8 : v_addi (0x45210 : word) 4 = Z_to_bv 64 0x45214. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_6904c : v_addi (0x45494 : word) 4 = (0x45498 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69158 : v_addi (0x455a0 : word) 4 = (0x455a4 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_6951c : v_addi (0x45964 : word) 4 = Z_to_bv 64 0x45968. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69530 : v_addi (0x45978 : word) 4 = Z_to_bv 64 0x4597c. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69554 : v_addi (0x4599c : word) 4 = (0x459a0 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69460 : v_addi (0x458a8 : word) 4 = Z_to_bv 64 0x458ac. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69474 : v_addi (0x458bc : word) 4 = Z_to_bv 64 0x458c0. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69498 : v_addi (0x458e0 : word) 4 = (0x458e4 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_68cc4 : ret_ok (0x45114 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_69048 : ret_ok (0x45498 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_69154 : ret_ok (0x455a4 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_69550 : ret_ok (0x459a0 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_69494 : ret_ok (0x458e4 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_68dc8 : v_jalr (Z_to_bv 64 0x45214) 0 = (0x45214 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_6951c : v_jalr (Z_to_bv 64 0x45968) 0 = (0x45968 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_69530 : v_jalr (Z_to_bv 64 0x4597c) 0 = (0x4597c : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_69460 : v_jalr (Z_to_bv 64 0x458ac) 0 = (0x458ac : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_69474 : v_jalr (Z_to_bv 64 0x458c0) 0 = (0x458c0 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma jalr_bcmp : v_jalr (Z_to_bv 64 0xa26e8) 0 = (0xa26e8 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma jalr_memcmp : v_jalr (Z_to_bv 64 0xa27b8) 0 = (0xa27b8 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Definition IBC_FRAME : Z := 4552.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ibc_cells (m : word -> option byte) : Prop :=
  cells m
  /\ rdn SEGS m (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xa94a8 0x1436e8                                     (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0x1437e6) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ rdn SEGS m (Z_to_bv 64 0x1437e7) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xab1e8 0xa26e8                                     (* [comment removed for export] *)
  /\ cell m 0xab1e0 0xa27b8.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Record accfacts (mem : word -> option byte) (x n usp : Z) : Prop := {
  af_zg   : forall g, (x / 8 <= g < (x + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  af_last : exists b1 : byte, mem (Z_to_bv 64 (SB + (x + n - 1) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((x + n - 1) mod 8 < bv_unsigned b1 < 8)%Z);
  af_w1   : exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + x / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  af_w2   : exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + (x + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  af_shd  : (SB + (x + n - 1) / 8 + 8 < usp - IBC_FRAME)%Z;
  af_rng  : (x + n <= kLowEnd)%Z \/ (kHighBeg <= x /\ x + n <= kHighEnd)%Z;
  af_sap  : (usp <= x \/ x + n <= usp - IBC_FRAME)%Z
}.

Record ibcH (mem : word -> option byte) (a b n usp : Z) (bufa bufb : list byte) : Prop := {
  ib_n    : (0 <= n <= 2 ^ 40)%Z;
  ib_a    : (0 <= a)%Z;  ib_b : (0 <= b)%Z;
  ib_an   : (a + n < 2 ^ 64)%Z;  ib_bn : (b + n < 2 ^ 64)%Z;
  ib_lena : length bufa = Z.to_nat n;  ib_lenb : length bufb = Z.to_nat n;
  ib_bufa : rdn SEGS mem (Z_to_bv 64 a) (length bufa) = Some bufa;
  ib_bufb : rdn SEGS mem (Z_to_bv 64 b) (length bufb) = Some bufb;
  ib_sp   : (SB + IBC_FRAME + 16 <= usp < 2 ^ 64)%Z;
  ib_fa   : (0 < n)%Z -> accfacts mem a n usp;
  ib_fb   : (0 < n)%Z -> accfacts mem b n usp;
  ib_stk  : forall x, (usp - IBC_FRAME <= x < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 x) 1 = true;
  ib_cel  : ibc_cells mem
}.

(* [comment removed for export] *)
Definition ibc_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.
Definition ekeep (r : reg) : bool :=
  (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21
   || bv_eqb r 22 || bv_eqb r 23 || bv_eqb r 24 || bv_eqb r 25 || bv_eqb r 26 || bv_eqb r 27)%bool.
(* [comment removed for export] *)
Definition sreg (r : reg) : bool :=
  (bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21
   || bv_eqb r 22 || bv_eqb r 23 || bv_eqb r 24 || bv_eqb r 25 || bv_eqb r 26 || bv_eqb r 27)%bool.

Lemma rp_clob_ibc : forall r : reg, ibc_clob r = false -> rp_clob r = false.
Proof.
  intros r Hr. unfold ibc_clob in Hr. unfold rp_clob.
  repeat match type of Hr with (?u || ?v)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
  repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
Qed.
Lemma sreg_not_clob : forall r : reg, sreg r = true -> ibc_clob r = false /\ rp_clob r = false /\ r <> 1.
Proof.
  intros r Hr. unfold sreg in Hr.
  repeat (apply Bool.orb_prop in Hr; destruct Hr as [Hr|Hr]); unfold bv_eqb in Hr; apply Z.eqb_eq in Hr; apply bv_eq in Hr; subst r;
    (split; [reflexivity|split; [reflexivity|intros X; discriminate X]]).
Qed.

Section IBC.
  Variables (mem rom : word -> option byte) (a b n usp : Z) (bufa bufb : list byte).
  Hypothesis H : ibcH mem a b n usp bufa bufb.

  #[using="mem a b n bufa bufb H"] Lemma Hsp : (0x7fff8000 + 4568 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (ib_sp _ _ _ _ _ _ _ H). unfold IBC_FRAME, SB in *. lia. Qed.
  #[using="mem a b usp bufa bufb H"] Lemma Hn : (0 <= n <= 2 ^ 40)%Z. Proof. exact (ib_n _ _ _ _ _ _ _ H). Qed.
  #[using="mem b usp bufa bufb H"] Lemma Ha64 : (0 <= a)%Z /\ (a + n < 2 ^ 64)%Z. Proof. pose proof (ib_a _ _ _ _ _ _ _ H). pose proof (ib_an _ _ _ _ _ _ _ H). lia. Qed.
  #[using="mem a usp bufa bufb H"] Lemma Hb64 : (0 <= b)%Z /\ (b + n < 2 ^ 64)%Z. Proof. pose proof (ib_b _ _ _ _ _ _ _ H). pose proof (ib_bn _ _ _ _ _ _ _ H). lia. Qed.

  (* [comment removed for export] *)
  Definition OUT (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - IBC_FRAME \/ usp <= bv_unsigned x)%Z -> m x = mem x)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true)
    /\ (forall x, mem x <> None -> m x <> None).
  #[using="Type"] Lemma OUT_mem : OUT mem. Proof. split; [intros; reflexivity|split; intros; assumption]. Qed.
  #[using="Type"] Lemma OUT_below : forall m (x : word), OUT m -> (bv_unsigned x < usp - IBC_FRAME)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. exact (F1 x (or_introl Hx)). Qed.
  #[using="a b n bufa bufb H"] Lemma rdn_OUT_below : forall m (x : Z) k, OUT m -> (0 <= x)%Z -> (x + Z.of_nat k <= usp - IBC_FRAME)%Z ->
    rdn SEGS m (Z_to_bv 64 x) k = rdn SEGS mem (Z_to_bv 64 x) k.
  Proof.
    intros m x k F Hx Hk. pose proof Hsp. unfold IBC_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros y Hy. rewrite zbv_u in Hy by lia. apply (OUT_below m y F). unfold IBC_FRAME. lia.
  Qed.
  #[using="a b n bufa bufb H"] Lemma rdn_OUT_out : forall m (x : Z) k, OUT m -> (0 <= x < 2 ^ 64)%Z -> (x + Z.of_nat k <= 2 ^ 64)%Z ->
    (x + Z.of_nat k <= usp - IBC_FRAME \/ usp <= x)%Z ->
    rdn SEGS m (Z_to_bv 64 x) k = rdn SEGS mem (Z_to_bv 64 x) k.
  Proof.
    intros m x k (F1 & _) Hx Hk Hap. pose proof Hsp. unfold IBC_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros y Hy. rewrite zbv_u in Hy by lia. apply F1. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="a b n bufa bufb H"] Lemma OUT_w8 : forall m (x : Z) (v : word), OUT m -> (usp - IBC_FRAME <= x)%Z -> (x + 8 <= usp)%Z ->
    OUT (wbytes m (Z_to_bv 64 x) (word_to_le_bytes 8 v)).
  Proof.
    intros m x v (F1 & F2 & F3) Hx1 Hx2. pose proof Hsp. unfold IBC_FRAME in *. split; [|split].
    - intros y Hy. unfold IBC_FRAME in Hy. rewrite <- (F1 y Hy). destruct Hy as [Hy|Hy].
      + apply wbytes_below; rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z; rewrite ?zbv_u by lia; lia.
      + apply wbytes_above; rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z; rewrite ?zbv_u by lia; lia.
    - intros y Hy. apply store_ok1_wbytes. apply F2. exact Hy.
    - intros y Hy. apply wbytes_keep. apply F3. exact Hy.
  Qed.
  #[using="a b n bufa bufb H"] Lemma OUT_rp : forall m (V : Z) (rra s0 s1 s2 s3 s4 s5 : word), OUT m -> (usp - IBC_FRAME + 72 <= V)%Z -> (V <= usp)%Z ->
    OUT (rp_frame m V rra s0 s1 s2 s3 s4 s5).
  Proof. intros. unfold rp_frame. repeat (apply OUT_w8; [|unfold IBC_FRAME in *; lia|lia]). assumption. Qed.
  #[using="a b n bufa bufb H"] Lemma cells_OUT : forall m, OUT m -> ibc_cells m.
  Proof.
    intros m F. pose proof (ib_cel _ _ _ _ _ _ _ H) as (C & C1 & C2 & C3 & C4 & C5 & C6). pose proof Hsp. pose proof SB_val. unfold IBC_FRAME in *.
    unfold ibc_cells, cells, cell in *. rewrite !(rdn_OUT_below m) by (first [exact F | cbn; unfold IBC_FRAME; lia]).
    split; [exact C|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|exact C6].
  Qed.
  #[using="a b n bufa bufb H"] Lemma stk8 : forall m x, OUT m -> (usp - IBC_FRAME <= x)%Z -> (x + 8 <= usp)%Z -> store_ok SEGS m (Z_to_bv 64 x) 8 = true.
  Proof.
    intros m x (_ & F2 & _) H1 H2. unfold IBC_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F2. apply (ib_stk _ _ _ _ _ _ _ H). unfold IBC_FRAME. lia.
  Qed.
  #[using="a b n bufa bufb H"] Lemma stk8m : forall m x, (forall y, store_ok SEGS mem y 1 = true -> store_ok SEGS m y 1 = true) ->
    (usp - IBC_FRAME <= x)%Z -> (x + 8 <= usp)%Z -> store_ok SEGS m (Z_to_bv 64 x) 8 = true.
  Proof.
    intros m x F2 H1 H2. unfold IBC_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F2. apply (ib_stk _ _ _ _ _ _ _ H). unfold IBC_FRAME. lia.
  Qed.
  Ltac msdO F D x v Hbase HO :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 x) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                 | apply stk8m; [intros y Hy; repeat apply store_ok1_wbytes; apply (proj1 (proj2 HO)); exact Hy | unfold IBC_FRAME; lia | lia] ]).

  (* [comment removed for export] *)
  #[using="b n bufb H"] Lemma bufa_OUT : forall m, OUT m -> rdn SEGS m (Z_to_bv 64 a) (length bufa) = Some bufa.
  Proof.
    intros m F. pose proof (ib_bufa _ _ _ _ _ _ _ H) as R. pose proof (ib_lena _ _ _ _ _ _ _ H) as L. pose proof Ha64. pose proof Hn. pose proof Hsp.
    destruct (Z.eq_dec n 0) as [N0|N0]; [rewrite N0 in L; destruct bufa; [reflexivity|discriminate L]|].
    pose proof (af_sap _ _ _ _ (ib_fa _ _ _ _ _ _ _ H ltac:(lia))) as AP. unfold IBC_FRAME in *.
    rewrite (rdn_OUT_out m); [exact R|exact F|lia|rewrite L; lia|rewrite L; unfold IBC_FRAME; lia].
  Qed.
  #[using="a n bufa H"] Lemma bufb_OUT : forall m, OUT m -> rdn SEGS m (Z_to_bv 64 b) (length bufb) = Some bufb.
  Proof.
    intros m F. pose proof (ib_bufb _ _ _ _ _ _ _ H) as R. pose proof (ib_lenb _ _ _ _ _ _ _ H) as L. pose proof Hb64. pose proof Hn. pose proof Hsp.
    destruct (Z.eq_dec n 0) as [N0|N0]; [rewrite N0 in L; destruct bufb; [reflexivity|discriminate L]|].
    pose proof (af_sap _ _ _ _ (ib_fb _ _ _ _ _ _ _ H ltac:(lia))) as AP. unfold IBC_FRAME in *.
    rewrite (rdn_OUT_out m); [exact R|exact F|lia|rewrite L; lia|rewrite L; unfold IBC_FRAME; lia].
  Qed.

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.
  Ltac adr c := match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with c by lia end.
  Ltac keep_tac Hr He := repeat (rewrite getr_other by (intros ->; cbn in Hr, He; first [discriminate Hr | discriminate He])).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MIC.
    Variable U : Z.
    Hypothesis HU : (usp - IBC_FRAME + 2264 <= U <= usp)%Z.
    Variables (rfw rfpc : word).
    Hypothesis RFJ : v_jalr rfw 0 = rfpc.
    Variable RES : word -> Prop.
    (* [comment removed for export] *)
    Hypothesis RF : forall regs m,
      OUT m -> getr regs 2 = Z_to_bv 64 (U - 2192) -> getr regs 1 = (0x45114 : word) ->
      getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
      exists regs' m',
        msteps SEGS (mkst regs rfpc m rom) (mkst regs' (0x45114 : word) m' rom)
        /\ RES (getr regs' 10)
        /\ (forall r, sreg r = true -> getr regs' r = getr regs r)
        /\ (forall r, ibc_clob r = false -> r <> 1 -> getr regs' r = getr regs r)
        /\ OUT m' /\ (forall x : word, (U - 2192 <= bv_unsigned x)%Z -> m' x = m x).

    Variable regs0 : bvmap 5 word.
    Variable ra : word.
    Variable m0 : word -> option byte.
    Hypothesis OUT0 : OUT m0.
    Hypothesis Hret : ret_ok ra.
    Hypothesis H01 : getr regs0 1 = ra.
    Hypothesis H02 : getr regs0 2 = Z_to_bv 64 U.
    Hypothesis H011 : getr regs0 11 = rfw.
    Hypothesis H012 : getr regs0 12 = Z_to_bv 64 a.
    Hypothesis H013 : getr regs0 13 = Z_to_bv 64 b.
    Hypothesis H014 : getr regs0 14 = Z_to_bv 64 n.

    #[using="mem a b n bufa bufb H HU"] Lemma HUsp : (0x7fff8000 + 2280 <= U < 2 ^ 64)%Z /\ (usp - 4552 + 2264 <= U <= usp)%Z.
    Proof. pose proof Hsp. pose proof HU. unfold IBC_FRAME in *. lia. Qed.

    (* [comment removed for export] *)
    Definition p13 : word -> option byte :=
      let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (U - o)) (word_to_le_bytes 8 v) in
      w 104%Z (getr regs0 27) (w 96%Z (getr regs0 26) (w 88%Z (getr regs0 25) (w 80%Z (getr regs0 24) (w 72%Z (getr regs0 23)
        (w 64%Z (getr regs0 22) (w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
        (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra m0)))))))))))).
    #[using="a b n bufa bufb H HU OUT0"] Lemma OUT_p13 : OUT p13.
    Proof. pose proof HUsp. unfold p13. repeat (apply OUT_w8; [|unfold IBC_FRAME; lia|lia]). exact OUT0. Qed.

    (* [comment removed for export] *)
    #[using="mem a b n usp bufa bufb H HU"] Lemma p13_above : forall x : word, (U <= bv_unsigned x)%Z -> p13 x = m0 x.
    Proof. intros x Hx. pose proof HUsp. unfold p13. rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia. Qed.
    Definition sfr (m : word -> option byte) : Prop :=
      OUT m /\ (forall x : word, (U - 104 <= bv_unsigned x < U)%Z -> m x = p13 x) /\ (forall x : word, (U <= bv_unsigned x)%Z -> m x = m0 x).
    #[using="a b n bufa bufb H HU OUT0"] Lemma sfr_p13 : sfr p13. Proof. split; [exact OUT_p13|split; [intros; reflexivity|exact p13_above]]. Qed.
    #[using="Type"] Lemma sfr_OUT : forall m, sfr m -> OUT m. Proof. intros m [F _]. exact F. Qed.
    #[using="a b n bufa bufb H HU"] Lemma sfr_w8 : forall m (x : Z) (v : word), sfr m -> (usp - IBC_FRAME <= x)%Z -> (x + 8 <= U - 104)%Z ->
      sfr (wbytes m (Z_to_bv 64 x) (word_to_le_bytes 8 v)).
    Proof.
      intros m x v (F1 & F2 & F3) Hx1 Hx2. pose proof HUsp. unfold IBC_FRAME in *. split; [apply OUT_w8; [exact F1|unfold IBC_FRAME; lia|lia]|split].
      - intros y Hy. rewrite <- (F2 y Hy). apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
      - intros y Hy. rewrite <- (F3 y Hy). apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    Qed.
    #[using="a b n bufa bufb H HU"] Lemma sfr_rp : forall m (rra s0 s1 s2 s3 s4 s5 : word), sfr m -> sfr (rp_frame m (U - 2192) rra s0 s1 s2 s3 s4 s5).
    Proof. intros. pose proof HUsp. unfold rp_frame. repeat (apply sfr_w8; [|unfold IBC_FRAME; lia|lia]). assumption. Qed.
    (* [comment removed for export] *)
    #[using="Type"] Lemma sfr_RF : forall m m', sfr m -> OUT m' -> (forall x : word, (U - 2192 <= bv_unsigned x)%Z -> m' x = m x) -> sfr m'.
    Proof.
      intros m m' (F1 & F2 & F3) O K. split; [exact O|split].
      - intros y Hy. rewrite (K y) by lia. apply F2. exact Hy.
      - intros y Hy. rewrite (K y) by lia. apply F3. exact Hy.
    Qed.

    (* [comment removed for export] *)
    Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
    Ltac rd_slot := pose proof HUsp; unfold p13;
      repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                    | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_ra : rdn SEGS p13 (Z_to_bv 64 (U - 8)) 8 = Some (word_to_le_bytes 8 ra).               Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s0 : rdn SEGS p13 (Z_to_bv 64 (U - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)).   Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s1 : rdn SEGS p13 (Z_to_bv 64 (U - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)).   Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s2 : rdn SEGS p13 (Z_to_bv 64 (U - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s3 : rdn SEGS p13 (Z_to_bv 64 (U - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s4 : rdn SEGS p13 (Z_to_bv 64 (U - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s5 : rdn SEGS p13 (Z_to_bv 64 (U - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s6 : rdn SEGS p13 (Z_to_bv 64 (U - 64)) 8 = Some (word_to_le_bytes 8 (getr regs0 22)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s7 : rdn SEGS p13 (Z_to_bv 64 (U - 72)) 8 = Some (word_to_le_bytes 8 (getr regs0 23)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s8 : rdn SEGS p13 (Z_to_bv 64 (U - 80)) 8 = Some (word_to_le_bytes 8 (getr regs0 24)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s9 : rdn SEGS p13 (Z_to_bv 64 (U - 88)) 8 = Some (word_to_le_bytes 8 (getr regs0 25)).  Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s10 : rdn SEGS p13 (Z_to_bv 64 (U - 96)) 8 = Some (word_to_le_bytes 8 (getr regs0 26)). Proof. rd_slot. Qed.
    #[using="mem a b n usp bufa bufb H HU"] Lemma rd_s11 : rdn SEGS p13 (Z_to_bv 64 (U - 104)) 8 = Some (word_to_le_bytes 8 (getr regs0 27)). Proof. rd_slot. Qed.

    (* [comment removed for export] *)
    Definition keep (regs : bvmap 5 word) : Prop :=
      forall r : reg, ibc_clob r = false -> ekeep r = false -> getr regs r = getr regs0 r.
    (* [comment removed for export] *)
    Definition base (regs : bvmap 5 word) : Prop :=
      getr regs 2 = Z_to_bv 64 (U - 2192) /\ getr regs 8 = Z_to_bv 64 U /\ getr regs 9 = Z_to_bv 64 n
      /\ getr regs 18 = Z_to_bv 64 b /\ getr regs 19 = ra /\ getr regs 20 = Z_to_bv 64 a /\ getr regs 21 = rfw
      /\ getr regs 24 = Z_to_bv 64 0x1436e8 /\ keep regs.
    Ltac base_tac B :=
      let HB := fresh in pose proof B as HB;
      destruct HB as (?B2 & ?B8 & ?B9 & ?B18 & ?B19 & ?B20 & ?B21 & ?B24 & ?BK);
      repeat split;
      [ gr; exact B2 | gr; exact B8 | gr; exact B9 | gr; exact B18 | gr; exact B19 | gr; exact B20 | gr; exact B21 | gr; exact B24
      | intros r Hr He; keep_tac Hr He; apply BK; assumption ].
    #[using="Type"] Lemma k_m65 : v_addi (Z_to_bv 64 0) (-65) = Z_to_bv 64 (2 ^ 64 - 65).
    Proof. apply bv_eq. vm_compute. reflexivity. Qed.

    Ltac msd F D x v Hbase :=
      mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 x) v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                   | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                   | apply stk8; [first [assumption | exact OUT0 | repeat (apply OUT_w8; [|unfold IBC_FRAME; lia|lia]); exact OUT0] | unfold IBC_FRAME; lia | lia] ]).

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    #[using="mem usp bufa bufb H HU OUT0 H01 H02 H011 H012 H013 H014"] Lemma blk_P :
      exists regs,
        msteps SEGS (mkst regs0 (0x44ff4 : word) m0 rom) (mkst regs (0x45068 : word) p13 rom)
        /\ getr regs 2 = Z_to_bv 64 (U - 2192) /\ getr regs 8 = Z_to_bv 64 U /\ getr regs 9 = Z_to_bv 64 n
        /\ getr regs 18 = Z_to_bv 64 b /\ getr regs 19 = ra /\ getr regs 20 = Z_to_bv 64 a /\ getr regs 21 = rfw
        /\ getr regs 24 = Z_to_bv 64 0x1436e8 /\ getr regs 23 = Z_to_bv 64 (U - 2176) /\ keep regs.
    Proof.
      pose proof HUsp. pose proof Ha64. pose proof Hb64. pose proof Hn.
      pose proof (cells_OUT p13 OUT_p13) as (_ & _ & G1 & IM & SM & _).
      eexists. split.
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_44ff4 eq_refl D_44ff4)). rewrite H02. zn.
        msd F_44ff8 D_44ff8 (U - 8)%Z ra H02.
        msd F_44ffc D_44ffc (U - 16)%Z (getr regs0 8) H02.
        msd F_45000 D_45000 (U - 24)%Z (getr regs0 9) H02.
        msd F_45004 D_45004 (U - 32)%Z (getr regs0 18) H02.
        msd F_45008 D_45008 (U - 40)%Z (getr regs0 19) H02.
        msd F_4500c D_4500c (U - 48)%Z (getr regs0 20) H02.
        msd F_45010 D_45010 (U - 56)%Z (getr regs0 21) H02.
        msd F_45014 D_45014 (U - 64)%Z (getr regs0 22) H02.
        msd F_45018 D_45018 (U - 72)%Z (getr regs0 23) H02.
        msd F_4501c D_4501c (U - 80)%Z (getr regs0 24) H02.
        msd F_45020 D_45020 (U - 88)%Z (getr regs0 25) H02.
        msd F_45024 D_45024 (U - 96)%Z (getr regs0 26) H02.
        msd F_45028 D_45028 (U - 104)%Z (getr regs0 27) H02.
        change (wbytes _ _ _) with p13.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4502c eq_refl D_4502c)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45030 eq_refl D_45030)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45034 eq_refl D_45034)). gr. rewrite H01.
        replace (v_addi ra 0) with ra by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45038 eq_refl D_45038)). gr. rewrite H014. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4503c eq_refl D_4503c)). gr. rewrite H013. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45040 eq_refl D_45040)). gr. rewrite H012. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45044 eq_refl D_45044)). gr. rewrite H011.
        replace (v_addi rfw 0) with rfw by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9048) F_45048 eq_refl D_45048);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_4504c D_4504c 0x1436e8%Z G1 H02.
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_45050 eq_refl D_45050);
                     gr; imm_norm; zn; rewrite ?Z.add_0_r; first [exact IM | adr 0x1437e6%Z; exact IM]).
        change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_45054 eq_refl D_45054); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_45058 eq_refl D_45058);
                     gr; imm_norm; zn; rewrite ?Z.add_0_r; first [exact SM | adr 0x1437e7%Z; exact SM]).
        change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4505c eq_refl D_4505c)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45060 eq_refl D_45060)). gr. zn.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_45064 eq_refl D_45064); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
        intros r Hr He. keep_tac Hr He. reflexivity.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    #[using="mem b bufa bufb H"] Lemma afacts : (0 < n)%Z ->
      (8 * (a / 8) <= a < 8 * (a / 8) + 8)%Z /\ (8 * ((a + n - 1) / 8) <= a + n - 1 < 8 * ((a + n - 1) / 8) + 8)%Z
      /\ ((a + n - 1) mod 8 = a + n - 1 - 8 * ((a + n - 1) / 8))%Z
      /\ (SB + (a + n - 1) / 8 + 8 < usp - 4552)%Z /\ (a / 8 <= (a + n - 1) / 8)%Z /\ SB = 0x7fff8000%Z
      /\ (a + n < 2 ^ 47)%Z.
    Proof.
      intros Hn0. pose proof (ib_fa _ _ _ _ _ _ _ H Hn0) as AF. pose proof (af_shd _ _ _ _ AF) as Hshd. unfold IBC_FRAME in Hshd.
      pose proof (af_rng _ _ _ _ AF) as RNG. unfold kLowEnd, kHighBeg, kHighEnd in RNG. pose proof SB_val. pose proof Ha64. pose proof Hn.
      pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
      pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)).
      pose proof (Z.div_le_mono a (a + n - 1) 8 ltac:(lia) ltac:(lia)). lia.
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma blk_A0 : forall regs m, sfr m -> base regs ->
      exists regs',
        msteps SEGS (mkst regs (0x45068 : word) m rom) (mkst regs' (0x45078 : word) m rom)
        /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 65) /\ getr regs' 25 = Z_to_bv 64 (n - 65) /\ getr regs' 10 = getr regs 10 /\ base regs'.
    Proof.
      intros regs m F B. pose proof HUsp. pose proof Ha64. pose proof Hn. pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      eexists. split.
      - mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45068 eq_refl D_45068)). gr. rewrite B20. rewrite v_not_zbv by lia.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_4506c eq_refl D_4506c); gr; rewrite ?B9; br_lt).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45070 eq_refl D_45070)). gr. rewrite B9. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45074 eq_refl D_45074)). rewrite getr_zero. rewrite k_m65.
        apply mst_refl.
      - split; [gr; reflexivity|]. split; [gr; apply (f_equal (Z_to_bv 64)); lia|]. split; [gr; reflexivity|]. base_tac B.
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma blk_AZ : forall regs m, n = 0%Z ->
      getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 25 = Z_to_bv 64 (n - 65) -> getr regs 9 = Z_to_bv 64 n ->
      msteps SEGS (mkst regs (0x45078 : word) m rom) (mkst regs (0x450b8 : word) m rom).
    Proof.
      intros regs m Hn0 H11 H25 H9.
      replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H25 by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_45078 eq_refl D_45078); gr; rewrite ?H11, ?H25; br_lt).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_452dc eq_refl D_452dc); gr; rewrite ?H9, ?getr_zero; br_eq).
      mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_452e0 eq_refl D_452e0)).
      apply mst_refl.
    Qed.

    (* [comment removed for export] *)
    #[using="b bufa bufb H HU"] Lemma rp_pre_a : forall m b1, sfr m -> (65 <= n)%Z ->
      mem (Z_to_bv 64 (SB + (a + n - 1) / 8)) = Some b1 ->
      (bv_unsigned b1 = 0%Z \/ ((a + n - 1) mod 8 < bv_unsigned b1 < 8)%Z) ->
      rpH m a n (U - 2192) b1.
    Proof.
      intros m b1 F Hn65 L1 Hb1. pose proof HUsp. pose proof SB_val. pose proof Ha64. pose proof Hn.
      destruct (afacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (sfr_OUT m F) as (F1 & F2 & F3). pose proof (ib_fa _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      constructor.
      - lia.
      - lia.
      - exact (af_rng _ _ _ _ AF).
      - lia.
      - lia.
      - intros g Hg. rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). apply (af_zg _ _ _ _ AF). lia.
      - rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). exact L1.
      - exact Hb1.
      - intros y Hy. apply F2. apply (ib_stk _ _ _ _ _ _ _ H). unfold IBC_FRAME. lia.
      - exact (proj1 (cells_OUT m (sfr_OUT m F))).
    Qed.

    #[using="bufa bufb H HU"] Lemma blk_AL : forall regs m, sfr m -> (65 <= n)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 25 = Z_to_bv 64 (n - 65) ->
      exists regs' m',
        msteps SEGS (mkst regs (0x45078 : word) m rom) (mkst regs' (0x450b8 : word) m' rom)
        /\ sfr m' /\ getr regs' 25 = Z_to_bv 64 (n - 65) /\ base regs'.
    Proof.
      intros regs m F Hn65 B H11 H25. pose proof HUsp. pose proof Ha64. pose proof Hn.
      pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      destruct (af_last _ _ _ _ (ib_fa _ _ _ _ _ _ _ H ltac:(lia))) as (b1 & L1 & Hb1).
      evar (rr : bvmap 5 word).
      edestruct (as_region_is_poisoned m rom a n (U - 2192) b1 (rp_pre_a m b1 F Hn65 L1 Hb1) rr (0x45498 : word) ret_ok_69048)
        as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
      { eexists. eexists. split; [|split; [|split]].
        - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_45078 eq_refl D_45078); gr; rewrite ?H11, ?H25; br_lt).
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_452dc eq_refl D_452dc); gr; rewrite ?B9, ?getr_zero; br_eq).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45488 eq_refl D_45488)). gr.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4548c eq_refl D_4548c)). gr. rewrite B20. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45490 eq_refl D_45490)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_45494 eq_refl D_45494)). rewrite lit_6904c.
          eapply msteps_trans; [subst rr; exact M1|].
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45498 eq_refl D_45498)). gr. rewrite R10. zn.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4549c eq_refl D_4549c)). gr.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_454a0 eq_refl D_454a0); gr; rewrite ?R10, ?getr_zero; br_eq).
          apply mst_refl.
        - apply sfr_rp. exact F.
        - subst rr. gr. rewrite (K1 25) by reflexivity. gr. exact H25.
        - subst rr. split; [gr; exact R2|].
          split; [gr; rewrite (K1 8) by reflexivity; gr; exact B8|]. split; [gr; rewrite (K1 9) by reflexivity; gr; exact B9|].
          split; [gr; rewrite (K1 18) by reflexivity; gr; exact B18|]. split; [gr; rewrite (K1 19) by reflexivity; gr; exact B19|].
          split; [gr; rewrite (K1 20) by reflexivity; gr; exact B20|]. split; [gr; rewrite (K1 21) by reflexivity; gr; exact B21|].
          split; [gr; rewrite (K1 24) by reflexivity; gr; exact B24|].
          intros r Hr He. keep_tac Hr He. rewrite (K1 r (rp_clob_ibc r Hr)). keep_tac Hr He. apply BK; assumption. }
      all: subst rr; gr; try reflexivity; try assumption.
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma blk_AQ1 : forall regs m, sfr m -> (1 <= n <= 64)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 25 = Z_to_bv 64 (n - 65) ->
      exists regs' (w : word),
        msteps SEGS (mkst regs (0x45078 : word) m rom) (mkst regs' (0x450b4 : word) m rom)
        /\ getr regs' 11 = Z_to_bv 64 (SB + a / 8) /\ getr regs' 12 = Z_to_bv 64 (SB + (a + n - 1) / 8)
        /\ getr regs' 13 = Z_to_bv 64 (a + n - 1) /\ getr regs' 14 = w /\ getr regs' 10 = getr regs 10 /\ getr regs' 25 = getr regs 25 /\ base regs'.
    Proof.
      intros regs m F Hn64 B H11 H25. pose proof HUsp as HU'. pose proof Ha64 as Hx64. pose proof Hn.
      pose proof H25 as H25raw.
      replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H25 by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
      pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      destruct (afacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (cells_OUT m (sfr_OUT m F)) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
      pose proof (ib_fa _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      destruct (af_w1 _ _ _ _ AF) as [w1 W1]. destruct (af_w2 _ _ _ _ AF) as [w2 W2].
      pose proof (Z.div_mod (SB + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + a / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SB + (a + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (a + n - 1) / 8) 8 ltac:(lia)).
      assert (W1c : cell m ((SB + a / 8) / 8 * 8) (bv_unsigned w1)).
      { unfold cell. rewrite zbv_self. rewrite (rdn_OUT_below m) by (first [exact (sfr_OUT m F) | cbn; unfold IBC_FRAME; (ltac2:(LK.k [@Hn64; @Hx64; @D0; @D1; @HSB; @H1; @H2; @Dshd]); lia)]). exact W1. }
      assert (W2c : cell m ((SB + (a + n - 1) / 8) / 8 * 8) (bv_unsigned w2)).
      { unfold cell. rewrite zbv_self. rewrite (rdn_OUT_below m) by (first [exact (sfr_OUT m F) | cbn; unfold IBC_FRAME; lia]). exact W2. }
      eexists. eexists. split.
      - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_45078 eq_refl D_45078); gr; rewrite ?H11, ?H25; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa907c) F_4507c eq_refl D_4507c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_45080 D_45080 0xb1bb8%Z C1 B20.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_45084 eq_refl D_45084)). gr. rewrite B20, B9, v_add_zbv by lia.
        mld F_45088 D_45088 SB C2 B20.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_4508c eq_refl D_4508c)). gr. rewrite B20, (v_srli_3 a) by lia.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45090 eq_refl D_45090)). gr. zn.
        replace (a + n + -1)%Z with (a + n - 1)%Z by lia.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_45094 eq_refl D_45094)). gr. rewrite (v_srli_3 (a + n - 1)) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_45098 eq_refl D_45098)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hx64; @HSB; @Hn64; @D0; @HxK]); lia).
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_4509c eq_refl D_4509c)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hx64; @HSB; @Hn64; @D0; @D1; @DM; @HxK]); lia).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_450a0 eq_refl D_450a0)). gr. rewrite v_andi_m8 by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_450a4 eq_refl D_450a4)). gr. rewrite v_andi_m8 by lia.
        mld F_450a8 D_450a8 (bv_unsigned w1) W1c B20.
        mld F_450ac D_450ac (bv_unsigned w2) W2c B20.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_450b0 eq_refl D_450b0)). gr.
        apply mst_refl.
      - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
        split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B.
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma a_loop : forall (k : nat) regs m (g : Z), sfr m -> (1 <= n <= 64)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (SB + g) -> getr regs 12 = Z_to_bv 64 (SB + (a + n - 1) / 8) -> getr regs 13 = Z_to_bv 64 0 ->
      (a / 8 <= g < (a + n - 1) / 8)%Z -> Z.of_nat k = ((a + n - 1) / 8 - g)%Z ->
      exists regs',
        msteps SEGS (mkst regs (0x45470 : word) m rom) (mkst regs' (0x45480 : word) m rom)
        /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 10 = getr regs 10 /\ getr regs' 25 = getr regs 25 /\ base regs'.
    Proof.
      pose proof HUsp as HU'. pose proof Ha64 as Hx64. pose proof Hn.
      induction k as [|k IH]; intros regs m g F Hn64 B H11 H12 H13 Hg Hk; [lia|].
      destruct (afacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (ib_fa _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
      { apply rdn1. rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). apply (af_zg _ _ _ _ AF). lia. }
      destruct (Z.eq_dec (g + 1) ((a + n - 1) / 8)) as [Heq | Hne].
      - eexists. split; [|split; [|split; [|split]]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_45470 eq_refl D_45470);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45474 eq_refl D_45474)). gr. rewrite H11. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45478 eq_refl D_45478)). gr. rewrite H13, v_or_zero.
          mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_4547c eq_refl D_4547c); gr; rewrite ?H12; br_eq).
          apply mst_refl.
        + gr. reflexivity.
        + gr. reflexivity.
        + gr. reflexivity.
        + base_tac B.
      - evar (rr : bvmap 5 word).
        edestruct (IH rr m (g + 1)%Z F Hn64) as (r2 & M2 & R13 & R10 & R25 & B2'); cycle -1.
        { exists r2. split; [|split; [|split; [|split]]].
          + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_45470 eq_refl D_45470);
                         gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
            change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45474 eq_refl D_45474)). gr. rewrite H11. zn.
            mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45478 eq_refl D_45478)). gr. rewrite H13, v_or_zero.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_4547c eq_refl D_4547c); gr; rewrite ?H12; br_eq).
            subst rr. exact M2.
          + exact R13.
          + rewrite R10. subst rr. gr. reflexivity.
          + rewrite R25. subst rr. gr. reflexivity.
          + exact B2'. }
        all: subst rr; gr; try reflexivity; try assumption; try lia.
        { base_tac B. }
        apply (f_equal (Z_to_bv 64)). lia.
    Qed.

    #[using="bufa bufb H HU"] Lemma blk_AQ2 : forall regs m, sfr m -> (1 <= n <= 64)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (SB + a / 8) -> getr regs 12 = Z_to_bv 64 (SB + (a + n - 1) / 8) -> getr regs 13 = Z_to_bv 64 (a + n - 1) ->
      exists regs',
        msteps SEGS (mkst regs (0x45454 : word) m rom) (mkst regs' (0x450b8 : word) m rom)
        /\ getr regs' 10 = getr regs 10 /\ getr regs' 25 = getr regs 25 /\ base regs'.
    Proof.
      intros regs m F Hn64 B H11 H12 H13. pose proof HUsp as HU'. pose proof Ha64 as Hx64. pose proof Hn.
      destruct (afacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (ib_fa _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      destruct (af_last _ _ _ _ AF) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
      assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (a + n - 1) / 8)) 1 = Some [b1]).
      { apply rdn1. rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). exact L1. }
      assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
      assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (T : exists regs1, msteps SEGS (mkst regs (0x45454 : word) m rom) (mkst regs1 (0x4546c : word) m rom)
                   /\ getr regs1 13 = Z_to_bv 64 0 /\ getr regs1 11 = getr regs 11 /\ getr regs1 12 = getr regs 12
                   /\ getr regs1 10 = getr regs 10 /\ getr regs1 25 = getr regs 25 /\ base regs1).
      { destruct Hb1 as [Hz | Hpart].
        - eexists. split.
          + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_45454 eq_refl D_45454);
                         gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
            unfold v_lb. rewrite Hsg, Hz.
            mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45458 eq_refl D_45458)). gr. rewrite H13, v_andi_7 by lia.
            mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_4545c eq_refl D_4545c)). gr. rewrite getr_zero.
            unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
            mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_45460 eq_refl D_45460)). gr.
            unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
            mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45464 eq_refl D_45464)). gr.
            mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_45468 eq_refl D_45468)). gr. rewrite AND0.
            apply mst_refl.
          + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B.
        - eexists. split.
          + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_45454 eq_refl D_45454);
                         gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
            unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
            mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45458 eq_refl D_45458)). gr. rewrite H13, v_andi_7 by lia.
            mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_4545c eq_refl D_4545c)). gr. rewrite getr_zero.
            unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
            mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_45460 eq_refl D_45460)). gr.
            unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
            mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45464 eq_refl D_45464)). gr.
            mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_45468 eq_refl D_45468)). gr. rewrite AND1.
            apply mst_refl.
          + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B. }
      destruct T as (q1 & M1 & A13 & A11 & A12 & A10 & A25 & B1).
      destruct (Z.eq_dec (a / 8) ((a + n - 1) / 8)) as [Heq | Hne].
      - eexists. split; [|split; [|split]].
        + eapply msteps_trans; [exact M1|].
          mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_4546c eq_refl D_4546c); gr; rewrite ?A11, ?A12, ?H11, ?H12; br_lt).
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45480 eq_refl D_45480)). gr. rewrite A13, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45484 eq_refl D_45484); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + gr. exact A10.
        + gr. exact A25.
        + base_tac B1.
      - evar (rr : bvmap 5 word).
        edestruct (a_loop (Z.to_nat ((a + n - 1) / 8 - a / 8)) rr m (a / 8) F Hn64) as (r2 & M2 & R13 & R10 & R25 & B2'); cycle -1.
        { eexists. split; [|split; [|split]].
          + eapply msteps_trans; [exact M1|].
            mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_4546c eq_refl D_4546c); gr; rewrite ?A11, ?A12, ?H11, ?H12; br_lt).
            eapply msteps_trans; [subst rr; exact M2|].
            mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45480 eq_refl D_45480)). rewrite R13, ANDI0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45484 eq_refl D_45484); gr; rewrite ?getr_zero; br_eq).
            apply mst_refl.
          + gr. rewrite R10. subst rr. exact A10.
          + gr. rewrite R25. subst rr. exact A25.
          + base_tac B2'. }
        all: subst rr; try assumption; try lia.
        { rewrite A11. exact H11. } { rewrite A12. exact H12. }
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma blk_CA : forall regs m, sfr m -> base regs -> 
      exists regs' m',
        msteps SEGS (mkst regs (0x45068 : word) m rom) (mkst regs' (0x450b8 : word) m' rom)
        /\ sfr m' /\ getr regs' 25 = Z_to_bv 64 (n - 65) /\ base regs'.
    Proof.
      intros regs m F B. pose proof Hn.
      destruct (blk_A0 regs m F B) as (q0 & M0 & Q11 & Q25 & Q10 & B0').
      pose proof B0' as (_ & _ & B9' & _).
      destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
      - exists q0, m. split; [|split; [exact F|split; [exact Q25|];  exact B0']].
        eapply msteps_trans; [exact M0|]. apply (blk_AZ q0 m Hn0 Q11 Q25 B9').
      - destruct (Z.lt_ge_cases n 65) as [Hsmall | Hbig].
        + destruct (blk_AQ1 q0 m F ltac:(lia) B0' Q11 Q25) as (q1 & w & M1 & A11 & A12 & A13 & A14 & A10 & A25 & B1).
          pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
          destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
          * exists q1, m. split; [|split; [exact F|split; [rewrite A25; exact Q25|];  exact B1]].
            eapply msteps_trans; [exact M0|]. eapply msteps_trans; [exact M1|].
            mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_450b4 eq_refl D_450b4); gr; rewrite ?A14, ?getr_zero; br_eq).
            apply mst_refl.
          * assert (NZu : bv_unsigned w <> 0%Z) by (intros E0; apply NZ; rewrite <- (zbv_self w), E0; reflexivity).
            destruct (blk_AQ2 q1 m F ltac:(lia) B1 A11 A12 A13) as (q2 & M2 & C10 & C25 & B2').
            exists q2, m. split; [|split; [exact F|split; [rewrite C25, A25; exact Q25|];  exact B2']].
            eapply msteps_trans; [exact M0|]. eapply msteps_trans; [exact M1|].
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_450b4 eq_refl D_450b4); gr; rewrite ?A14, ?getr_zero;
                         rewrite <- (zbv_self w); br_eq).
            exact M2.
        + destruct (blk_AL q0 m F Hbig B0' Q11 Q25) as (q1 & m1 & M1 & F1 & L25 & B1).
          exists q1, m1. split; [|split; [exact F1|split; [exact L25|];  exact B1]].
          eapply msteps_trans; [exact M0|]. exact M1.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    #[using="mem a bufa bufb H"] Lemma bfacts : (0 < n)%Z ->
      (8 * (b / 8) <= b < 8 * (b / 8) + 8)%Z /\ (8 * ((b + n - 1) / 8) <= b + n - 1 < 8 * ((b + n - 1) / 8) + 8)%Z
      /\ ((b + n - 1) mod 8 = b + n - 1 - 8 * ((b + n - 1) / 8))%Z
      /\ (SB + (b + n - 1) / 8 + 8 < usp - 4552)%Z /\ (b / 8 <= (b + n - 1) / 8)%Z /\ SB = 0x7fff8000%Z
      /\ (b + n < 2 ^ 47)%Z.
    Proof.
      intros Hn0. pose proof (ib_fb _ _ _ _ _ _ _ H Hn0) as AF. pose proof (af_shd _ _ _ _ AF) as Hshd. unfold IBC_FRAME in Hshd.
      pose proof (af_rng _ _ _ _ AF) as RNG. unfold kLowEnd, kHighBeg, kHighEnd in RNG. pose proof SB_val. pose proof Hb64. pose proof Hn.
      pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
      pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)).
      pose proof (Z.div_le_mono b (b + n - 1) 8 ltac:(lia) ltac:(lia)). lia.
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma blk_B0 : forall regs m, sfr m -> base regs -> getr regs 25 = Z_to_bv 64 (n - 65) ->
      exists regs',
        msteps SEGS (mkst regs (0x450b8 : word) m rom) (mkst regs' (0x450c4 : word) m rom)
        /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 65) /\ getr regs' 25 = Z_to_bv 64 (n - 65) /\ getr regs' 10 = getr regs 10 /\ base regs'.
    Proof.
      intros regs m F B H25in. pose proof HUsp. pose proof Hb64. pose proof Hn. pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      eexists. split.
      - mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_450b8 eq_refl D_450b8)). gr. rewrite B18. rewrite v_not_zbv by lia.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_450bc eq_refl D_450bc); gr; rewrite ?B9; br_lt).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_450c0 eq_refl D_450c0)). rewrite getr_zero. rewrite k_m65.
        apply mst_refl.
      - split; [gr; reflexivity|]. split; [gr; exact H25in|]. split; [gr; reflexivity|]. base_tac B.
    Qed.

    (* [comment removed for export] *)
    #[using="Type"] Lemma blk_BZ : forall regs m, n = 0%Z ->
      getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 25 = Z_to_bv 64 (n - 65) -> getr regs 9 = Z_to_bv 64 n ->
      msteps SEGS (mkst regs (0x450c4 : word) m rom) (mkst regs (0x45104 : word) m rom).
    Proof.
      intros regs m Hn0 H11 H25 H9.
      replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H25 by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_450c4 eq_refl D_450c4); gr; rewrite ?H11, ?H25; br_lt).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_45350 eq_refl D_45350); gr; rewrite ?H9, ?getr_zero; br_eq).
      mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_45354 eq_refl D_45354)).
      apply mst_refl.
    Qed.

    (* [comment removed for export] *)
    #[using="a bufa bufb H HU"] Lemma rp_pre_b : forall m b1, sfr m -> (65 <= n)%Z ->
      mem (Z_to_bv 64 (SB + (b + n - 1) / 8)) = Some b1 ->
      (bv_unsigned b1 = 0%Z \/ ((b + n - 1) mod 8 < bv_unsigned b1 < 8)%Z) ->
      rpH m b n (U - 2192) b1.
    Proof.
      intros m b1 F Hn65 L1 Hb1. pose proof HUsp. pose proof SB_val. pose proof Hb64. pose proof Hn.
      destruct (bfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (sfr_OUT m F) as (F1 & F2 & F3). pose proof (ib_fb _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      constructor.
      - lia.
      - lia.
      - exact (af_rng _ _ _ _ AF).
      - lia.
      - lia.
      - intros g Hg. rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). apply (af_zg _ _ _ _ AF). lia.
      - rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). exact L1.
      - exact Hb1.
      - intros y Hy. apply F2. apply (ib_stk _ _ _ _ _ _ _ H). unfold IBC_FRAME. lia.
      - exact (proj1 (cells_OUT m (sfr_OUT m F))).
    Qed.

    #[using="bufa bufb H HU"] Lemma blk_BL : forall regs m, sfr m -> (65 <= n)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 25 = Z_to_bv 64 (n - 65) ->
      exists regs' m',
        msteps SEGS (mkst regs (0x450c4 : word) m rom) (mkst regs' (0x45104 : word) m' rom)
        /\ sfr m' /\  base regs'.
    Proof.
      intros regs m F Hn65 B H11 H25. pose proof HUsp. pose proof Hb64. pose proof Hn.
      pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      destruct (af_last _ _ _ _ (ib_fb _ _ _ _ _ _ _ H ltac:(lia))) as (b1 & L1 & Hb1).
      evar (rr : bvmap 5 word).
      edestruct (as_region_is_poisoned m rom b n (U - 2192) b1 (rp_pre_b m b1 F Hn65 L1 Hb1) rr (0x455a4 : word) ret_ok_69154)
        as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
      { eexists. eexists. split; [|split].
        - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_450c4 eq_refl D_450c4); gr; rewrite ?H11, ?H25; br_lt).
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45350 eq_refl D_45350); gr; rewrite ?B9, ?getr_zero; br_eq).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45594 eq_refl D_45594)). gr.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45598 eq_refl D_45598)). gr. rewrite B18. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4559c eq_refl D_4559c)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_455a0 eq_refl D_455a0)). rewrite lit_69158.
          eapply msteps_trans; [subst rr; exact M1|].
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_455a4 eq_refl D_455a4)). gr. rewrite R10. zn.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_455a8 eq_refl D_455a8); gr; rewrite ?R10, ?getr_zero; br_eq).
          apply mst_refl.
        - apply sfr_rp. exact F.
        - subst rr. split; [gr; exact R2|].
          split; [gr; rewrite (K1 8) by reflexivity; gr; exact B8|]. split; [gr; rewrite (K1 9) by reflexivity; gr; exact B9|].
          split; [gr; rewrite (K1 18) by reflexivity; gr; exact B18|]. split; [gr; rewrite (K1 19) by reflexivity; gr; exact B19|].
          split; [gr; rewrite (K1 20) by reflexivity; gr; exact B20|]. split; [gr; rewrite (K1 21) by reflexivity; gr; exact B21|].
          split; [gr; rewrite (K1 24) by reflexivity; gr; exact B24|].
          intros r Hr He. keep_tac Hr He. rewrite (K1 r (rp_clob_ibc r Hr)). keep_tac Hr He. apply BK; assumption. }
      all: subst rr; gr; try reflexivity; try assumption.
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma blk_BQ1 : forall regs m, sfr m -> (1 <= n <= 64)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (2 ^ 64 - 65) -> getr regs 25 = Z_to_bv 64 (n - 65) ->
      exists regs' (w : word),
        msteps SEGS (mkst regs (0x450c4 : word) m rom) (mkst regs' (0x45100 : word) m rom)
        /\ getr regs' 11 = Z_to_bv 64 (SB + b / 8) /\ getr regs' 12 = Z_to_bv 64 (SB + (b + n - 1) / 8)
        /\ getr regs' 13 = Z_to_bv 64 (b + n - 1) /\ getr regs' 14 = w /\ getr regs' 10 = getr regs 10 /\ getr regs' 25 = getr regs 25 /\ base regs'.
    Proof.
      intros regs m F Hn64 B H11 H25. pose proof HUsp as HU'. pose proof Hb64 as Hx64. pose proof Hn.
      pose proof H25 as H25raw.
      replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H25 by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
      pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      destruct (bfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (cells_OUT m (sfr_OUT m F)) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
      pose proof (ib_fb _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      destruct (af_w1 _ _ _ _ AF) as [w1 W1]. destruct (af_w2 _ _ _ _ AF) as [w2 W2].
      pose proof (Z.div_mod (SB + b / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + b / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SB + (b + n - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (b + n - 1) / 8) 8 ltac:(lia)).
      assert (W1c : cell m ((SB + b / 8) / 8 * 8) (bv_unsigned w1)).
      { unfold cell. rewrite zbv_self. rewrite (rdn_OUT_below m) by (first [exact (sfr_OUT m F) | cbn; unfold IBC_FRAME; lia]). exact W1. }
      assert (W2c : cell m ((SB + (b + n - 1) / 8) / 8 * 8) (bv_unsigned w2)).
      { unfold cell. rewrite zbv_self. rewrite (rdn_OUT_below m) by (first [exact (sfr_OUT m F) | cbn; unfold IBC_FRAME; lia]). exact W2. }
      eexists. eexists. split.
      - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_450c4 eq_refl D_450c4); gr; rewrite ?H11, ?H25; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa90c8) F_450c8 eq_refl D_450c8);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_450cc D_450cc 0xb1bb8%Z C1 B18.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_450d0 eq_refl D_450d0)). gr. rewrite B18, B9, v_add_zbv by lia.
        mld F_450d4 D_450d4 SB C2 B18.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_450d8 eq_refl D_450d8)). gr. rewrite B18, (v_srli_3 b) by lia.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_450dc eq_refl D_450dc)). gr. zn.
        replace (b + n + -1)%Z with (b + n - 1)%Z by lia.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_450e0 eq_refl D_450e0)). gr. rewrite (v_srli_3 (b + n - 1)) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_450e4 eq_refl D_450e4)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_450e8 eq_refl D_450e8)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_450ec eq_refl D_450ec)). gr. rewrite v_andi_m8 by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_450f0 eq_refl D_450f0)). gr. rewrite v_andi_m8 by lia.
        mld F_450f4 D_450f4 (bv_unsigned w1) W1c B18.
        mld F_450f8 D_450f8 (bv_unsigned w2) W2c B18.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_450fc eq_refl D_450fc)). gr.
        apply mst_refl.
      - split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
        split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B.
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma b_loop : forall (k : nat) regs m (g : Z), sfr m -> (1 <= n <= 64)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (SB + g) -> getr regs 12 = Z_to_bv 64 (SB + (b + n - 1) / 8) -> getr regs 13 = Z_to_bv 64 0 ->
      (b / 8 <= g < (b + n - 1) / 8)%Z -> Z.of_nat k = ((b + n - 1) / 8 - g)%Z ->
      exists regs',
        msteps SEGS (mkst regs (0x4557c : word) m rom) (mkst regs' (0x4558c : word) m rom)
        /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 10 = getr regs 10 /\ getr regs' 25 = getr regs 25 /\ base regs'.
    Proof.
      pose proof HUsp as HU'. pose proof Hb64 as Hx64. pose proof Hn.
      induction k as [|k IH]; intros regs m g F Hn64 B H11 H12 H13 Hg Hk; [lia|].
      destruct (bfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (ib_fb _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
      { apply rdn1. rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). apply (af_zg _ _ _ _ AF). lia. }
      destruct (Z.eq_dec (g + 1) ((b + n - 1) / 8)) as [Heq | Hne].
      - eexists. split; [|split; [|split; [|split]]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_4557c eq_refl D_4557c);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45580 eq_refl D_45580)). gr. rewrite H11. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45584 eq_refl D_45584)). gr. rewrite H13, v_or_zero.
          mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_45588 eq_refl D_45588); gr; rewrite ?H12; br_eq).
          apply mst_refl.
        + gr. reflexivity.
        + gr. reflexivity.
        + gr. reflexivity.
        + base_tac B.
      - evar (rr : bvmap 5 word).
        edestruct (IH rr m (g + 1)%Z F Hn64) as (r2 & M2 & R13 & R10 & R25 & B2'); cycle -1.
        { exists r2. split; [|split; [|split; [|split]]].
          + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_4557c eq_refl D_4557c);
                         gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
            change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
            mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45580 eq_refl D_45580)). gr. rewrite H11. zn.
            mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45584 eq_refl D_45584)). gr. rewrite H13, v_or_zero.
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45588 eq_refl D_45588); gr; rewrite ?H12; br_eq).
            subst rr. exact M2.
          + exact R13.
          + rewrite R10. subst rr. gr. reflexivity.
          + rewrite R25. subst rr. gr. reflexivity.
          + exact B2'. }
        all: subst rr; gr; try reflexivity; try assumption; try lia.
        { base_tac B. }
        apply (f_equal (Z_to_bv 64)). lia.
    Qed.

    #[using="bufa bufb H HU"] Lemma blk_BQ2 : forall regs m, sfr m -> (1 <= n <= 64)%Z -> base regs ->
      getr regs 11 = Z_to_bv 64 (SB + b / 8) -> getr regs 12 = Z_to_bv 64 (SB + (b + n - 1) / 8) -> getr regs 13 = Z_to_bv 64 (b + n - 1) ->
      exists regs',
        msteps SEGS (mkst regs (0x45560 : word) m rom) (mkst regs' (0x45104 : word) m rom)
        /\ getr regs' 10 = getr regs 10 /\ getr regs' 25 = getr regs 25 /\ base regs'.
    Proof.
      intros regs m F Hn64 B H11 H12 H13. pose proof HUsp as HU'. pose proof Hb64 as Hx64. pose proof Hn.
      destruct (bfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB & HxK).
      pose proof (ib_fb _ _ _ _ _ _ _ H ltac:(lia)) as AF.
      destruct (af_last _ _ _ _ AF) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
      assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (b + n - 1) / 8)) 1 = Some [b1]).
      { apply rdn1. rewrite (OUT_below m) by (first [exact (sfr_OUT m F) | rewrite zbv_u by lia; unfold IBC_FRAME; lia]). exact L1. }
      assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
      assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      assert (T : exists regs1, msteps SEGS (mkst regs (0x45560 : word) m rom) (mkst regs1 (0x45578 : word) m rom)
                   /\ getr regs1 13 = Z_to_bv 64 0 /\ getr regs1 11 = getr regs 11 /\ getr regs1 12 = getr regs 12
                   /\ getr regs1 10 = getr regs 10 /\ getr regs1 25 = getr regs 25 /\ base regs1).
      { destruct Hb1 as [Hz | Hpart].
        - eexists. split.
          + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_45560 eq_refl D_45560);
                         gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
            unfold v_lb. rewrite Hsg, Hz.
            mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45564 eq_refl D_45564)). gr. rewrite H13, v_andi_7 by lia.
            mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_45568 eq_refl D_45568)). gr. rewrite getr_zero.
            unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
            mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_4556c eq_refl D_4556c)). gr.
            unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
            mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45570 eq_refl D_45570)). gr.
            mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_45574 eq_refl D_45574)). gr. rewrite AND0.
            apply mst_refl.
          + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B.
        - eexists. split.
          + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_45560 eq_refl D_45560);
                         gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
            unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
            mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45564 eq_refl D_45564)). gr. rewrite H13, v_andi_7 by lia.
            mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_45568 eq_refl D_45568)). gr. rewrite getr_zero.
            unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
            mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_4556c eq_refl D_4556c)). gr.
            unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
            mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45570 eq_refl D_45570)). gr.
            mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_45574 eq_refl D_45574)). gr. rewrite AND1.
            apply mst_refl.
          + split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. base_tac B. }
      destruct T as (q1 & M1 & A13 & A11 & A12 & A10 & A25 & B1).
      destruct (Z.eq_dec (b / 8) ((b + n - 1) / 8)) as [Heq | Hne].
      - eexists. split; [|split; [|split]].
        + eapply msteps_trans; [exact M1|].
          mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_45578 eq_refl D_45578); gr; rewrite ?A11, ?A12, ?H11, ?H12; br_lt).
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_4558c eq_refl D_4558c)). gr. rewrite A13, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45590 eq_refl D_45590); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + gr. exact A10.
        + gr. exact A25.
        + base_tac B1.
      - evar (rr : bvmap 5 word).
        edestruct (b_loop (Z.to_nat ((b + n - 1) / 8 - b / 8)) rr m (b / 8) F Hn64) as (r2 & M2 & R13 & R10 & R25 & B2'); cycle -1.
        { eexists. split; [|split; [|split]].
          + eapply msteps_trans; [exact M1|].
            mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_45578 eq_refl D_45578); gr; rewrite ?A11, ?A12, ?H11, ?H12; br_lt).
            eapply msteps_trans; [subst rr; exact M2|].
            mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_4558c eq_refl D_4558c)). rewrite R13, ANDI0.
            mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45590 eq_refl D_45590); gr; rewrite ?getr_zero; br_eq).
            apply mst_refl.
          + gr. rewrite R10. subst rr. exact A10.
          + gr. rewrite R25. subst rr. exact A25.
          + base_tac B2'. }
        all: subst rr; try assumption; try lia.
        { rewrite A11. exact H11. } { rewrite A12. exact H12. }
    Qed.

    (* [comment removed for export] *)
    #[using="bufa bufb H HU"] Lemma blk_CB : forall regs m, sfr m -> base regs ->  getr regs 25 = Z_to_bv 64 (n - 65) ->
      exists regs' m',
        msteps SEGS (mkst regs (0x450b8 : word) m rom) (mkst regs' (0x45104 : word) m' rom)
        /\ sfr m' /\  base regs'.
    Proof.
      intros regs m F B H25in. pose proof Hn.
      destruct (blk_B0 regs m F B H25in) as (q0 & M0 & Q11 & Q25 & Q10 & B0').
      pose proof B0' as (_ & _ & B9' & _).
      destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
      - exists q0, m. split; [|split; [exact F| exact B0']].
        eapply msteps_trans; [exact M0|]. apply (blk_BZ q0 m Hn0 Q11 Q25 B9').
      - destruct (Z.lt_ge_cases n 65) as [Hsmall | Hbig].
        + destruct (blk_BQ1 q0 m F ltac:(lia) B0' Q11 Q25) as (q1 & w & M1 & A11 & A12 & A13 & A14 & A10 & A25 & B1).
          pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
          destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
          * exists q1, m. split; [|split; [exact F| exact B1]].
            eapply msteps_trans; [exact M0|]. eapply msteps_trans; [exact M1|].
            mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_45100 eq_refl D_45100); gr; rewrite ?A14, ?getr_zero; br_eq).
            apply mst_refl.
          * assert (NZu : bv_unsigned w <> 0%Z) by (intros E0; apply NZ; rewrite <- (zbv_self w), E0; reflexivity).
            destruct (blk_BQ2 q1 m F ltac:(lia) B1 A11 A12 A13) as (q2 & M2 & C10 & C25 & B2').
            exists q2, m. split; [|split; [exact F| exact B2']].
            eapply msteps_trans; [exact M0|]. eapply msteps_trans; [exact M1|].
            mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45100 eq_refl D_45100); gr; rewrite ?A14, ?getr_zero;
                         rewrite <- (zbv_self w); br_eq).
            exact M2.
        + destruct (blk_BL q0 m F Hbig B0' Q11 Q25) as (q1 & m1 & M1 & F1 &  B1).
          exists q1, m1. split; [|split; [exact F1| exact B1]].
          eapply msteps_trans; [exact M0|]. exact M1.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    #[using="bufa bufb H HU rfpc RFJ RF"] Lemma blk_CALL : forall regs m, sfr m -> base regs ->
      exists regs' m',
        msteps SEGS (mkst regs (0x45104 : word) m rom) (mkst regs' (0x451fc : word) m' rom)
        /\ sfr m' /\ RES (getr regs' 21) /\ getr regs' 2 = Z_to_bv 64 (U - 2192) /\ getr regs' 19 = ra /\ keep regs'.
    Proof.
      intros regs m F B. pose proof HUsp. pose proof Ha64. pose proof Hb64. pose proof Hn.
      pose proof B as (B2 & B8 & B9 & B18 & B19 & B20 & B21 & B24 & BK).
      evar (rr : bvmap 5 word).
      edestruct (RF rr m (sfr_OUT m F)) as (r1 & m1 & M1 & R1 & SK & CK & O1 & K1); cycle -1.
      { eexists. eexists. split; [|split; [|split; [|split; [|split]]]].
        - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45104 eq_refl D_45104)). gr. rewrite B20. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45108 eq_refl D_45108)). gr. rewrite B18. zn. rewrite ?Z.add_0_r.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4510c eq_refl D_4510c)). gr. rewrite B9. zn. rewrite ?Z.add_0_r.
          mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ rfw F_45110 eq_refl D_45110); [reflexivity | gr; exact B21]).
          rewrite lit_68cc8, RFJ.
          eapply msteps_trans; [subst rr; exact M1|].
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45114 eq_refl D_45114)). gr.
          replace (v_addi (getr r1 10) 0) with (getr r1 10) by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
          mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_45118 eq_refl D_45118)).
          apply mst_refl.
        - exact (sfr_RF m m1 F O1 K1).
        - gr. exact R1.
        - subst rr. gr. rewrite (SK 2) by reflexivity. gr. exact B2.
        - subst rr. gr. rewrite (SK 19) by reflexivity. gr. exact B19.
        - subst rr. intros r Hr He. keep_tac Hr He. rewrite (CK r Hr) by (intros ->; cbn in He; discriminate He). keep_tac Hr He. apply BK; assumption. }
      all: subst rr; gr; try reflexivity; try assumption.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac mld2 F D v Hrd Hbase :=
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                   [ gr; rewrite ?Hbase; imm_norm; zn;
                     match goal with |- rdn _ _ (Z_to_bv 64 ?x) 8 = _ =>
                       match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                         replace x with c by lia end end; exact Hrd
                   | apply bytes_le_to_Z_8 ]).

    #[using="a b n bufa bufb H HU Hret H01 H02"] Lemma blk_E : forall regs mF, sfr mF -> getr regs 2 = Z_to_bv 64 (U - 2192) -> getr regs 19 = ra -> keep regs ->
      exists regs',
        msteps SEGS (mkst regs (0x451fc : word) mF rom) (mkst regs' ra mF rom)
        /\ getr regs' 10 = getr regs 21
        /\ getr regs' 2 = Z_to_bv 64 U /\ getr regs' 1 = ra
        /\ (forall r, ibc_clob r = false -> getr regs' r = getr regs0 r).
    Proof.
      intros regs mF F B2 B19 BK. pose proof HUsp. pose proof Ha64. pose proof Hb64. pose proof Hn.
      pose proof F as (F1 & F2 & F3).
      assert (HF : forall x, (U - 104 <= x)%Z -> (x + 8 <= U)%Z -> rdn SEGS mF (Z_to_bv 64 x) 8 = rdn SEGS p13 (Z_to_bv 64 x) 8).
      { intros x Hx1 Hx2. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros y Hy. rewrite zbv_u in Hy by lia. cbn in Hy. apply F2. lia. }
      pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18. pose proof rd_s3 as RD19.
      pose proof rd_s4 as RD20. pose proof rd_s5 as RD21. pose proof rd_s6 as RD22. pose proof rd_s7 as RD23. pose proof rd_s8 as RD24.
      pose proof rd_s9 as RD25. pose proof rd_s10 as RD26. pose proof rd_s11 as RD27.
      rewrite <- HF in RD1, RD8, RD9, RD18, RD19, RD20, RD21, RD22, RD23, RD24, RD25, RD26, RD27 by lia.
      eexists. split.
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_451fc eq_refl D_451fc)). gr. rewrite B19.
        replace (v_addi ra 0) with ra by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45200 eq_refl D_45200)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45204 eq_refl D_45204)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45208 eq_refl D_45208)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4520c eq_refl D_4520c)). gr.
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_45210 eq_refl D_45210)). rewrite lit_68dc8.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x45214) F_44ff0 eq_refl D_44ff0); gr; reflexivity |].
        imm_norm. rewrite ret_68dc8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45214 eq_refl D_45214)). gr.
        replace (v_addi (getr regs 21) 0) with (getr regs 21) by (unfold v_addi; rewrite Z.add_0_r, zbv_self; reflexivity).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45218 eq_refl D_45218)). gr. rewrite B2. zn.
        mld2 F_4521c D_4521c ra RD1 B2.
        mld2 F_45220 D_45220 (getr regs0 8) RD8 B2.
        mld2 F_45224 D_45224 (getr regs0 9) RD9 B2.
        mld2 F_45228 D_45228 (getr regs0 18) RD18 B2.
        mld2 F_4522c D_4522c (getr regs0 19) RD19 B2.
        mld2 F_45230 D_45230 (getr regs0 20) RD20 B2.
        mld2 F_45234 D_45234 (getr regs0 21) RD21 B2.
        mld2 F_45238 D_45238 (getr regs0 22) RD22 B2.
        mld2 F_4523c D_4523c (getr regs0 23) RD23 B2.
        mld2 F_45240 D_45240 (getr regs0 24) RD24 B2.
        mld2 F_45244 D_45244 (getr regs0 25) RD25 B2.
        mld2 F_45248 D_45248 (getr regs0 26) RD26 B2.
        mld2 F_4524c D_4524c (getr regs0 27) RD27 B2.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45250 eq_refl D_45250)). gr. zn.
        replace (U - 2192 + 160 + 2032)%Z with U by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_45254 eq_refl D_45254); gr; reflexivity |].
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
    #[using="a b n bufa bufb H HU rfw rfpc RFJ RF OUT0 Hret H01 H02 H011 H012 H013 H014"] Theorem mic_run :
      exists regs' m',
        msteps SEGS (mkst regs0 (0x44ff4 : word) m0 rom) (mkst regs' ra m' rom)
        /\ RES (getr regs' 10)
        /\ getr regs' 2 = Z_to_bv 64 U /\ getr regs' 1 = ra
        /\ (forall r, ibc_clob r = false -> getr regs' r = getr regs0 r)
        /\ OUT m' /\ (forall x : word, (U <= bv_unsigned x)%Z -> m' x = m0 x).
    Proof.
      pose proof Hn.
      destruct blk_P as (q1 & MP & P2 & P8 & P9 & P18 & P19 & P20 & P21 & P24 & P23 & PK).
      assert (B1 : base q1) by (repeat split; assumption).
      destruct (blk_CA q1 p13 sfr_p13 B1) as (q2 & m2 & MA & S2 & A25 & B2).
      destruct (blk_CB q2 m2 S2 B2 A25) as (q3 & m3 & MB & S3 & B3).
      destruct (blk_CALL q3 m3 S3 B3) as (q4 & m4 & MC & S4 & R4 & C2 & C19 & CK).
      destruct (blk_E q4 m4 S4 C2 C19 CK) as (q5 & ME & E10 & E2 & E1 & EK).
      pose proof S4 as (O4 & _ & A4).
      exists q5, m4. split.
      { eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MA|]. eapply msteps_trans; [exact MB|].
        eapply msteps_trans; [exact MC|]. exact ME. }
      split; [rewrite E10; exact R4|]. split; [exact E2|]. split; [exact E1|]. split; [exact EK|]. split; [exact O4|exact A4].
    Qed.
  End MIC.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RESmc (w : word) : Prop := exists d : Z, (-255 <= d <= 255)%Z /\ w = Z_to_bv 64 d.

  #[using="Type"] Lemma memcmp_clob_sreg : forall r : reg, sreg r = true -> ~ In r VBothMuslMemcmp.memcmp_clob.
  Proof.
    intros r Hr Hin. unfold VBothMuslMemcmp.memcmp_clob in Hin. cbn in Hin. unfold sreg in Hr.
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; discriminate Hr|]). exact Hin.
  Qed.
  #[using="Type"] Lemma memcmp_clob_nclob : forall r : reg, ibc_clob r = false -> ~ In r VBothMuslMemcmp.memcmp_clob.
  Proof.
    intros r Hr Hin. unfold VBothMuslMemcmp.memcmp_clob in Hin. cbn in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn in Hr; discriminate Hr|]). exact Hin.
  Qed.

  #[using="bufa bufb H"] Lemma RF_memcmp : forall (U : Z) regs m,
    OUT m -> getr regs 2 = Z_to_bv 64 (U - 2192) -> getr regs 1 = (0x45114 : word) ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' m',
      msteps SEGS (mkst regs (0xa27b8 : word) m rom) (mkst regs' (0x45114 : word) m' rom)
      /\ RESmc (getr regs' 10)
      /\ (forall r, sreg r = true -> getr regs' r = getr regs r)
      /\ (forall r, ibc_clob r = false -> r <> 1 -> getr regs' r = getr regs r)
      /\ OUT m' /\ (forall x : word, (U - 2192 <= bv_unsigned x)%Z -> m' x = m x).
  Proof.
    intros U regs m O H2 H1 H10 H11 H12. pose proof Ha64. pose proof Hb64. pose proof Hn.
    pose proof (ib_lena _ _ _ _ _ _ _ H) as La. pose proof (ib_lenb _ _ _ _ _ _ _ H) as Lb.
    pose proof (bufa_OUT m O) as RA. pose proof (bufb_OUT m O) as RB. rewrite La in RA. rewrite Lb in RB.
    destruct (VBothMuslMemcmp.ref_memcmp m rom (Z_to_bv 64 a) (Z_to_bv 64 b) (Z.to_nat n) bufa bufb RA RB
                ltac:(rewrite Z2Nat.id by lia; lia) ltac:(rewrite zbv_u, Z2Nat.id by lia; lia)
                regs (0x45114 : word) ret_ok_68cc4 H1 H10 H11 ltac:(rewrite Z2Nat.id by lia; exact H12))
      as (regs' & i & M & AG & Hi & EQ & RES).
    exists regs', m. split; [exact M|]. split; [|split; [|split; [|split; [exact O|intros; reflexivity]]]].
    - unfold RESmc. destruct RES as [[_ R0]|(_ & NE & R1)].
      + exists 0%Z. split; [lia|exact R0].
      + pose proof (bv_unsigned_in_range 8 (nth i bufa B0)) as X. pose proof (bv_unsigned_in_range 8 (nth i bufb B0)) as Y.
        change (bv_modulus 8) with 256%Z in X, Y.
        exists (bv_unsigned (nth i bufa B0) - bv_unsigned (nth i bufb B0))%Z. split; [lia|].
        rewrite R1. unfold RefMemcpyLib.LBv. rewrite v_sub_zbv by lia. reflexivity.
    - intros r Hr. apply AG. apply memcmp_clob_sreg. exact Hr.
    - intros r Hr _. apply AG. apply memcmp_clob_nclob. exact Hr.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition S2 : Z := (usp - 2240)%Z.
  Definition U2 : Z := (usp - 2288)%Z.

  Ltac rd8w := repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                              | rewrite rdn_wbytes_out; [| len8; rewrite !zbv_u by lia; lia | len8; rewrite !zbv_u by lia; lia | len8; rewrite !zbv_u by lia; lia] ]).

  #[using="bufa bufb H"] Lemma mci_run : forall regs m (r0 : word),
    OUT m -> ret_ok r0 -> getr regs 1 = r0 -> getr regs 2 = Z_to_bv 64 S2 ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' m',
      msteps SEGS (mkst regs (0x45888 : word) m rom) (mkst regs' r0 m' rom)
      /\ RESmc (getr regs' 10)
      /\ getr regs' 2 = Z_to_bv 64 S2 /\ getr regs' 1 = r0
      /\ (forall r, ibc_clob r = false -> r <> 1 -> getr regs' r = getr regs r)
      /\ OUT m' /\ (forall x : word, (S2 <= bv_unsigned x)%Z -> m' x = m x).
  Proof.
    intros regs m r0 O Hret H1 H2 H10 H11 H12. pose proof Hsp. pose proof Ha64. pose proof Hb64. pose proof Hn. unfold S2 in *.
    (* [comment removed for export] *)
    set (w := fun (o : Z) (v : word) (mm : word -> option byte) => wbytes mm (Z_to_bv 64 (usp - 2240 - o)) (word_to_le_bytes 8 v)).
    set (m4 := w 32%Z (getr regs 18) (w 24%Z (getr regs 9) (w 16%Z (getr regs 8) (w 8%Z r0 m)))).
    set (m5 := w 40%Z (Z_to_bv 64 0x19ea8) m4).
    set (m7 := w 64%Z (Z_to_bv 64 n) (w 56%Z (Z_to_bv 64 0x458c0) m5)).
    assert (O4 : OUT m4) by (unfold m4, w; repeat (apply OUT_w8; [|unfold IBC_FRAME; lia|lia]); exact O).
    assert (O5 : OUT m5) by (unfold m5, w; apply OUT_w8; [exact O4|unfold IBC_FRAME; lia|lia]).
    assert (O7 : OUT m7) by (unfold m7, w; do 2 (apply OUT_w8; [|unfold IBC_FRAME; lia|lia]); exact O5).
    assert (AI4 : rdn SEGS m4 (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_OUT m4 O4))).
    assert (AI7 : rdn SEGS m7 (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_OUT m7 O7))).
    pose proof (cells_OUT m7 O7) as (_ & _ & _ & _ & _ & _ & RM7).
    (* [comment removed for export] *)
    assert (RD7a : rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x458c0))) by (unfold m7, w; rd8w).
    assert (RD7b : rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 n))) by (unfold m7, w; rd8w).
    assert (RS1 : rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - 8)) 8 = Some (word_to_le_bytes 8 r0)) by (unfold m7, m5, m4, w; rd8w).
    assert (RS8 : rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (unfold m7, m5, m4, w; rd8w).
    assert (RS9 : rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (unfold m7, m5, m4, w; rd8w).
    assert (RS18 : rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))) by (unfold m7, m5, m4, w; rd8w).
    evar (rr : bvmap 5 word).
    edestruct (mic_run U2 ltac:(unfold U2, IBC_FRAME; lia) (Z_to_bv 64 0xa27b8) (0xa27b8 : word) jalr_memcmp RESmc (RF_memcmp U2)
                rr (0x458e4 : word) m7 O7 ret_ok_69494) as (r1 & m1 & M1 & R1 & Q2 & Q1 & QK & O1 & K1); cycle -1.
    { assert (RD1 : forall o v, (8 <= o)%Z -> (o <= 32)%Z ->
                rdn SEGS m7 (Z_to_bv 64 (usp - 2240 - o)) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS m1 (Z_to_bv 64 (usp - 2240 - o)) 8 = Some (word_to_le_bytes 8 v)).
      { intros o v Ho1 Ho2 R. rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros y Hy. rewrite zbv_u in Hy by lia. cbn in Hy. apply K1. unfold U2. lia. }
      eexists. eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45888 eq_refl D_45888)). rewrite H2. zn.
        msdO F_4588c D_4588c (usp - 2240 - 8)%Z r0 H2 O.
        msdO F_45890 D_45890 (usp - 2240 - 16)%Z (getr regs 8) H2 O.
        msdO F_45894 D_45894 (usp - 2240 - 24)%Z (getr regs 9) H2 O.
        msdO F_45898 D_45898 (usp - 2240 - 32)%Z (getr regs 18) H2 O.
        change (wbytes _ _ _) with m4.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4589c eq_refl D_4589c)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458a0 eq_refl D_458a0)). gr. rewrite H11. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458a4 eq_refl D_458a4)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_458a8 eq_refl D_458a8)). rewrite lit_69460.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb2f20) F_5af20 eq_refl D_5af20);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5af24 eq_refl D_5af24);
                     gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI4).
        rewrite v_lb_1.
        mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5af28 eq_refl D_5af28)).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5af2c eq_refl D_5af2c)). gr. zn.
        mstep ltac:(exact (step_sltiu _ _ _ _ _ _ _ _ _ F_5af30 eq_refl D_5af30)). gr.
        replace (v_sltiu (Z_to_bv 64 (1 + -1)) 1) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x458ac) F_5af34 eq_refl D_5af34); gr; reflexivity |].
        imm_norm. rewrite ret_69460.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_458ac eq_refl D_458ac); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x198b0) F_458b0 eq_refl D_458b0);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458b4 eq_refl D_458b4)). gr. zn.
        msdO F_458b8 D_458b8 (usp - 2240 - 40)%Z (Z_to_bv 64 0x19ea8) H2 O.
        change (wbytes _ _ _) with m5.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_458bc eq_refl D_458bc)). rewrite lit_69474.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be30 eq_refl D_5be30)). gr. zn.
        msdO F_5be34 D_5be34 (usp - 2240 - 56)%Z (Z_to_bv 64 0x458c0) H2 O.
        msdO F_5be38 D_5be38 (usp - 2240 - 64)%Z (Z_to_bv 64 n) H2 O.
        change (wbytes _ _ _) with m7.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb2e3c) F_5be3c eq_refl D_5be3c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be40 eq_refl D_5be40)). gr. zn.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5be44 eq_refl D_5be44);
                     gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI7).
        rewrite v_lb_1.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be48 eq_refl D_5be48)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5be4c eq_refl D_5be4c)).
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5be50 eq_refl D_5be50); gr; br_eq).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0x458c0) F_5be54 eq_refl D_5be54);
                     [ gr; imm_norm; zn; adr (usp - 2240 - 56)%Z; exact RD7a | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 n) F_5be58 eq_refl D_5be58);
                     [ gr; imm_norm; zn; adr (usp - 2240 - 64)%Z; exact RD7b | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be5c eq_refl D_5be5c)). gr. zn.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x458c0) F_5be60 eq_refl D_5be60); gr; reflexivity |].
        imm_norm. rewrite ret_69474. replace (usp - 2240 + -48 + -16 + 16)%Z with (usp - 2240 - 48)%Z by lia.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab8c0) F_458c0 eq_refl D_458c0);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_458c4 D_458c4 0xa27b8%Z RM7 H2.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_458c8 eq_refl D_458c8); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458cc eq_refl D_458cc)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458d0 eq_refl D_458d0)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458d4 eq_refl D_458d4)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458d8 eq_refl D_458d8)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458dc eq_refl D_458dc)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_458e0 eq_refl D_458e0)). rewrite lit_69498.
        eapply msteps_trans; [subst rr; exact M1|].
        (* [comment removed for export] *)
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ r0 F_458e4 eq_refl D_458e4);
                     [ gr; rewrite Q2; unfold U2; imm_norm; zn; adr (usp - 2240 - 8)%Z; apply RD1; [lia|lia|exact RS1] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs 8) F_458e8 eq_refl D_458e8);
                     [ gr; rewrite Q2; unfold U2; imm_norm; zn; adr (usp - 2240 - 16)%Z; apply RD1; [lia|lia|exact RS8] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs 9) F_458ec eq_refl D_458ec);
                     [ gr; rewrite Q2; unfold U2; imm_norm; zn; adr (usp - 2240 - 24)%Z; apply RD1; [lia|lia|exact RS9] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs 18) F_458f0 eq_refl D_458f0);
                     [ gr; rewrite Q2; unfold U2; imm_norm; zn; adr (usp - 2240 - 32)%Z; apply RD1; [lia|lia|exact RS18] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_458f4 eq_refl D_458f4)). gr. rewrite Q2. unfold U2. zn.
        replace (usp - 2288 + 48)%Z with (usp - 2240)%Z by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ r0 F_458f8 eq_refl D_458f8); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. exact R1.
      - gr. reflexivity.
      - gr. reflexivity.
      - intros r Hr Hr1. subst rr.
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [gr; symmetry; exact H2|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [gr; reflexivity|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [gr; reflexivity|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [gr; reflexivity|].
        rewrite !getr_other by (intros ->; first [contradiction | cbn in Hr; discriminate Hr]).
        rewrite (QK r Hr). repeat (rewrite getr_other by (intros ->; first [contradiction | cbn in Hr; discriminate Hr | congruence])). reflexivity.
      - exact O1.
      - intros x Hx. rewrite (K1 x) by (unfold U2; lia). unfold m7, m5, m4, w. rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia. }
    all: subst rr; gr; try reflexivity; try (unfold U2; apply (f_equal (Z_to_bv 64)); lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition U1 : Z := (usp - 48)%Z.
  #[using="bufa bufb H"] Lemma RF_bcmp : forall regs m,
    OUT m -> getr regs 2 = Z_to_bv 64 (U1 - 2192) -> getr regs 1 = (0x45114 : word) ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' m',
      msteps SEGS (mkst regs (0xa26e8 : word) m rom) (mkst regs' (0x45114 : word) m' rom)
      /\ RESmc (getr regs' 10)
      /\ (forall r, sreg r = true -> getr regs' r = getr regs r)
      /\ (forall r, ibc_clob r = false -> r <> 1 -> getr regs' r = getr regs r)
      /\ OUT m' /\ (forall x : word, (U1 - 2192 <= bv_unsigned x)%Z -> m' x = m x).
  Proof.
    intros regs m O H2 H1 H10 H11 H12. unfold U1 in *.
    destruct (mci_run regs m (0x45114 : word) O ret_ok_68cc4 H1 ltac:(unfold S2; rewrite H2; apply (f_equal (Z_to_bv 64)); lia) H10 H11 H12)
      as (regs' & m' & M & R & Q2 & Q1 & QK & O' & K).
    exists regs', m'. split; [|split; [exact R|split; [|split; [exact QK|split; [exact O'|]]]]].
    - mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_a26e8 eq_refl D_a26e8)).
      mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44230 eq_refl D_44230)).
      exact M.
    - intros r Hr. destruct (sreg_not_clob r Hr) as (C1 & _ & C3).
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite Q2, H2; unfold S2; apply (f_equal (Z_to_bv 64)); lia|].
      exact (QK r C1 C3).
    - intros x Hx. apply K. unfold S2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="bufa bufb H"] Lemma bci_run : forall regs (r0 : word),
    ret_ok r0 -> getr regs 1 = r0 -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' m',
      msteps SEGS (mkst regs (0x45944 : word) mem rom) (mkst regs' r0 m' rom)
      /\ RESmc (getr regs' 10)
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = r0
      /\ (forall r, ibc_clob r = false -> r <> 1 -> getr regs' r = getr regs r)
      /\ OUT m' /\ (forall x : word, (usp <= bv_unsigned x)%Z -> m' x = mem x).
  Proof.
    intros regs r0 Hret H1 H2 H10 H11 H12. pose proof Hsp. pose proof Ha64. pose proof Hb64. pose proof Hn. pose proof OUT_mem as O.
    set (w := fun (o : Z) (v : word) (mm : word -> option byte) => wbytes mm (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v)).
    set (m4 := w 32%Z (getr regs 18) (w 24%Z (getr regs 9) (w 16%Z (getr regs 8) (w 8%Z r0 mem)))).
    set (m5 := w 40%Z (Z_to_bv 64 0x15650) m4).
    set (m7 := w 64%Z (Z_to_bv 64 n) (w 56%Z (Z_to_bv 64 0x4597c) m5)).
    assert (O4 : OUT m4) by (unfold m4, w; repeat (apply OUT_w8; [|unfold IBC_FRAME; lia|lia]); exact O).
    assert (O5 : OUT m5) by (unfold m5, w; apply OUT_w8; [exact O4|unfold IBC_FRAME; lia|lia]).
    assert (O7 : OUT m7) by (unfold m7, w; do 2 (apply OUT_w8; [|unfold IBC_FRAME; lia|lia]); exact O5).
    assert (AI4 : rdn SEGS m4 (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_OUT m4 O4))).
    assert (AI7 : rdn SEGS m7 (Z_to_bv 64 0xb2898) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_OUT m7 O7))).
    pose proof (cells_OUT m7 O7) as (_ & _ & _ & _ & _ & RB7 & _).
    assert (RD7a : rdn SEGS m7 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4597c))) by (unfold m7, w; rd8w).
    assert (RD7b : rdn SEGS m7 (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 n))) by (unfold m7, w; rd8w).
    assert (RS1 : rdn SEGS m7 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 r0)) by (unfold m7, m5, m4, w; rd8w).
    assert (RS8 : rdn SEGS m7 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (unfold m7, m5, m4, w; rd8w).
    assert (RS9 : rdn SEGS m7 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (unfold m7, m5, m4, w; rd8w).
    assert (RS18 : rdn SEGS m7 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))) by (unfold m7, m5, m4, w; rd8w).
    evar (rr : bvmap 5 word).
    edestruct (mic_run U1 ltac:(unfold U1, IBC_FRAME; lia) (Z_to_bv 64 0xa26e8) (0xa26e8 : word) jalr_bcmp RESmc RF_bcmp
                rr (0x459a0 : word) m7 O7 ret_ok_69550) as (r1 & m1 & M1 & R1 & Q2 & Q1 & QK & O1 & K1); cycle -1.
    { assert (RD1 : forall o v, (8 <= o)%Z -> (o <= 32)%Z ->
                rdn SEGS m7 (Z_to_bv 64 (usp - o)) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS m1 (Z_to_bv 64 (usp - o)) 8 = Some (word_to_le_bytes 8 v)).
      { intros o v Ho1 Ho2 R. rewrite <- R. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
        intros y Hy. rewrite zbv_u in Hy by lia. cbn in Hy. apply K1. unfold U1. lia. }
      eexists. eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45944 eq_refl D_45944)). rewrite H2. zn.
        msdO F_45948 D_45948 (usp - 8)%Z r0 H2 O.
        msdO F_4594c D_4594c (usp - 16)%Z (getr regs 8) H2 O.
        msdO F_45950 D_45950 (usp - 24)%Z (getr regs 9) H2 O.
        msdO F_45954 D_45954 (usp - 32)%Z (getr regs 18) H2 O.
        change (wbytes _ _ _) with m4.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45958 eq_refl D_45958)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4595c eq_refl D_4595c)). gr. rewrite H11. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45960 eq_refl D_45960)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_45964 eq_refl D_45964)). rewrite lit_6951c.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb2f20) F_5af20 eq_refl D_5af20);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5af24 eq_refl D_5af24);
                     gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI4).
        rewrite v_lb_1.
        mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5af28 eq_refl D_5af28)).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5af2c eq_refl D_5af2c)). gr. zn.
        mstep ltac:(exact (step_sltiu _ _ _ _ _ _ _ _ _ F_5af30 eq_refl D_5af30)). gr.
        replace (v_sltiu (Z_to_bv 64 (1 + -1)) 1) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x45968) F_5af34 eq_refl D_5af34); gr; reflexivity |].
        imm_norm. rewrite ret_6951c.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_45968 eq_refl D_45968); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x1596c) F_4596c eq_refl D_4596c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45970 eq_refl D_45970)). gr. zn.
        msdO F_45974 D_45974 (usp - 40)%Z (Z_to_bv 64 0x15650) H2 O.
        change (wbytes _ _ _) with m5.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_45978 eq_refl D_45978)). rewrite lit_69530.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be30 eq_refl D_5be30)). gr. zn.
        msdO F_5be34 D_5be34 (usp - 56)%Z (Z_to_bv 64 0x4597c) H2 O.
        msdO F_5be38 D_5be38 (usp - 64)%Z (Z_to_bv 64 n) H2 O.
        change (wbytes _ _ _) with m7.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb2e3c) F_5be3c eq_refl D_5be3c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be40 eq_refl D_5be40)). gr. zn.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5be44 eq_refl D_5be44);
                     gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI7).
        rewrite v_lb_1.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be48 eq_refl D_5be48)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5be4c eq_refl D_5be4c)).
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5be50 eq_refl D_5be50); gr; br_eq).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0x4597c) F_5be54 eq_refl D_5be54);
                     [ gr; imm_norm; zn; adr (usp - 56)%Z; exact RD7a | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 n) F_5be58 eq_refl D_5be58);
                     [ gr; imm_norm; zn; adr (usp - 64)%Z; exact RD7b | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be5c eq_refl D_5be5c)). gr. zn.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x4597c) F_5be60 eq_refl D_5be60); gr; reflexivity |].
        imm_norm. rewrite ret_69530. replace (usp + -48 + -16 + 16)%Z with (usp - 48)%Z by lia.
        (* [comment removed for export] *)
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab97c) F_4597c eq_refl D_4597c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_45980 D_45980 0xa26e8%Z RB7 H2.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_45984 eq_refl D_45984); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45988 eq_refl D_45988)). gr. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_4598c eq_refl D_4598c)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45990 eq_refl D_45990)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45994 eq_refl D_45994)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45998 eq_refl D_45998)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_4599c eq_refl D_4599c)). rewrite lit_69554.
        eapply msteps_trans; [subst rr; exact M1|].
        (* [comment removed for export] *)
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ r0 F_459a0 eq_refl D_459a0);
                     [ gr; rewrite Q2; unfold U1; imm_norm; zn; adr (usp - 8)%Z; apply RD1; [lia|lia|exact RS1] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs 8) F_459a4 eq_refl D_459a4);
                     [ gr; rewrite Q2; unfold U1; imm_norm; zn; adr (usp - 16)%Z; apply RD1; [lia|lia|exact RS8] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs 9) F_459a8 eq_refl D_459a8);
                     [ gr; rewrite Q2; unfold U1; imm_norm; zn; adr (usp - 24)%Z; apply RD1; [lia|lia|exact RS9] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (getr regs 18) F_459ac eq_refl D_459ac);
                     [ gr; rewrite Q2; unfold U1; imm_norm; zn; adr (usp - 32)%Z; apply RD1; [lia|lia|exact RS18] | apply bytes_le_to_Z_8 ]).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_459b0 eq_refl D_459b0)). gr. rewrite Q2. unfold U1. zn.
        replace (usp - 48 + 48)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ r0 F_459b4 eq_refl D_459b4); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. exact R1.
      - gr. reflexivity.
      - gr. reflexivity.
      - intros r Hr Hr1. subst rr.
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [gr; symmetry; exact H2|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [gr; reflexivity|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [gr; reflexivity|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [gr; reflexivity|].
        rewrite !getr_other by (intros ->; first [contradiction | cbn in Hr; discriminate Hr]).
        rewrite (QK r Hr). repeat (rewrite getr_other by (intros ->; first [contradiction | cbn in Hr; discriminate Hr | congruence])). reflexivity.
      - exact O1.
      - intros x Hx. rewrite (K1 x) by (unfold U1; lia). unfold m7, m5, m4, w. rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia. }
    all: subst rr; gr; try reflexivity; try (unfold U1; apply (f_equal (Z_to_bv 64)); lia).
  Qed.

  (* [comment removed for export] *)
  #[using="bufa bufb H"] Theorem ibc_body : forall regs (ra : word),
    ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' (d : Z) m',
      msteps SEGS (mkst regs (0x45944 : word) mem rom) (mkst regs' ra m' rom)
      /\ (-255 <= d <= 255)%Z /\ getr regs' 10 = Z_to_bv 64 d
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, ibc_clob r = false -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - IBC_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
  Proof.
    intros regs ra Hret H1 H2 H10 H11 H12.
    destruct (bci_run regs ra Hret H1 H2 H10 H11 H12) as (regs' & m' & M & (d & Hd & Rd) & Q2 & Q1 & QK & (O1 & O2 & O3) & AB).
    exists regs', d, m'. split; [exact M|]. split; [exact Hd|]. split; [exact Rd|]. split; [exact Q2|]. split; [exact Q1|].
    split; [|split; [|split; [exact O3|exact O2]]].
    - intros r Hr. destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite Q1; symmetry; exact H1|]. exact (QK r Hr N1).
    - intros x [Hx|Hx]; [apply O1; left; exact Hx|]. apply AB. exact Hx.
  Qed.
End IBC.

(* [comment removed for export] *)
Theorem ibc_run :
  forall (mem rom : word -> option byte) (a b n usp : Z) (bufa bufb : list byte),
  ibcH mem a b n usp bufa bufb ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
  getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' (d : Z) m',
    msteps SEGS (mkst regs (0x44234 : word) mem rom) (mkst regs' ra m' rom)
    /\ (-255 <= d <= 255)%Z /\ getr regs' 10 = Z_to_bv 64 d
    /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, ibc_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - IBC_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
Proof.
  intros mem rom a b n usp bufa bufb H regs ra Hret H1 H2 H10 H11 H12.
  destruct (ibc_body mem rom a b n usp bufa bufb H regs ra Hret H1 H2 H10 H11 H12) as (regs' & d & m' & M & REST).
  exists regs', d, m'. split; [|exact REST].
  mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44234 eq_refl D_44234)).
  exact M.
Qed.
