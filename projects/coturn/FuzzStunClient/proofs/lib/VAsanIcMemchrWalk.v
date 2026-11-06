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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require AsanMemcpyBase AsanMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanTls_code VAsanIcStrlen_code VAsanMusl_code VAsanIcMemchr_code VAsanMemsetWalk VAsanTlsWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanMuslStrLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VAsanMuslStrlen.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_695dc : v_addi (0x45a44 : word) 4 = Z_to_bv 64 0x45a48. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_695e4 : v_addi (0x45a4c : word) 4 = Z_to_bv 64 0x45a50. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69600 : v_addi (0x45a68 : word) 4 = (0x45a6c : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_69798 : v_addi (0x45c00 : word) 4 = (0x45c04 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_1376a8 : v_addi (0xa4a58 : word) 4 = (0xa4a5c : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_695fc : ret_ok (0x45a6c : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_69794 : ret_ok (0x45c04 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_1376a8 : ret_ok (0xa4a5c : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_695dc : v_jalr (Z_to_bv 64 0x45a48) 0 = (0x45a48 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_695e4 : v_jalr (Z_to_bv 64 0x45a50) 0 = (0x45a50 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fz (l : list byte) : nat :=
  match l with
  | [] => 0%nat
  | b :: t => if (bv_unsigned b =? 0)%Z then 0%nat else S (fz t)
  end.

Lemma fz_spec : forall l (k : nat), (k < length l)%nat -> bv_unsigned (nth k l B0) = 0%Z ->
  (fz l <= k)%nat /\ bv_unsigned (nth (fz l) l B0) = 0%Z /\ (forall j, (j < fz l)%nat -> bv_unsigned (nth j l B0) <> 0%Z).
Proof.
  induction l as [|b t IH]; intros k Hk Hz; cbn in Hk; [lia|].
  cbn [fz]. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|NE].
  - split; [lia|]. split; [exact E|]. intros j Hj. lia.
  - destruct k as [|k]; [cbn in Hz; lia|]. cbn [nth] in Hz.
    destruct (IH k ltac:(lia) Hz) as (A & B & C).
    split; [lia|]. split; [exact B|]. intros [|j] Hj; cbn [nth]; [exact NE|]. apply C. lia.
Qed.

(* [comment removed for export] *)
Definition IMC_FRAME : Z := 2200.    (* [comment removed for export] *)
Definition SNL_FRAME : Z := 2232.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition imc_cells (m : word -> option byte) : Prop :=
  cells m
  /\ rdn SEGS m (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1]      (* [comment removed for export] *)
  /\ cell m 0xacbb0 0xa40b0                                     (* [comment removed for export] *)
  /\ AsanMemchr.rodata_clear m.                                   (* [comment removed for export] *)

(* [comment removed for export] *)
Record imcH (F : Z) (mem : word -> option byte) (s n usp : Z) (buf : list byte) (K : Z) : Prop := {
  ic_buf  : rdn SEGS mem (Z_to_bv 64 s) (length buf) = Some buf;
  ic_win  : ((s + K) / 8 * 8 + 8 <= s + Z.of_nat (length buf))%Z;
  ic_nw   : (s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  ic_s    : (0 < s)%Z;
  ic_K    : (0 <= K)%Z /\ (K < Z.of_nat (length buf))%Z /\ (K + 1 <= 2 ^ 40)%Z /\ (K + 8 <= n)%Z /\ (n < 2 ^ 64)%Z;
  ic_zero_K : bv_unsigned (VAsanMuslStrlen.b_ buf K) = 0%Z;
  ic_rng  : (s + K + 1 <= kLowEnd)%Z \/ (kHighBeg <= s /\ s + K + 1 <= kHighEnd)%Z;
  ic_sp   : (SB + F + 8 <= usp < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  ic_sap  : (usp <= s \/ s + Z.of_nat (length buf) <= usp - F)%Z;
  ic_shd  : (SB + (s + K) / 8 + 8 < usp - F)%Z;
  (* [comment removed for export] *)
  ic_zg   : forall g, (s / 8 <= g < (s + K) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  ic_last : exists b1 : byte, mem (Z_to_bv 64 (SB + (s + K) / 8)) = Some b1
                              /\ (bv_unsigned b1 = 0%Z \/ ((s + K) mod 8 < bv_unsigned b1 < 8)%Z);
  (* [comment removed for export] *)
  ic_words : forall a, ((SB + s / 8) / 8 * 8 <= a)%Z -> (a <= (SB + (s + K) / 8) / 8 * 8)%Z -> (a mod 8 = 0)%Z ->
               exists w : word, rdn SEGS mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 w);
  ic_stk  : forall a, (usp - F <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  ic_cel  : imc_cells mem
}.

(* [comment removed for export] *)
Definition imc_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.
(* [comment removed for export] *)
Definition ekeep (r : reg) : bool :=
  (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 20 || bv_eqb r 21)%bool.

Lemma imc_clob_cs : forall r : reg, imc_clob r = false -> r <> 0 -> In r RefMemcpyLib.callee_saved.
Proof.
  intros r Hr H0. unfold imc_clob in Hr.
  repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
  repeat match goal with Hb : bv_eqb r ?k = false |- _ =>
    unfold bv_eqb in Hb; apply Z.eqb_neq in Hb; let kv := eval vm_compute in (bv_unsigned k) in change (bv_unsigned k) with kv in Hb end.
  assert (H0' : bv_unsigned r <> 0%Z) by (intros Hu; apply H0; apply bv_eq; exact Hu).
  pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32%Z in R.
  assert (U : forall k : reg, bv_unsigned r = bv_unsigned k -> k = r) by (intros k Hk; symmetry; apply bv_eq; exact Hk).
  assert (C : (bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9
              \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22
              \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27)%Z) by lia.
  unfold RefMemcpyLib.callee_saved. cbn [In].
  repeat match goal with X : (_ \/ _) |- _ => destruct X as [X|X] end.
  all: match goal with X : bv_unsigned ?rr = ?k |- _ =>
         let rec go := first [left; apply U; match goal with |- _ = bv_unsigned ?k => let kv := eval vm_compute in (bv_unsigned k) in change (bv_unsigned k) with kv end; exact X | right; go] in go end.
Qed.

Section IMC.
  Variable F : Z.                       (* [comment removed for export] *)
  Hypothesis HF : (IMC_FRAME <= F)%Z.
  Variables (mem rom : word -> option byte) (s n usp : Z) (buf : list byte) (K : Z).
  Hypothesis H : imcH F mem s n usp buf K.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 s.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 0.
  Hypothesis H012 : getr regs0 12 = Z_to_bv 64 n.

  Let HK := ic_K _ _ _ _ _ _ _ H.
  #[using="HF mem s n buf K H"] Lemma Hsp : (0x7fff8000 + 2208 <= usp < 2 ^ 64)%Z /\ (0x7fff8000 + F + 8 <= usp)%Z.
  Proof. pose proof (ic_sp _ _ _ _ _ _ _ H). unfold IMC_FRAME, SB in *. lia. Qed.
  #[using="F mem n usp buf K H HK"] Lemma Hs64 : (0 < s < 2 ^ 64)%Z.
  Proof. pose proof (ic_nw _ _ _ _ _ _ _ H). pose proof (ic_s _ _ _ _ _ _ _ H). lia. Qed.
  #[using="F mem n usp buf H HK"] Lemma HK64 : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z /\ (s + K + 1 < 2 ^ 47)%Z.
  Proof. pose proof (ic_K _ _ _ _ _ _ _ H). pose proof (ic_rng _ _ _ _ _ _ _ H). pose proof Hs64. unfold kLowEnd, kHighBeg, kHighEnd in *. lia. Qed.

  (* [comment removed for export] *)
  Definition I : Z := Z.of_nat (fz buf).
  #[using="F mem s n usp H HK"] Lemma I_facts : (0 <= I <= K)%Z /\ bv_unsigned (VAsanMuslStrlen.b_ buf I) = 0%Z
                  /\ (forall j, (0 <= j < I)%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf j) <> 0%Z)
                  /\ (forall j : nat, (j < Z.to_nat I)%nat -> bv_unsigned (nth j buf B0) <> 0%Z).
  Proof.
    pose proof HK as (K0 & KL & _).
    destruct (fz_spec buf (Z.to_nat K) ltac:(lia) (ic_zero_K _ _ _ _ _ _ _ H)) as (A & B & C).
    unfold I, VAsanMuslStrlen.b_. rewrite Nat2Z.id. split; [lia|]. split; [exact B|]. split.
    - intros j Hj. apply C. lia.
    - intros j Hj. apply C. lia.
  Qed.

  (* [comment removed for export] *)
  Definition p7 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
      (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem)))))).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.
  Ltac adr c := match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with c by lia end.

  (* [comment removed for export] *)
  Definition sfr (m : word -> option byte) : Prop :=
       (forall x : word, (bv_unsigned x < usp - F \/ usp <= bv_unsigned x)%Z -> m x = mem x)
    /\ (forall x : word, (usp - 56 <= bv_unsigned x < usp)%Z -> m x = p7 x)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true)
    /\ (forall x, mem x <> None -> m x <> None).

  #[using="F HF s n buf K H"] Lemma p7_out : forall x : word, (bv_unsigned x < usp - 56 \/ usp <= bv_unsigned x)%Z -> p7 x = mem x.
  Proof.
    intros x [Hx|Hx]; unfold p7; pose proof Hsp.
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  #[using="HF s n buf K H"] Lemma sfr_p7 : sfr p7.
  Proof.
    split; [|split; [intros; reflexivity|split]].
    - intros x Hx. apply p7_out. unfold IMC_FRAME in *. lia.
    - intros x Hx. unfold p7. repeat apply store_ok1_wbytes. exact Hx.
    - intros x Hx. unfold p7. repeat apply wbytes_keep. exact Hx.
  Qed.
  #[using="HF s n buf K H"] Lemma sfr_w8 : forall m (a : Z) (v : word), sfr m -> (usp - F <= a)%Z -> (a + 8 <= usp - 56)%Z ->
    sfr (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof.
    intros m a v (F1 & F2 & F3 & F4) Ha Hb. pose proof Hsp. unfold IMC_FRAME in *. split; [|split; [|split]].
    - intros x Hx. rewrite <- (F1 x Hx). destruct Hx as [Hx|Hx].
      + apply wbytes_below; len8; rewrite ?zbv_u by lia; lia.
      + apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. rewrite <- (F2 x Hx). apply wbytes_above; len8; rewrite ?zbv_u by lia; lia.
    - intros x Hx. apply store_ok1_wbytes. apply F3. exact Hx.
    - intros x Hx. apply wbytes_keep. apply F4. exact Hx.
  Qed.
  #[using="HF s n buf K H"] Lemma sfr_rp : forall m (rra s0 s1 s2 s3 s4 s5 : word), sfr m -> sfr (rp_frame m (usp - 2128) rra s0 s1 s2 s3 s4 s5).
  Proof. intros. unfold rp_frame. repeat (apply sfr_w8; [|unfold IMC_FRAME in *; lia|lia]). assumption. Qed.

  #[using="Type"] Lemma sfr_below : forall m (x : word), sfr m -> (bv_unsigned x < usp - F)%Z -> m x = mem x.
  Proof. intros m x (F1 & _) Hx. exact (F1 x (or_introl Hx)). Qed.
  #[using="HF s n buf K H"] Lemma rdn_sfr_below : forall m (a : Z) k, sfr m -> (0 <= a)%Z -> (a + Z.of_nat k <= usp - F)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k FF Ha Hk. pose proof Hsp. unfold IMC_FRAME in *. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply (sfr_below m x FF). lia.
  Qed.
  #[using="HF s n buf K H"] Lemma rdn_sfr_out : forall m (a : Z) k, sfr m -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z ->
    (a + Z.of_nat k <= usp - F \/ usp <= a)%Z ->
    rdn SEGS m (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros m a k (F1 & _) Ha Hk Hap. pose proof Hsp. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply F1. lia.
  Qed.
  #[using="HF s n buf K H"] Lemma cells_sfr : forall m, sfr m -> imc_cells m.
  Proof.
    intros m FF. pose proof (ic_cel _ _ _ _ _ _ _ H) as (C & C1 & C2 & C5). pose proof Hsp. pose proof SB_val. unfold IMC_FRAME in *.
    unfold imc_cells, cells, cell in *. rewrite !(rdn_sfr_below m) by (first [exact FF | cbn; lia]).
    split; [exact C|]. split; [exact C1|]. split; [exact C2|].
    intros i Hi. rewrite (sfr_below m); [exact (C5 i Hi)|exact FF|rewrite zbv_u by lia; lia].
  Qed.
  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp; unfold p7;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
  #[using="F HF s n buf K H"] Lemma rd_ra : rdn SEGS p7 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).              Proof. rd_slot. Qed.
  #[using="F HF s n buf K H"] Lemma rd_s0 : rdn SEGS p7 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)).  Proof. rd_slot. Qed.
  #[using="F HF s n buf K H"] Lemma rd_s1 : rdn SEGS p7 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)).  Proof. rd_slot. Qed.
  #[using="F HF s n buf K H"] Lemma rd_s2 : rdn SEGS p7 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.
  #[using="F HF s n buf K H"] Lemma rd_s3 : rdn SEGS p7 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. rd_slot. Qed.
  #[using="F HF s n buf K H"] Lemma rd_s4 : rdn SEGS p7 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. rd_slot. Qed.
  #[using="F HF s n buf K H"] Lemma rd_s5 : rdn SEGS p7 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. rd_slot. Qed.

  #[using="HF s n buf K H"] Lemma stk8 : forall m a, sfr m -> (usp - F <= a)%Z -> (a + 8 <= usp)%Z -> store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a (_ & _ & F3 & _) H1 H2. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply F3. apply (ic_stk _ _ _ _ _ _ _ H). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition p9 : word -> option byte :=
    wbytes (wbytes p7 (Z_to_bv 64 (usp - 2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x45a50)))
           (Z_to_bv 64 (usp - 2144)) (word_to_le_bytes 8 (Z_to_bv 64 usp)).
  #[using="HF s n buf K H"] Lemma sfr_p9 : sfr p9.
  Proof. unfold p9. apply sfr_w8; [apply sfr_w8; [exact sfr_p7|unfold IMC_FRAME in *; lia|lia]|unfold IMC_FRAME in *; lia|lia]. Qed.

  Ltac msd F D a v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                 | apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold p9, p7; repeat apply store_ok1_wbytes;
                   apply (ic_stk _ _ _ _ _ _ _ H); unfold IMC_FRAME in *; lia ]).

  (* [comment removed for export] *)
  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r : reg, imc_clob r = false -> ekeep r = false -> getr regs r = getr regs0 r.
  Ltac keep_tac Hr He := repeat (rewrite getr_other by (intros ->; cbn in Hr, He; first [discriminate Hr | discriminate He])).

  #[using="F HF buf K H H01 H02 H010 H011 H012 HK"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x45a10 : word) mem rom) (mkst regs (0x45a50 : word) p9 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 2128) /\ getr regs 8 = Z_to_bv 64 usp /\ getr regs 18 = Z_to_bv 64 s
      /\ getr regs 9 = Z_to_bv 64 n /\ getr regs 19 = Z_to_bv 64 0 /\ getr regs 10 = Z_to_bv 64 1 /\ keep regs.
  Proof.
    pose proof Hsp. pose proof Hs64. pose proof (cells_sfr p7 sfr_p7) as (_ & AI & _).
    assert (AI9 : rdn SEGS p9 (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1]) by exact (proj1 (proj2 (cells_sfr p9 sfr_p9))).
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a10 eq_refl D_45a10)). rewrite H02. zn.
      msd F_45a14 D_45a14 (usp - 8)%Z ra H02.
      msd F_45a18 D_45a18 (usp - 16)%Z (getr regs0 8) H02.
      msd F_45a1c D_45a1c (usp - 24)%Z (getr regs0 9) H02.
      msd F_45a20 D_45a20 (usp - 32)%Z (getr regs0 18) H02.
      msd F_45a24 D_45a24 (usp - 40)%Z (getr regs0 19) H02.
      msd F_45a28 D_45a28 (usp - 48)%Z (getr regs0 20) H02.
      msd F_45a2c D_45a2c (usp - 56)%Z (getr regs0 21) H02.
      change (wbytes _ _ _) with p7.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a30 eq_refl D_45a30)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a34 eq_refl D_45a34)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a38 eq_refl D_45a38)). gr. rewrite H012. zn. rewrite ?Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a3c eq_refl D_45a3c)). gr. rewrite H011. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a40 eq_refl D_45a40)). gr. rewrite H010. zn. rewrite ?Z.add_0_r.
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_45a44 eq_refl D_45a44)). rewrite lit_695dc.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3f30) F_5af30 eq_refl D_5af30);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5af34 eq_refl D_5af34);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI).
      rewrite v_lb_1.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5af38 eq_refl D_5af38)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5af3c eq_refl D_5af3c)). gr. zn.
      mstep ltac:(exact (step_sltiu _ _ _ _ _ _ _ _ _ F_5af40 eq_refl D_5af40)). gr.
      replace (v_sltiu (Z_to_bv 64 (1 + -1)) 1) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x45a48) F_5af44 eq_refl D_5af44); gr; reflexivity |].
      imm_norm. rewrite ret_695dc.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_45a48 eq_refl D_45a48); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_45a4c eq_refl D_45a4c)). rewrite lit_695e4.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be40 eq_refl D_5be40)). gr. zn.
      msd F_5be44 D_5be44 (usp - 2136)%Z (Z_to_bv 64 0x45a50) H02.
      msd F_5be48 D_5be48 (usp - 2144)%Z (Z_to_bv 64 usp) H02.
      change (wbytes _ _ _) with p9.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3e4c) F_5be4c eq_refl D_5be4c);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be50 eq_refl D_5be50)). gr. zn.
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5be54 eq_refl D_5be54);
                   gr; imm_norm; zn; rewrite ?Z.add_0_r; exact AI9).
      rewrite v_lb_1.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be58 eq_refl D_5be58)). rewrite getr_zero. zn.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5be5c eq_refl D_5be5c)).
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5be60 eq_refl D_5be60); gr; br_eq).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0x45a50) F_5be64 eq_refl D_5be64);
                   [ gr; imm_norm; zn; adr (usp - 2136)%Z;
                     unfold p9; rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia| len8; rewrite !zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia | len8; rewrite zbv_u by lia; lia]
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 usp) F_5be68 eq_refl D_5be68);
                   [ gr; imm_norm; zn; adr (usp - 2144)%Z;
                     unfold p9; apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                   | apply bytes_le_to_Z_8 ]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5be6c eq_refl D_5be6c)). gr. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (Z_to_bv 64 0x45a50) F_5be70 eq_refl D_5be70); gr; reflexivity |].
      imm_norm. rewrite ret_695e4. replace (usp - 2128 + -16 + 16)%Z with (usp - 2128)%Z by lia.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try reflexivity.
      intros r Hr He. keep_tac Hr He. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="F HF K H HK"] Lemma mchrH_p9 : AsanMemchr.mchrH p9 (Z_to_bv 64 s) buf I n.
  Proof.
    pose proof Hsp. pose proof Hs64. pose proof (ic_nw _ _ _ _ _ _ _ H). pose proof (ic_sap _ _ _ _ _ _ _ H) as AP.
    pose proof (cells_sfr p9 sfr_p9) as (_ & _ & _ & RO). pose proof I_facts as (I1 & I2 & I3 & I4). pose proof HK as (K0 & KL & K40 & Kn & N64).
    pose proof (ic_win _ _ _ _ _ _ _ H) as W.
    pose proof (Z.div_le_mono (s + I) (s + K) 8 ltac:(lia) ltac:(lia)).
    constructor; rewrite ?zbv_u by lia.
    - rewrite (rdn_sfr_out p9); [exact (ic_buf _ _ _ _ _ _ _ H) | exact sfr_p9 | lia | lia | lia].
    - lia.
    - lia.
    - lia.
    - unfold I. rewrite Nat2Z.id. unfold VAsanMuslStrlen.b_, I in I2. rewrite Nat2Z.id in I2. exact I2.
    - intros j Hj. apply I4. exact Hj.
    - lia.
    - lia.
    - exact RO.
  Qed.

  #[using="F HF K H HK"] Lemma blk_S : forall regs,
    keep regs -> getr regs 18 = Z_to_bv 64 s -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 1 ->
    getr regs 2 = Z_to_bv 64 (usp - 2128) -> getr regs 8 = Z_to_bv 64 usp ->
    exists regs',
      msteps SEGS (mkst regs (0x45a50 : word) p9 rom) (mkst regs' (0x45a6c : word) p9 rom)
      /\ getr regs' 10 = Z_to_bv 64 (s + I) /\ getr regs' 20 = Z_to_bv 64 1 /\ getr regs' 9 = Z_to_bv 64 n /\ getr regs' 18 = Z_to_bv 64 s
      /\ getr regs' 2 = Z_to_bv 64 (usp - 2128) /\ getr regs' 8 = Z_to_bv 64 usp /\ keep regs'.
  Proof.
    intros regs HKp H18 H9 H19 H10 H2 H8. pose proof Hsp. pose proof Hs64.
    pose proof (cells_sfr p9 sfr_p9) as (_ & _ & RL & _).
    evar (rr : bvmap 5 word).
    edestruct (AsanMemchr.ref_memchr0 p9 (Z_to_bv 64 s) buf I n rom rr (0x45a6c : word) mchrH_p9 ret_ok_695fc)
      as (r1 & M1 & K1 & R10); cycle -1.
    { exists r1. split; [|split; [rewrite R10; rewrite zbv_u by lia; reflexivity|]].
      - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaca50) F_45a50 eq_refl D_45a50);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_45a54 D_45a54 0xa40b0%Z RL H18.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a58 eq_refl D_45a58)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a5c eq_refl D_45a5c)). gr. rewrite H18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a60 eq_refl D_45a60)). gr. rewrite H19. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a64 eq_refl D_45a64)). gr. rewrite H9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa40b0) F_45a68 eq_refl D_45a68);
                     [reflexivity | gr; reflexivity]).
        rewrite ?lit_69600.
        match goal with |- msteps _ (mkst ?r ?pc ?mm ?ro) _ =>
          replace pc with (0xa40b0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
        subst rr. exact M1.
      - assert (KK : forall k : reg, In k RefMemcpyLib.callee_saved -> getr r1 k = getr rr k) by (intros k Hk; exact (K1 k Hk)).
        rewrite (KK 20), (KK 9), (KK 18), (KK 2), (KK 8) by (cbn; tauto). subst rr. gr.
        split; [reflexivity|]. split; [exact H9|]. split; [exact H18|]. split; [exact H2|]. split; [exact H8|].
        intros r Hr He.
        destruct (bv_eq_dec _ r 0) as [-> | N0]; [rewrite !getr_zero; reflexivity|].
        rewrite (KK r (imc_clob_cs r Hr N0)). keep_tac Hr He. apply HKp; assumption. }
    all: subst rr; gr; try reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="F HF n K H HK"] Lemma blk_T : forall regs, keep regs ->
    getr regs 10 = Z_to_bv 64 (s + I) -> getr regs 20 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 s -> getr regs 8 = Z_to_bv 64 usp ->
    getr regs 2 = Z_to_bv 64 (usp - 2128) ->
    exists regs',
      msteps SEGS (mkst regs (0x45a6c : word) p9 rom) (mkst regs' (0x45a8c : word) p9 rom)
      /\ getr regs' 9 = Z_to_bv 64 (I + 1) /\ getr regs' 10 = Z_to_bv 64 (s + I)
      /\ getr regs' 18 = Z_to_bv 64 s /\ getr regs' 2 = Z_to_bv 64 (usp - 2128) /\ getr regs' 8 = Z_to_bv 64 usp
      /\ getr regs' 11 = Z_to_bv 64 (I + 1 - 65) /\ getr regs' 12 = Z_to_bv 64 (2 ^ 64 - 65)
      /\ keep regs'.
  Proof.
    intros regs HKp H10 H20 H18 H8 H2. pose proof Hsp. pose proof Hs64. pose proof HK64 as (HK0 & HK1 & HK2). pose proof I_facts as (I1 & _).
    eexists. split.
    - mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_45a6c eq_refl D_45a6c); gr; rewrite ?H20, ?getr_zero; br_eq).
      mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45a70 eq_refl D_45a70); gr; rewrite ?H10, ?getr_zero; br_eq).
      mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_45b28 eq_refl D_45b28)). gr. rewrite H10, H18. rewrite v_sub_zbv by lia.
      replace (s + I - s)%Z with I by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45b2c eq_refl D_45b2c)). gr. zn.
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45b30 eq_refl D_45b30)). gr. rewrite H18. rewrite v_not_zbv by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45b34 eq_refl D_45b34)). gr. rewrite H8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45b38 eq_refl D_45b38)). gr. zn.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_45b3c eq_refl D_45b3c); gr; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a84 eq_refl D_45a84)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45a88 eq_refl D_45a88)). rewrite getr_zero. zn.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try assumption.
      + rewrite <- (zbv_wrap_add (-65)). apply (f_equal (Z_to_bv 64)). lia.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="F n usp buf H HK"] Lemma last_i : forall i, (0 <= i <= K)%Z ->
    exists b1 : byte, mem (Z_to_bv 64 (SB + (s + i) / 8)) = Some b1
                      /\ (bv_unsigned b1 = 0%Z \/ ((s + i) mod 8 < bv_unsigned b1 < 8)%Z).
  Proof.
    intros i Hi. pose proof Hs64.
    pose proof (Z.div_le_mono (s + i) (s + K) 8 ltac:(lia) ltac:(lia)) as LE.
    destruct (Z.lt_ge_cases ((s + i) / 8) ((s + K) / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      apply (ic_zg _ _ _ _ _ _ _ H). split; [apply Z.div_le_mono; lia|exact LT].
    - assert (E : ((s + i) / 8 = (s + K) / 8)%Z) by lia.
      destruct (ic_last _ _ _ _ _ _ _ H) as (b1 & M & B). exists b1. rewrite E. split; [exact M|].
      destruct B as [B|B]; [left; exact B|right].
      pose proof (Z.div_mod (s + i) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + i) 8 ltac:(lia)).
      pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). lia.
  Qed.
  #[using="F n usp buf H HK"] Lemma zero_i : forall i g, (0 <= i <= K)%Z -> (s / 8 <= g < (s + i) / 8)%Z ->
    mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
  Proof.
    intros i g Hi Hg. pose proof Hs64. pose proof (Z.div_le_mono (s + i) (s + K) 8 ltac:(lia) ltac:(lia)).
    apply (ic_zg _ _ _ _ _ _ _ H). lia.
  Qed.
  #[using="HF mem n buf H HK"] Lemma qfacts : forall i, (0 <= i <= K)%Z ->
    (8 * (s / 8) <= s < 8 * (s / 8) + 8)%Z /\ (8 * ((s + i) / 8) <= s + i < 8 * ((s + i) / 8) + 8)%Z
    /\ ((s + i) mod 8 = s + i - 8 * ((s + i) / 8))%Z
    /\ (SB + (s + i) / 8 + 8 < usp - F)%Z /\ (s / 8 <= (s + i) / 8 <= (s + K) / 8)%Z /\ SB = 0x7fff8000%Z
    /\ (s + K + 1 < 2 ^ 47)%Z /\ (2200 <= F)%Z.
  Proof.
    intros i Hi. pose proof (ic_shd _ _ _ _ _ _ _ H) as Hshd. pose proof SB_val. pose proof Hs64.
    pose proof HK64 as (HK0 & HK1 & HK2). pose proof HF as HF'. unfold IMC_FRAME in HF'.
    pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
    pose proof (Z.div_mod (s + i) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + i) 8 ltac:(lia)).
    pose proof (Z.div_le_mono s (s + i) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (s + i) (s + K) 8 ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HF n K H HK"] Lemma blk_Q1 : forall regs m, sfr m -> (I <= 63)%Z -> keep regs ->
    getr regs 9 = Z_to_bv 64 (I + 1) -> getr regs 18 = Z_to_bv 64 s ->
    getr regs 11 = Z_to_bv 64 (I + 1 - 65) -> getr regs 12 = Z_to_bv 64 (2 ^ 64 - 65) ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x45a8c : word) m rom) (mkst regs' (0x45ac8 : word) m rom)
      /\ getr regs' 11 = Z_to_bv 64 (SB + s / 8) /\ getr regs' 12 = Z_to_bv 64 (SB + (s + I) / 8)
      /\ getr regs' 13 = Z_to_bv 64 (s + I) /\ getr regs' 14 = w
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m FF Hi63 HKp H9 H18 H11 H12. pose proof Hsp as HU. pose proof Hs64. pose proof I_facts as (Hi & _).
    destruct (qfacts I Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & HFF).
    pose proof (cells_sfr m FF) as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & _).
    pose proof (Z.div_mod (SB + s / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + s / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + (s + I) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (s + I) / 8) 8 ltac:(lia)).
    pose proof (Z.div_le_mono (SB + s / 8) (SB + (s + I) / 8) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (SB + (s + I) / 8) (SB + (s + K) / 8) 8 ltac:(lia) ltac:(lia)).
    destruct (ic_words _ _ _ _ _ _ _ H ((SB + s / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@HK; @H0; @Hi; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:((ltac2:(LK.k [@HK; @H0; @Hi; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w1 W1].
    destruct (ic_words _ _ _ _ _ _ _ H ((SB + (s + I) / 8) / 8 * 8)%Z ltac:((ltac2:(LK.k [@HK; @H0; @Hi; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:((ltac2:(LK.k [@HK; @H0; @Hi; @D0; @D1; @D01; @HSB; @H5; @H6]); lia)) ltac:(rewrite Z_mod_mult; reflexivity)) as [w2 W2].
    assert (W1c : cell m ((SB + s / 8) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact FF | cbn; (ltac2:(LK.k [@H0; @Hi; @D0; @D1; @D01; @HSB; @H1; @H2; @Dshd]); lia)]). exact W1. }
    assert (W2c : cell m ((SB + (s + I) / 8) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite (rdn_sfr_below m) by (first [exact FF | cbn; (ltac2:(LK.k [@H0; @Hi; @D0; @D1; @D01; @HSB; @H3; @H4; @HK; @Dshd]); lia)]). exact W2. }
    replace (Z_to_bv 64 (I + 1 - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + (I + 1))) in H11
      by (rewrite <- (zbv_wrap_add (I + 1 - 65)); apply (f_equal (Z_to_bv 64)); lia).
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_45a8c eq_refl D_45a8c); gr; rewrite ?H11, ?H12; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaaa90) F_45a90 eq_refl D_45a90);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_45a94 D_45a94 0xb35f8%Z C1 H18.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_45a98 eq_refl D_45a98)). gr. rewrite H9, H18, v_add_zbv by lia.
      mld F_45a9c D_45a9c SB C2 H18.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_45aa0 eq_refl D_45aa0)). gr. rewrite H18, (v_srli_3 s) by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45aa4 eq_refl D_45aa4)). gr. zn.
      replace (s + (I + 1) + -1)%Z with (s + I)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_45aa8 eq_refl D_45aa8)). gr. rewrite (v_srli_3 (s + I)) by (ltac2:(LK.k [@HK; @H0; @Hi; @D0; @D1; @D01; @HSB; @HsK]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_45aac eq_refl D_45aac)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@H0; @HSB; @HK; @Hi; @D0; @HsK]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_45ab0 eq_refl D_45ab0)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@H0; @HSB; @Hi; @D0; @D1; @DM; @D01; @HsK]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45ab4 eq_refl D_45ab4)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@HK; @H0; @Hi; @D0; @D1; @D01; @HSB; @HsK]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45ab8 eq_refl D_45ab8)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@H0; @Hi; @D1; @DM; @D01; @HSB; @HsK]); lia).
      mld F_45abc D_45abc (bv_unsigned w1) W1c H18.
      mld F_45ac0 D_45ac0 (bv_unsigned w2) W2c H18.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45ac4 eq_refl D_45ac4)). gr.
      apply mst_refl.
    - gr. repeat split; try reflexivity; try assumption.
      intros r Hr He. keep_tac Hr He. apply HKp; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HF n K H HK"] Lemma blk_Q2a : forall regs m, sfr m -> keep regs ->
    getr regs 12 = Z_to_bv 64 (SB + (s + I) / 8) -> getr regs 13 = Z_to_bv 64 (s + I) ->
    exists regs',
      msteps SEGS (mkst regs (0x45bc0 : word) m rom) (mkst regs' (0x45bd8 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 0
      /\ getr regs' 11 = getr regs 11 /\ getr regs' 12 = getr regs 12
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m FF HKp H12 H13. pose proof Hsp as HU. pose proof Hs64. pose proof I_facts as (Hi & _).
    destruct (qfacts I Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & HFF).
    destruct (last_i I Hi) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS m (Z_to_bv 64 (SB + (s + I) / 8)) 1 = Some [b1]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact FF | rewrite zbv_u by lia; lia]). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_45bc0 eq_refl D_45bc0);
                     gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45bc4 eq_refl D_45bc4)). gr. rewrite H13, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_45bc8 eq_refl D_45bc8)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_45bcc eq_refl D_45bcc)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45bd0 eq_refl D_45bd0)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_45bd4 eq_refl D_45bd4)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
    - eexists. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_45bc0 eq_refl D_45bc0);
                     gr; rewrite ?H12; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45bc4 eq_refl D_45bc4)). gr. rewrite H13, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_45bc8 eq_refl D_45bc8)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_45bcc eq_refl D_45bcc)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_45bd0 eq_refl D_45bd0)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_45bd4 eq_refl D_45bd4)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HF n K H HK"] Lemma q_loop : forall (k : nat) regs m (g : Z), sfr m -> keep regs ->
    getr regs 11 = Z_to_bv 64 (SB + g) -> getr regs 12 = Z_to_bv 64 (SB + (s + I) / 8) -> getr regs 13 = Z_to_bv 64 0 ->
    (s / 8 <= g < (s + I) / 8)%Z -> Z.of_nat k = ((s + I) / 8 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x45bdc : word) m rom) (mkst regs' (0x45bec : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 0
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    pose proof Hsp as HU. pose proof Hs64. pose proof I_facts as (Hi & _).
    induction k as [|k IH]; intros regs m g FF HKp H11 H12 H13 Hg Hk; [lia|].
    destruct (qfacts I Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & HFF).
    assert (Z0 : rdn SEGS m (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite (sfr_below m) by (first [exact FF | rewrite zbv_u by lia; lia]).
      apply (zero_i I); lia. }
    destruct (Z.eq_dec (g + 1) ((s + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_45bdc eq_refl D_45bdc);
                     gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45be0 eq_refl D_45be0)). gr. rewrite H11. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45be4 eq_refl D_45be4)). gr. rewrite H13, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_45be8 eq_refl D_45be8); gr; rewrite ?H12; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr m (g + 1)%Z FF) as (r2 & M2 & R13 & R10 & R2 & R8 & R9 & R18 & K2); cycle -1.
      { exists r2. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_45bdc eq_refl D_45bdc);
                       gr; rewrite ?H11; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45be0 eq_refl D_45be0)). gr. rewrite H11. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_45be4 eq_refl D_45be4)). gr. rewrite H13, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45be8 eq_refl D_45be8); gr; rewrite ?H12; br_eq).
          subst rr. exact M2.
        + exact R13.
        + rewrite R10. subst rr. gr. reflexivity.
        + rewrite R2. subst rr. gr. reflexivity.
        + rewrite R8. subst rr. gr. reflexivity.
        + rewrite R9. subst rr. gr. reflexivity.
        + rewrite R18. subst rr. gr. reflexivity.
        + exact K2. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      { intros r Hr He. keep_tac Hr He. apply HKp; assumption. }
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HF n K H HK"] Lemma blk_Q2b : forall regs m, sfr m -> keep regs ->
    getr regs 11 = Z_to_bv 64 (SB + s / 8) -> getr regs 12 = Z_to_bv 64 (SB + (s + I) / 8) -> getr regs 13 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x45bd8 : word) m rom) (mkst regs' (0x45acc : word) m rom)
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ keep regs'.
  Proof.
    intros regs m FF HKp H11 H12 H13. pose proof Hsp as HU. pose proof Hs64. pose proof I_facts as (Hi & _).
    destruct (qfacts I Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & HFF).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec (s / 8) ((s + I) / 8)) as [Heq | Hne].
    - eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_45bd8 eq_refl D_45bd8); gr; rewrite ?H11, ?H12; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45bec eq_refl D_45bec)). gr. rewrite H13, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45bf0 eq_refl D_45bf0); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity. + gr. reflexivity.
      + intros r Hr He. keep_tac Hr He. apply HKp; assumption.
    - evar (rr : bvmap 5 word).
      edestruct (q_loop (Z.to_nat ((s + I) / 8 - s / 8)) rr m (s / 8) FF) as (r2 & M2 & R13 & R10 & R2 & R8 & R9 & R18 & K2); cycle -1.
      { eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_45bd8 eq_refl D_45bd8); gr; rewrite ?H11, ?H12; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_45bec eq_refl D_45bec)). rewrite R13, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45bf0 eq_refl D_45bf0); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + gr. rewrite R10. subst rr. reflexivity.
        + gr. rewrite R2. subst rr. reflexivity.
        + gr. rewrite R8. subst rr. reflexivity.
        + gr. rewrite R9. subst rr. reflexivity.
        + gr. rewrite R18. subst rr. reflexivity.
        + intros r Hr He. keep_tac Hr He. apply K2; assumption. }
      all: subst rr; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HF n K H HK"] Lemma rp_pre : forall m b1, sfr m -> (64 <= I)%Z ->
    mem (Z_to_bv 64 (SB + (s + I) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((s + I) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH m s (I + 1) (usp - 2128) b1.
  Proof.
    intros m b1 FF Hi64 L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof Hs64. pose proof HK64 as (HK0 & HK1 & HK2). pose proof I_facts as (Hi & _).
    destruct (qfacts I Hi) as (D0 & D1 & DM & Dshd & D01 & HSB & HsK & HFF).
    pose proof FF as (F1 & F2 & F3 & F4).
    constructor; rewrite ?Z.add_assoc; replace (s + I + 1 - 1)%Z with (s + I)%Z by lia.
    - lia.
    - lia.
    - pose proof (ic_rng _ _ _ _ _ _ _ H). lia.
    - lia.
    - lia.
    - intros g Hg. rewrite (sfr_below m) by (first [exact FF | rewrite zbv_u by lia; lia]). apply (zero_i I); lia.
    - rewrite (sfr_below m) by (first [exact FF | rewrite zbv_u by lia; lia]). exact L1.
    - exact Hb1.
    - intros a Ha. apply F3. apply (ic_stk _ _ _ _ _ _ _ H). lia.
    - exact (proj1 (cells_sfr m FF)).
  Qed.

  #[using="Type"] Lemma rp_clob_imc : forall r : reg, imc_clob r = false -> rp_clob r = false.
  Proof.
    intros r Hr. unfold imc_clob in Hr. unfold rp_clob.
    repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
    repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
  Qed.

  #[using="HF n K H HK"] Lemma blk_L : forall regs m, sfr m -> (64 <= I)%Z -> keep regs ->
    getr regs 9 = Z_to_bv 64 (I + 1) -> getr regs 10 = Z_to_bv 64 (s + I) ->
    getr regs 18 = Z_to_bv 64 s -> getr regs 2 = Z_to_bv 64 (usp - 2128) -> getr regs 8 = Z_to_bv 64 usp ->
    getr regs 11 = Z_to_bv 64 (I + 1 - 65) -> getr regs 12 = Z_to_bv 64 (2 ^ 64 - 65) ->
    exists regs' m',
      msteps SEGS (mkst regs (0x45a8c : word) m rom) (mkst regs' (0x45acc : word) m' rom)
      /\ sfr m'
      /\ getr regs' 10 = Z_to_bv 64 (s + I) /\ getr regs' 2 = Z_to_bv 64 (usp - 2128)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ keep regs'.
  Proof.
    intros regs m FF Hi64 HKp H9 H10 H18 H2 H8 H11 H12. pose proof Hsp. pose proof Hs64. pose proof HK64 as (HK0 & HK1 & HK2). pose proof I_facts as (Hi & _).
    destruct (last_i I Hi) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned m rom s (I + 1) (usp - 2128) b1 (rp_pre m b1 FF ltac:(lia) L1 Hb1) rr (0x45c04 : word) ret_ok_69794)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_45a8c eq_refl D_45a8c); gr; rewrite ?H11, ?H12; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45bb8 eq_refl D_45bb8); gr; rewrite ?H9, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45bf4 eq_refl D_45bf4)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45bf8 eq_refl D_45bf8)). gr. rewrite H18. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45bfc eq_refl D_45bfc)). gr. rewrite H9. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_45c00 eq_refl D_45c00)). rewrite lit_69798.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45c04 eq_refl D_45c04)). gr. rewrite R10. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45c08 eq_refl D_45c08)). gr.
        rewrite (K1 21) by reflexivity. subst rr. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_45c0c eq_refl D_45c0c); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      - apply sfr_rp. exact FF.
      - subst rr. gr. reflexivity.
      - subst rr. gr. exact R2.
      - subst rr. gr. rewrite (K1 8) by reflexivity. gr. reflexivity.
      - subst rr. gr. rewrite (K1 9) by reflexivity. gr. reflexivity.
      - subst rr. intros r Hr He. keep_tac Hr He. rewrite (K1 r (rp_clob_imc r Hr)). keep_tac Hr He. apply HKp; assumption. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  #[using="F HF s n buf K H Hret"] Lemma blk_E : forall regs mF,
    getr regs 2 = Z_to_bv 64 (usp - 2128) ->
    (forall a, (usp - 56 <= a)%Z -> (a + 8 <= usp)%Z -> rdn SEGS mF (Z_to_bv 64 a) 8 = rdn SEGS p7 (Z_to_bv 64 a) 8) ->
    exists regs',
      msteps SEGS (mkst regs (0x45acc : word) mF rom) (mkst regs' ra mF rom)
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 10 = getr regs 10
      /\ (forall r, ekeep r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs mF H2 HFr. pose proof Hsp.
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18.
    pose proof rd_s3 as RD19. pose proof rd_s4 as RD20. pose proof rd_s5 as RD21.
    rewrite <- HFr in RD1 by lia. rewrite <- HFr in RD8 by lia. rewrite <- HFr in RD9 by lia. rewrite <- HFr in RD18 by lia.
    rewrite <- HFr in RD19 by lia. rewrite <- HFr in RD20 by lia. rewrite <- HFr in RD21 by lia.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45acc eq_refl D_45acc)). rewrite H2. zn.
      mld2 F_45ad0 D_45ad0 ra RD1 H2.
      mld2 F_45ad4 D_45ad4 (getr regs0 8) RD8 H2.
      mld2 F_45ad8 D_45ad8 (getr regs0 9) RD9 H2.
      mld2 F_45adc D_45adc (getr regs0 18) RD18 H2.
      mld2 F_45ae0 D_45ae0 (getr regs0 19) RD19 H2.
      mld2 F_45ae4 D_45ae4 (getr regs0 20) RD20 H2.
      mld2 F_45ae8 D_45ae8 (getr regs0 21) RD21 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_45aec eq_refl D_45aec)). gr. zn.
      replace (usp - 2128 + 96 + 2032)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_45af0 eq_refl D_45af0); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r He. unfold ekeep in He.
      repeat (rewrite getr_other by (intros ->; cbn in He; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HF n K H Hret H01 H02 H010 H011 H012 HK"] Theorem imc_body :
    exists regs' m',
      msteps SEGS (mkst regs0 (0x45a10 : word) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 (s + I) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, imc_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - F \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
  Proof.
    pose proof Hsp as HU. pose proof I_facts as (Hi & _).
    destruct blk_P as (q1 & MP & P2 & P8 & P18 & P9 & P19 & P10 & PK).
    destruct (blk_S q1 PK P18 P9 P19 P10 P2 P8) as (q2 & MS & S10 & S20 & S9 & S18 & S2 & S8 & SK).
    destruct (blk_T q2 SK S10 S20 S18 S8 S2) as (q3 & MT & T9 & T10 & T18 & T2 & T8 & T11 & T12 & TK).
    (* [comment removed for export] *)
    assert (TAIL : forall q mX, sfr mX -> keep q ->
      getr q 10 = Z_to_bv 64 (s + I) -> getr q 2 = Z_to_bv 64 (usp - 2128) ->
      msteps SEGS (mkst regs0 (0x45a10 : word) mem rom) (mkst q (0x45acc : word) mX rom) ->
      exists regs' m',
        msteps SEGS (mkst regs0 (0x45a10 : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 (s + I) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, imc_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - F \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
        /\ (forall x, mem x <> None -> m' x <> None)
        /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true)).
    { intros q mX FF QK Q10 Q2 MQ. pose proof FF as (F1 & F2 & F3 & F4).
      destruct (blk_E q mX Q2) as (q6 & M6 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E10 & EK).
      { intros a Ha1 Ha2. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx.
        apply F2. lia. }
      exists q6, mX. split; [eapply msteps_trans; [exact MQ | exact M6] |].
      split; [rewrite E10; exact Q10|]. split; [exact E2|]. split; [exact E1|].
      split; [|split; [exact F1 | split; [exact F4 | exact F3]]].
      intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite E1; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite E2; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact E8|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact E9|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact E18|].
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact E19|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact E20|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact E21|].
      assert (He : ekeep r = false).
      { unfold ekeep. rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8), (bv_eqb_neq _ _ N9),
          (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21). reflexivity. }
      rewrite (EK r He). apply QK; assumption. }
    destruct (Z.lt_ge_cases I 64) as [Hsmall | Hbig].
    - (* [comment removed for export] *)
      destruct (blk_Q1 q3 p9 sfr_p9 ltac:(lia) TK T9 T18 T11 T12) as (q4 & w & M4 & A11 & A12 & A13 & A14 & A10 & A2 & A8 & A9 & A18 & AK).
      pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
      destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
      + apply (TAIL q4 p9 sfr_p9 AK); [rewrite A10; exact T10 | rewrite A2; exact T2|].
        eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MT|].
        eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_45ac8 eq_refl D_45ac8); gr; rewrite ?A14, ?getr_zero; br_eq).
        apply mst_refl.
      + assert (NZu : bv_unsigned w <> 0%Z).
        { intros E0. apply NZ. rewrite <- (zbv_self w), E0. reflexivity. }
        destruct (blk_Q2a q4 p9 sfr_p9 AK A12 A13) as (q5 & M5 & B13 & B11 & B12 & B10 & B2 & B8 & B9 & B18 & BK).
        destruct (blk_Q2b q5 p9 sfr_p9 BK) as (q6 & M6 & C10 & C2 & C8 & C9 & C18 & CK);
          [rewrite B11; exact A11 | rewrite B12; exact A12 | exact B13 |].
        apply (TAIL q6 p9 sfr_p9 CK); [rewrite C10, B10, A10; exact T10 | rewrite C2, B2, A2; exact T2|].
        eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MT|].
        eapply msteps_trans; [exact M4|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_45ac8 eq_refl D_45ac8); gr; rewrite ?A14, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M5|]. exact M6.
    - (* [comment removed for export] *)
      destruct (blk_L q3 p9 sfr_p9 Hbig TK T9 T10 T18 T2 T8 T11 T12) as (q4 & m4 & M4 & F4 & L10 & L2 & L8 & L9 & LK).
      apply (TAIL q4 m4 F4 LK L10 L2).
      eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MT|]. exact M4.
  Qed.
End IMC.

(* [comment removed for export] *)
Theorem imc_run :
  forall (F : Z) (mem rom : word -> option byte) (s n usp : Z) (buf : list byte) (K : Z),
  (IMC_FRAME <= F)%Z -> imcH F mem s n usp buf K ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 s ->
  getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' m',
    msteps SEGS (mkst regs (0x44248 : word) mem rom) (mkst regs' ra m' rom)
    /\ getr regs' 10 = Z_to_bv 64 (s + Z.of_nat (fz buf)) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, imc_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - F \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
Proof.
  intros F mem rom s n usp buf K HF H regs ra Hret H1 H2 H10 H11 H12.
  destruct (imc_body F HF mem rom s n usp buf K H regs ra Hret H1 H2 H10 H11 H12) as (regs' & m' & M & REST).
  exists regs', m'. split; [|exact REST].
  mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_44248 eq_refl D_44248)).
  exact M.
Qed.

(* [comment removed for export] *)
Lemma fz_facts : forall buf K, (0 <= K < Z.of_nat (length buf))%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf K) = 0%Z ->
  (0 <= Z.of_nat (fz buf) <= K)%Z /\ bv_unsigned (VAsanMuslStrlen.b_ buf (Z.of_nat (fz buf))) = 0%Z
  /\ (forall j, (0 <= j < Z.of_nat (fz buf))%Z -> bv_unsigned (VAsanMuslStrlen.b_ buf j) <> 0%Z).
Proof.
  intros buf K HK Hz.
  destruct (fz_spec buf (Z.to_nat K) ltac:(lia) ltac:(unfold VAsanMuslStrlen.b_ in Hz; exact Hz)) as (A & B & C).
  unfold VAsanMuslStrlen.b_. rewrite Nat2Z.id. split; [lia|]. split; [exact B|]. intros j Hj.
  replace j with (Z.of_nat (Z.to_nat j)) by lia. rewrite Nat2Z.id. apply C. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SNL.
  Variables (mem rom : word -> option byte) (s n usp : Z) (buf : list byte) (K : Z).
  Hypothesis H : imcH SNL_FRAME mem s n usp buf K.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 s.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 n.

  Let I : Z := Z.of_nat (fz buf).

  (* [comment removed for export] *)
  Definition q3 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem)).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.

  #[using="mem s n buf K H I"] Lemma Hsp' : (0x7fff8000 + SNL_FRAME + 8 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (ic_sp _ _ _ _ _ _ _ H). unfold SB in *. lia. Qed.

  #[using="s n buf K H I"] Lemma q3_out : forall x : word, (bv_unsigned x < usp - 24 \/ usp <= bv_unsigned x)%Z -> q3 x = mem x.
  Proof.
    intros x [Hx|Hx]; unfold q3; pose proof Hsp'; unfold SNL_FRAME in *.
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="H I"] Lemma imcH_q3 : imcH IMC_FRAME q3 s n (usp - 32) buf K.
  Proof.
    pose proof H as HH. pose proof Hsp'. pose proof SB_val. unfold SNL_FRAME, IMC_FRAME in *.
    pose proof (ic_nw _ _ _ _ _ _ _ H). pose proof (ic_s _ _ _ _ _ _ _ H). pose proof (ic_K _ _ _ _ _ _ _ H) as (K0 & KL & K40 & Kn & N64).
    pose proof (ic_sap _ _ _ _ _ _ _ H) as AP. pose proof (ic_shd _ _ _ _ _ _ _ H) as SH.
    assert (RB : forall (a : Z) k, (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat k <= 2 ^ 64)%Z -> (a + Z.of_nat k <= usp - 32 \/ usp <= a)%Z ->
                 rdn SEGS q3 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k).
    { intros a k Ha Hk Hap. apply rdn_ext; [rewrite zbv_u by lia; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. apply q3_out. lia. }
    destruct HH. constructor; try assumption; try (unfold IMC_FRAME; lia).
    - rewrite RB; [assumption|lia|lia|lia].
    - intros g Hg. rewrite q3_out; [apply ic_zg0; exact Hg|]. rewrite zbv_u; [lia|].
      pose proof (Z.div_le_mono (s) (s + K) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)). lia.
    - destruct ic_last0 as (b1 & M & B). exists b1. split; [|exact B]. rewrite q3_out; [exact M|]. rewrite zbv_u; [lia|].
      pose proof (Z.div_pos (s + K) 8 ltac:(lia) ltac:(lia)). lia.
    - intros a Ha Hb Hm.
      pose proof (Z.div_pos s 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_mod (SB + s / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + s / 8) 8 ltac:(lia)).
      pose proof (Z.div_mod (SB + (s + K) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (s + K) / 8) 8 ltac:(lia)).
      rewrite RB; [apply ic_words0; assumption|(ltac2:(LK.k [@ic_win0; @ic_s0; @ic_sap0; @H0; @H1; @H2; @K0; @AP; @Ha; @Hb; @H5; @H6; @H7; @H8; @KL; @SH]); lia)|cbn; (ltac2:(LK.k [@ic_win0; @ic_s0; @ic_sap0; @H0; @H1; @H2; @K0; @AP; @Ha; @Hb; @H5; @H6; @H7; @H8; @KL; @SH]); lia)|cbn; (ltac2:(LK.k [@ic_win0; @ic_s0; @ic_sap0; @H0; @H1; @H2; @K0; @AP; @Ha; @Hb; @H5; @H6; @H7; @H8; @KL; @SH]); lia)].
    - intros a Ha. unfold q3. repeat apply store_ok1_wbytes. apply ic_stk0. lia.
    - destruct ic_cel0 as (C & C1 & C2 & C5). unfold imc_cells, cells, cell in *.
      rewrite !RB by (cbn; lia). split; [exact C|]. split; [exact C1|]. split; [exact C2|].
      intros i Hi. rewrite q3_out; [exact (C5 i Hi)|]. rewrite zbv_u by lia. lia.
  Qed.

  Ltac msd F D a v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption | apply (f_equal (Z_to_bv 64)); lia]
                 | apply store_ok8_bytes; [lia|lia|]; intros j Hj; unfold q3; repeat apply store_ok1_wbytes;
                   apply (ic_stk _ _ _ _ _ _ _ H); unfold SNL_FRAME; lia ]).
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp'; unfold SNL_FRAME in *; unfold q3;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).
  #[using="s n buf K H I"] Lemma rd_ra' : rdn SEGS q3 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).              Proof. rd_slot. Qed.
  #[using="s n buf K H I"] Lemma rd_s0' : rdn SEGS q3 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)). Proof. rd_slot. Qed.
  #[using="s n buf K H I"] Lemma rd_s1' : rdn SEGS q3 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)). Proof. rd_slot. Qed.

  #[using="s n K H Hret H01 H02 H010 H011"] Theorem strnlen_body :
    exists regs' m',
      msteps SEGS (mkst regs0 (0xa4a38 : word) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 I /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, imc_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - SNL_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
  Proof.
    pose proof Hsp' as HU. unfold SNL_FRAME in HU. pose proof (ic_s _ _ _ _ _ _ _ H) as Hs. pose proof (ic_nw _ _ _ _ _ _ _ H).
    pose proof (ic_K _ _ _ _ _ _ _ H) as (K0 & KL & K40 & Kn & N64).
    destruct (fz_facts buf K ltac:(lia) (ic_zero_K _ _ _ _ _ _ _ H)) as (I1 & _). fold I in I1.
    (* [comment removed for export] *)
    evar (rr : bvmap 5 word).
    edestruct (imc_run IMC_FRAME q3 rom s n (usp - 32) buf K ltac:(lia) imcH_q3 rr (0xa4a5c : word) ret_ok_1376a8)
      as (r1 & m1 & M1 & R10 & R2 & R1 & K1 & M1o & M1g & M1s); cycle -1.
    { assert (SL : forall a, (usp - 24 <= a)%Z -> (a + 8 <= usp)%Z -> rdn SEGS m1 (Z_to_bv 64 a) 8 = rdn SEGS q3 (Z_to_bv 64 a) 8).
      { intros a Ha Hb. apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx.
        apply M1o. lia. }
      pose proof rd_ra' as RD1. pose proof rd_s0' as RD8. pose proof rd_s1' as RD9.
      rewrite <- SL in RD1 by lia. rewrite <- SL in RD8 by lia. rewrite <- SL in RD9 by lia.
      eexists. exists m1. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a38 eq_refl D_a4a38)). rewrite H02. zn.
        msd F_a4a3c D_a4a3c (usp - 8)%Z ra H02.
        msd F_a4a40 D_a4a40 (usp - 16)%Z (getr regs0 8) H02.
        msd F_a4a44 D_a4a44 (usp - 24)%Z (getr regs0 9) H02.
        change (wbytes _ _ _) with q3.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a48 eq_refl D_a4a48)). gr. rewrite H011. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a4c eq_refl D_a4a4c)). gr. rewrite H010. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a50 eq_refl D_a4a50)). rewrite getr_zero. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a54 eq_refl D_a4a54)). gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_jal_link _ _ _ _ _ _ _ _ F_a4a58 eq_refl D_a4a58)). rewrite lit_1376a8.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_a4a5c eq_refl D_a4a5c); gr; rewrite ?R10, ?getr_zero; br_eq).
        mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_a4a60 eq_refl D_a4a60)). gr. rewrite R10.
        rewrite (K1 9) by reflexivity. subst rr. gr. rewrite v_sub_zbv by lia.
        replace (s + Z.of_nat (fz buf) - s)%Z with I by (unfold I; lia).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a64 eq_refl D_a4a64)). gr. zn. rewrite ?Z.add_0_r.
        mld2 F_a4a68 D_a4a68 ra RD1 R2.
        mld2 F_a4a6c D_a4a6c (getr regs0 8) RD8 R2.
        mld2 F_a4a70 D_a4a70 (getr regs0 9) RD9 R2.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_a4a74 eq_refl D_a4a74)). gr. rewrite R2. zn.
        replace (usp - 32 + 32)%Z with usp by lia.
        eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_a4a78 eq_refl D_a4a78); gr; reflexivity |].
        imm_norm. rewrite Hret. apply mst_refl.
      - gr. reflexivity.
      - gr. reflexivity.
      - gr. reflexivity.
      - intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | N1]; [gr; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [gr; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [gr; reflexivity|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [gr; reflexivity|].
        destruct (bv_eq_dec _ r 10) as [-> | N10]; [cbn in Hr; discriminate|].
        repeat (rewrite getr_other by (intros ->; first [congruence | cbn in Hr; discriminate Hr])).
        rewrite (K1 r Hr). subst rr.
        repeat (rewrite getr_other by (intros ->; first [congruence | cbn in Hr; discriminate Hr])). reflexivity.
      - intros x Hx. unfold SNL_FRAME in Hx. rewrite M1o by (unfold IMC_FRAME; lia). apply q3_out. lia.
      - intros x Hx. apply M1g. unfold q3. repeat apply wbytes_keep. exact Hx.
      - intros x Hx. apply M1s. unfold q3. repeat apply store_ok1_wbytes. exact Hx. }
    all: subst rr; gr; try reflexivity; try assumption; try (apply (f_equal (Z_to_bv 64)); lia).
  Qed.
End SNL.

Theorem strnlen_run :
  forall (mem rom : word -> option byte) (s n usp : Z) (buf : list byte) (K : Z),
  imcH SNL_FRAME mem s n usp buf K ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' m',
    msteps SEGS (mkst regs (0xa4a38 : word) mem rom) (mkst regs' ra m' rom)
    /\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (fz buf)) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, imc_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - SNL_FRAME \/ usp <= bv_unsigned x)%Z -> m' x = mem x)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m' x 1 = true).
Proof.
  intros mem rom s n usp buf K H regs ra Hret H1 H2 H10 H11.
  exact (strnlen_body mem rom s n usp buf K H regs ra Hret H1 H2 H10 H11).
Qed.
