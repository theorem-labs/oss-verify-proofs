(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac WalkTac L5Defs Bs0_code_36bd8_36cac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSRVOH.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Definition TABLE : Z := 80432.

(* [comment removed for export] *)
Definition tabb (b : Z) : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2 with Some bs => bs | None => [] end.
Definition hexv (b : Z) : word := v_lh (Z_to_bv 64 (bytes_le_to_Z (tabb b))).
Definition tab_clear (M : mem) : Prop := forall x : word, TABLE <= bv_unsigned x < TABLE + 512 -> M x = None.

Lemma tabb_all : forallb (fun i => let b := Z.of_nat i in
    match rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2 with
    | Some bs => Nat.eqb (length bs) 2 && (0 <=? bytes_le_to_Z bs) && (bytes_le_to_Z bs <? 65536) | None => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tabb_ok b : 0 <= b < 256 -> rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2 = Some (tabb b) /\ 0 <= bytes_le_to_Z (tabb b) < 65536.
Proof.
  intros Hb. pose proof tabb_all as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat b) ltac:(apply in_seq; lia)). cbv beta zeta in A. rewrite Z2Nat.id in A by lia. unfold tabb.
  destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (TABLE + 2 * b)) 2) as [bs|]; [| discriminate A].
  apply andb_prop in A as [A B2]. apply andb_prop in A as [A1 A2]. split; [reflexivity|]. apply Z.leb_le in A2. apply Z.ltb_lt in B2. lia.
Qed.
Lemma rdn_clear2 (M : mem) a : tab_clear M -> TABLE <= a -> a + 2 <= TABLE + 512 ->
  rdn RSEGS M (Z_to_bv 64 a) 2 = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 2.
Proof.
  intros TC H1 H2. unfold tab_clear, TABLE in *. cbn [rdn].
  rewrite (TC (Z_to_bv 64 a)) by (rewrite L5.unsigned_lit by lia; lia).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (apply bv_eq; rewrite u_add1 by (rewrite L5.unsigned_lit by lia; lia); rewrite !L5.unsigned_lit by lia; reflexivity).
  rewrite (TC (Z_to_bv 64 (a + 1))) by (rewrite L5.unsigned_lit by lia; lia). reflexivity.
Qed.
Lemma lh_tab (fx : FPState) R (M : mem) pc W rd rs b :
  fetch_word RSEGS pc = Some W -> is_ecall W = false -> decode_any W = Some (Load SZ2 true rd rs 0, 4%Z) ->
  getr R rs = Z_to_bv 64 (TABLE + 2 * b) -> 0 <= b < 256 -> tab_clear M -> bv_eqb rd 0 = false ->
  RiscvSemantics.step RSEGS (@mkst fx R pc M (seg_rom RSEGS)) = MachineOk (@mkst fx (regupd R rd (hexv b)) (v_addi pc 4) M (seg_rom RSEGS)).
Proof.
  intros HF HE HD Hrs Hb TC Hrd. destruct (tabb_ok b Hb) as (RD & RG).
  rewrite (step_lh RSEGS R pc M (seg_rom RSEGS) W rd rs 0 (tabb b) (Z_to_bv 64 (bytes_le_to_Z (tabb b))) HF HE HD).
  - rewrite Hrd. reflexivity.
  - rewrite Hrs. change (bv_signed (0 : bv 12)) with 0. unfold v_addi. rewrite Z.add_0_r, L5.unsigned_lit by (unfold TABLE; lia).
    rewrite (rdn_clear2 M _ TC) by (unfold TABLE; lia). exact RD.
  - rewrite L5.unsigned_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint memw (M : mem) (p : Z) (b : nat -> Z) (k : nat) : mem :=
  match k with
  | O => M
  | S k' => wbytes (memw M p b k') (Z_to_bv 64 (p + 2 * Z.of_nat k')) (word_to_le_bytes 2 (hexv (b k')))
  end.
Lemma memw_out (M : mem) p b k (x : word) : 0 <= p -> p + 24 <= 2 ^ 64 -> (k <= 12)%nat ->
  (bv_unsigned x < p \/ p + 24 <= bv_unsigned x) -> memw M p b k x = M x.
Proof.
  intros H1 H2 Hk Hx. induction k as [|k IH]; [reflexivity|]. cbn [memw].
  assert (LEN : Z.of_nat (length (word_to_le_bytes 2 (hexv (b k)))) = 2) by (rewrite length_N_to_le_bytes; reflexivity).
  destruct Hx as [Hx|Hx].
  - rewrite wbytes_below; [apply IH; lia| rewrite LEN, L5.unsigned_lit by lia; lia| rewrite L5.unsigned_lit by lia; lia].
  - rewrite wbytes_above; [apply IH; lia| rewrite LEN, L5.unsigned_lit by lia; lia].
Qed.
Lemma memw_grows (M : mem) p b k : mem_grows M (memw M p b k).
Proof.
  induction k as [|k IH]; [apply mem_grows_refl|]. cbn [memw]. eapply mem_grows_trans; [exact IH| apply wbytes_grows].
Qed.
Lemma tab_clear_w (M : mem) p b k : (p + 24 <= TABLE \/ TABLE + 512 <= p) /\ 0 <= p /\ p + 24 <= 2 ^ 64 -> tab_clear M -> (k <= 12)%nat -> tab_clear (memw M p b k).
Proof. intros Hp TC Hk x Hx. unfold tab_clear, TABLE in *. rewrite memw_out; [apply TC; exact Hx| lia| lia| exact Hk| lia]. Qed.
Lemma rdn_memw (M : mem) p b k a n : 0 <= p -> p + 24 <= 2 ^ 64 -> (k <= 12)%nat -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (a + Z.of_nat n <= p \/ p + 24 <= a) -> rdn RSEGS (memw M p b k) (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
Proof.
  intros H1 H2 Hk. revert a. induction n as [|n IH]; intros a Ha1 Ha2 Hd; [reflexivity|].
  cbn [rdn]. rewrite memw_out; [| lia| lia| exact Hk| rewrite L5.unsigned_lit by lia; lia].
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (apply bv_eq; rewrite u_add1 by (rewrite L5.unsigned_lit by lia; lia); rewrite !L5.unsigned_lit by lia; reflexivity).
  rewrite IH by lia. reflexivity.
Qed.

Lemma v_slli_1 b : 0 <= b < 2 ^ 62 -> v_slli (Z_to_bv 64 b) (bv_unsigned (1%bv : bv 6)) = Z_to_bv 64 (2 * b).
Proof. intros Hb. change (bv_unsigned (1%bv : bv 6)) with 1. unfold v_slli. rewrite L5.unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.
Lemma v_add_lit a c : 0 <= a -> 0 <= c -> a + c < 2 ^ 64 -> v_add (Z_to_bv 64 a) (Z_to_bv 64 c) = Z_to_bv 64 (a + c).
Proof. intros H1 H2 H3. unfold v_add. rewrite !L5.unsigned_lit by lia. reflexivity. Qed.
Lemma v_addi_lit a (i : Z) : 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros H. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity. Qed.

Local Ltac hstep tac := eapply mst_step; [reflexivity| tac| ]; step_simpl.

Lemma oid_hex (fx : FPState) (R : bvmap 5 word) (M : mem) (sp p : Z) (b : nat -> Z) :
  getr R 11%bv = Z_to_bv 64 p -> getr R 2%bv = Z_to_bv 64 sp ->
  getr R 21%bv = Z_to_bv 64 (b 0%nat) -> getr R 20%bv = Z_to_bv 64 (b 1%nat) -> getr R 19%bv = Z_to_bv 64 (b 2%nat) ->
  getr R 27%bv = Z_to_bv 64 (b 3%nat) -> getr R 26%bv = Z_to_bv 64 (b 4%nat) -> getr R 25%bv = Z_to_bv 64 (b 5%nat) ->
  getr R 24%bv = Z_to_bv 64 (b 6%nat) -> getr R 23%bv = Z_to_bv 64 (b 7%nat) -> getr R 22%bv = Z_to_bv 64 (b 8%nat) ->
  L5.u64_at RSEGS M sp (b 9%nat) -> L5.u64_at RSEGS M (sp + 8) (b 10%nat) -> L5.u64_at RSEGS M (sp + 16) (b 11%nat) ->
  (forall i, (i < 12)%nat -> 0 <= b i < 256) ->
  tab_clear M -> L5.writable RSEGS M p 24 ->
  (p + 24 <= TABLE \/ TABLE + 512 <= p) /\ 0 <= p /\ p + 24 <= 2 ^ 64 -> (p + 24 <= sp \/ sp + 24 <= p) -> 0 <= sp -> sp + 24 < 2 ^ 64 ->
  exists R',
    msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36cd4) M (seg_rom RSEGS)) (@mkst fx R' (Z_to_bv 64 0x36da8) (memw M p b 12) (seg_rom RSEGS))
    /\ getr R' 1%bv = getr R 1%bv /\ getr R' 2%bv = getr R 2%bv /\ getr R' 3%bv = getr R 3%bv /\ getr R' 4%bv = getr R 4%bv /\ getr R' 8%bv = getr R 8%bv
    /\ getr R' 9%bv = getr R 9%bv /\ getr R' 10%bv = getr R 10%bv /\ getr R' 11%bv = getr R 11%bv /\ getr R' 18%bv = getr R 18%bv.
Proof.
  intros X11 X2 Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 S9 S10 S11 HB TC0 WP Hp Hsp Hsp0 Hsp1.
  pose proof TC0 as TC.
  assert (sokw : forall (m : mem) k, mem_grows M m -> (k <= 11)%nat -> store_ok RSEGS m (Z_to_bv 64 (p + 2 * Z.of_nat k)) 2 = true).
  { intros m k Hg Hk. apply (store_ok_mono RSEGS 2 M m _ Hg). apply (WP (2 * Z.of_nat k) 2%nat); lia. }
  eexists. split.
  - unfold L5.u64_at in S9, S10, S11. change M with (memw M p b 0) at 1.
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 0%nat)); [exact F_36c7c| reflexivity| exact D_36c7c| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 0%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_auipc_at RSEGS) with (v := Z_to_bv 64 81112); [exact F_36c80| reflexivity| exact D_36c80| reflexivity| vm_compute; reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_addi_at RSEGS) with (v := Z_to_bv 64 80432); [exact F_36c84| reflexivity| exact D_36c84| reflexivity| gres; vm_compute; reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 0%nat)); [exact F_36c88| reflexivity| exact D_36c88| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 0%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 0%nat) F_36c8c eq_refl D_36c8c); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 1%nat)); [exact F_36c90| reflexivity| exact D_36c90| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 1%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 1%nat)); [exact F_36c94| reflexivity| exact D_36c94| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 1%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 0)) (v := hexv (b 0%nat)); [exact F_36c98| reflexivity| exact D_36c98| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 0) with (p + 2 * Z.of_nat 0) by lia; apply (sokw _ 0%nat (memw_grows M p b 0) ltac:(lia))]).
    change (wbytes (memw M p b 0) (Z_to_bv 64 (p + 0)) (word_to_le_bytes 2 (hexv (b 0%nat)))) with (memw M p b 1).
    clear TC. assert (TC : tab_clear (memw M p b 1)) by (apply (tab_clear_w M p b 1 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 1%nat) F_36c9c eq_refl D_36c9c); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 2%nat)); [exact F_36ca0| reflexivity| exact D_36ca0| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 2%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 2%nat)); [exact F_36ca4| reflexivity| exact D_36ca4| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 2%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 2)) (v := hexv (b 1%nat)); [exact F_36ca8| reflexivity| exact D_36ca8| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 2) with (p + 2 * Z.of_nat 1) by lia; apply (sokw _ 1%nat (memw_grows M p b 1) ltac:(lia))]).
    change (wbytes (memw M p b 1) (Z_to_bv 64 (p + 2)) (word_to_le_bytes 2 (hexv (b 1%nat)))) with (memw M p b 2).
    clear TC. assert (TC : tab_clear (memw M p b 2)) by (apply (tab_clear_w M p b 2 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 2%nat) F_36cac eq_refl D_36cac); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 3%nat)); [exact F_36cb0| reflexivity| exact D_36cb0| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 3%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 3%nat)); [exact F_36cb4| reflexivity| exact D_36cb4| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 3%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 4)) (v := hexv (b 2%nat)); [exact F_36cb8| reflexivity| exact D_36cb8| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 4) with (p + 2 * Z.of_nat 2) by lia; apply (sokw _ 2%nat (memw_grows M p b 2) ltac:(lia))]).
    change (wbytes (memw M p b 2) (Z_to_bv 64 (p + 4)) (word_to_le_bytes 2 (hexv (b 2%nat)))) with (memw M p b 3).
    clear TC. assert (TC : tab_clear (memw M p b 3)) by (apply (tab_clear_w M p b 3 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 3%nat) F_36cbc eq_refl D_36cbc); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 4%nat)); [exact F_36cc0| reflexivity| exact D_36cc0| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 4%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 4%nat)); [exact F_36cc4| reflexivity| exact D_36cc4| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 4%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 6)) (v := hexv (b 3%nat)); [exact F_36cc8| reflexivity| exact D_36cc8| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 6) with (p + 2 * Z.of_nat 3) by lia; apply (sokw _ 3%nat (memw_grows M p b 3) ltac:(lia))]).
    change (wbytes (memw M p b 3) (Z_to_bv 64 (p + 6)) (word_to_le_bytes 2 (hexv (b 3%nat)))) with (memw M p b 4).
    clear TC. assert (TC : tab_clear (memw M p b 4)) by (apply (tab_clear_w M p b 4 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 4%nat) F_36ccc eq_refl D_36ccc); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 5%nat)); [exact F_36cd0| reflexivity| exact D_36cd0| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 5%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 5%nat)); [exact F_36cd4| reflexivity| exact D_36cd4| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 5%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 8)) (v := hexv (b 4%nat)); [exact F_36cd8| reflexivity| exact D_36cd8| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 8) with (p + 2 * Z.of_nat 4) by lia; apply (sokw _ 4%nat (memw_grows M p b 4) ltac:(lia))]).
    change (wbytes (memw M p b 4) (Z_to_bv 64 (p + 8)) (word_to_le_bytes 2 (hexv (b 4%nat)))) with (memw M p b 5).
    clear TC. assert (TC : tab_clear (memw M p b 5)) by (apply (tab_clear_w M p b 5 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 5%nat) F_36cdc eq_refl D_36cdc); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 6%nat)); [exact F_36ce0| reflexivity| exact D_36ce0| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 6%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 6%nat)); [exact F_36ce4| reflexivity| exact D_36ce4| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 6%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 10)) (v := hexv (b 5%nat)); [exact F_36ce8| reflexivity| exact D_36ce8| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 10) with (p + 2 * Z.of_nat 5) by lia; apply (sokw _ 5%nat (memw_grows M p b 5) ltac:(lia))]).
    change (wbytes (memw M p b 5) (Z_to_bv 64 (p + 10)) (word_to_le_bytes 2 (hexv (b 5%nat)))) with (memw M p b 6).
    clear TC. assert (TC : tab_clear (memw M p b 6)) by (apply (tab_clear_w M p b 6 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 6%nat) F_36cec eq_refl D_36cec); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 7%nat)); [exact F_36cf0| reflexivity| exact D_36cf0| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 7%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 7%nat)); [exact F_36cf4| reflexivity| exact D_36cf4| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 7%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 12)) (v := hexv (b 6%nat)); [exact F_36cf8| reflexivity| exact D_36cf8| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 12) with (p + 2 * Z.of_nat 6) by lia; apply (sokw _ 6%nat (memw_grows M p b 6) ltac:(lia))]).
    change (wbytes (memw M p b 6) (Z_to_bv 64 (p + 12)) (word_to_le_bytes 2 (hexv (b 6%nat)))) with (memw M p b 7).
    clear TC. assert (TC : tab_clear (memw M p b 7)) by (apply (tab_clear_w M p b 7 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 7%nat) F_36cfc eq_refl D_36cfc); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 8%nat)); [exact F_36d00| reflexivity| exact D_36d00| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 8%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 8%nat)); [exact F_36d04| reflexivity| exact D_36d04| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 8%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 14)) (v := hexv (b 7%nat)); [exact F_36d08| reflexivity| exact D_36d08| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 14) with (p + 2 * Z.of_nat 7) by lia; apply (sokw _ 7%nat (memw_grows M p b 7) ltac:(lia))]).
    change (wbytes (memw M p b 7) (Z_to_bv 64 (p + 14)) (word_to_le_bytes 2 (hexv (b 7%nat)))) with (memw M p b 8).
    clear TC. assert (TC : tab_clear (memw M p b 8)) by (apply (tab_clear_w M p b 8 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 8%nat) F_36d0c eq_refl D_36d0c); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_ld RSEGS) with (bs := word_to_le_bytes 8 (Z_to_bv 64 (b 9%nat))) (v := Z_to_bv 64 (b 9%nat)); [exact F_36d10| reflexivity| exact D_36d10| gres; imm_norm; rewrite X2; rewrite v_addi_lit by lia; rewrite ?Z.add_0_r; rewrite (rdn_memw M p b 8) by lia; exact S9| apply bytes_le_to_Z_8]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 9%nat)); [exact F_36d14| reflexivity| exact D_36d14| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 9%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 9%nat)); [exact F_36d18| reflexivity| exact D_36d18| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 9%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 16)) (v := hexv (b 8%nat)); [exact F_36d1c| reflexivity| exact D_36d1c| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 16) with (p + 2 * Z.of_nat 8) by lia; apply (sokw _ 8%nat (memw_grows M p b 8) ltac:(lia))]).
    change (wbytes (memw M p b 8) (Z_to_bv 64 (p + 16)) (word_to_le_bytes 2 (hexv (b 8%nat)))) with (memw M p b 9).
    clear TC. assert (TC : tab_clear (memw M p b 9)) by (apply (tab_clear_w M p b 9 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 9%nat) F_36d20 eq_refl D_36d20); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_ld RSEGS) with (bs := word_to_le_bytes 8 (Z_to_bv 64 (b 10%nat))) (v := Z_to_bv 64 (b 10%nat)); [exact F_36d24| reflexivity| exact D_36d24| gres; imm_norm; rewrite X2; rewrite v_addi_lit by lia; rewrite ?Z.add_0_r; rewrite (rdn_memw M p b 9) by lia; exact S10| apply bytes_le_to_Z_8]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 10%nat)); [exact F_36d28| reflexivity| exact D_36d28| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 10%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 10%nat)); [exact F_36d2c| reflexivity| exact D_36d2c| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 10%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 18)) (v := hexv (b 9%nat)); [exact F_36d30| reflexivity| exact D_36d30| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 18) with (p + 2 * Z.of_nat 9) by lia; apply (sokw _ 9%nat (memw_grows M p b 9) ltac:(lia))]).
    change (wbytes (memw M p b 9) (Z_to_bv 64 (p + 18)) (word_to_le_bytes 2 (hexv (b 9%nat)))) with (memw M p b 10).
    clear TC. assert (TC : tab_clear (memw M p b 10)) by (apply (tab_clear_w M p b 10 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 10%nat) F_36d34 eq_refl D_36d34); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_ld RSEGS) with (bs := word_to_le_bytes 8 (Z_to_bv 64 (b 11%nat))) (v := Z_to_bv 64 (b 11%nat)); [exact F_36d38| reflexivity| exact D_36d38| gres; imm_norm; rewrite X2; rewrite v_addi_lit by lia; rewrite ?Z.add_0_r; rewrite (rdn_memw M p b 10) by lia; exact S11| apply bytes_le_to_Z_8]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_slli_at RSEGS) with (v := Z_to_bv 64 (2 * b 11%nat)); [exact F_36d3c| reflexivity| exact D_36d3c| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_slli_1; pose proof (HB 11%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 20)) (v := hexv (b 10%nat)); [exact F_36d40| reflexivity| exact D_36d40| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 20) with (p + 2 * Z.of_nat 10) by lia; apply (sokw _ 10%nat (memw_grows M p b 10) ltac:(lia))]).
    change (wbytes (memw M p b 10) (Z_to_bv 64 (p + 20)) (word_to_le_bytes 2 (hexv (b 10%nat)))) with (memw M p b 11).
    clear TC. assert (TC : tab_clear (memw M p b 11)) by (apply (tab_clear_w M p b 11 Hp TC0); lia).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_add_at RSEGS) with (v := Z_to_bv 64 (80432 + 2 * b 11%nat)); [exact F_36d44| reflexivity| exact D_36d44| reflexivity| gres; rewrite ?Q0, ?Q1, ?Q2, ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8; apply v_add_lit; pose proof (HB 11%nat ltac:(lia)); lia]).
    (* [comment removed for export] *)
    hstep ltac:(apply (lh_tab fx _ _ _ _ _ _ (b 11%nat) F_36d48 eq_refl D_36d48); [gres; reflexivity| apply HB; clear; lia| exact TC| reflexivity]).
    (* [comment removed for export] *)
    hstep ltac:(eapply (step_sh_at RSEGS) with (a := Z_to_bv 64 (p + 22)) (v := hexv (b 11%nat)); [exact F_36d4c| reflexivity| exact D_36d4c| gres; imm_norm; rewrite X11; rewrite v_addi_lit by lia; f_equal; lia| gres; reflexivity| replace (p + 22) with (p + 2 * Z.of_nat 11) by lia; apply (sokw _ 11%nat (memw_grows M p b 11) ltac:(lia))]).
    change (wbytes (memw M p b 11) (Z_to_bv 64 (p + 22)) (word_to_le_bytes 2 (hexv (b 11%nat)))) with (memw M p b 12).
    clear TC. assert (TC : tab_clear (memw M p b 12)) by (apply (tab_clear_w M p b 12 Hp TC0); lia).
    lazymatch goal with |- msteps _ (mkst _ ?pcl _ _) _ => replace pcl with (Z_to_bv 64 0x36da8) by (apply bv_eq; vm_compute; reflexivity) end.
    apply mst_refl.
  - gres. repeat split; reflexivity.
Qed.
End PNSRVOH.
