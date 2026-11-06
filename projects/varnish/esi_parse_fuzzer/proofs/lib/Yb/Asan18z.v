(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec ShapeAlg SpinAlg CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require RefMocc AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan Asanqlm.

Module Asanvp3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk SymExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SymExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition PW0 : bv 32 := 0x00465713.  (* [comment removed for export] *)
Definition PW1 : bv 32 := 0xfff54793.  (* [comment removed for export] *)
Definition PW2 : bv 32 := 0x00150513.  (* [comment removed for export] *)
Definition PW3 : bv 32 := 0x00279793.  (* [comment removed for export] *)
Definition PW4 : bv 32 := 0x00f587b3.  (* [comment removed for export] *)
Definition PW5 : bv 32 := 0x00e7a023.  (* [comment removed for export] *)
Definition PW6 : bv 32 := 0x01560633.  (* [comment removed for export] *)
Definition PW7 : bv 32 := 0xff3562e3.  (* [comment removed for export] *)

Lemma PD0 : decode_any PW0 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z). Proof. vm_refl. Qed.
Lemma PD1 : decode_any PW1 = Some (OpImm ALU_XOR 15 10 4095, 4%Z). Proof. vm_refl. Qed.
Lemma PD2 : decode_any PW2 = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl. Qed.
Lemma PD3 : decode_any PW3 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z). Proof. vm_refl. Qed.
Lemma PD4 : decode_any PW4 = Some (Op ALU_ADD 15 11 15, 4%Z). Proof. vm_refl. Qed.
Lemma PD5 : decode_any PW5 = Some (Store SZ4 15 14 0, 4%Z). Proof. vm_refl. Qed.
Lemma PD6 : decode_any PW6 = Some (Op ALU_ADD 12 12 21, 4%Z). Proof. vm_refl. Qed.
Lemma PD7 : decode_any PW7 = Some (Branch BC_LTU 10 19 8164, 4%Z). Proof. vm_refl. Qed.

(* [comment removed for export] *)
Fixpoint pf_mem (mem : word -> option byte) (e c s i : Z) (k : nat) : word -> option byte :=
  match k with
  | O => mem
  | S k' => pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))))
                   e (c + s) s (i + 1) k'
  end.

(* [comment removed for export] *)
Fixpoint pf_bytes (c s : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => Z_to_le_bytes 4 ((c + Z.of_nat k' * s) / 16) ++ pf_bytes c s k'
  end.

Lemma pf_bytes_length : forall c s k, length (pf_bytes c s k) = (4 * k)%nat.
Proof. intros c s k. induction k as [|k IH]; cbn [pf_bytes length]; [reflexivity|]. rewrite length_app, length_Z_to_le_bytes, IH. lia. Qed.

Lemma pf_bytes_nth : forall c s k j t,
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  nth (Z.to_nat (4 * j) + t) (pf_bytes c s k) (Z_to_bv 8 0) = nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0).
Proof.
  intros c s k. induction k as [|k IH]; intros j t Hj Ht; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite app_nth1 by (rewrite length_Z_to_le_bytes; lia). replace (Z.to_nat (4 * 0) + t)%nat with t by lia. f_equal. f_equal. f_equal. lia.
  - rewrite app_nth2 by (rewrite length_Z_to_le_bytes; lia). rewrite length_Z_to_le_bytes.
    replace (Z.to_nat (4 * j) + t - 4)%nat with (Z.to_nat (4 * (j - 1)) + t)%nat by lia.
    rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pf_bytes_cell : forall c s k j,
  (0 <= j < Z.of_nat k)%Z ->
  firstn 4 (skipn (Z.to_nat (4 * j)) (pf_bytes c s k)) = Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16).
Proof.
  intros c s k. induction k as [|k IH]; intros j Hj; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - replace (Z.to_nat (4 * 0)) with 0%nat by lia. rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). f_equal. f_equal. lia.
  - rewrite skipn_app, length_Z_to_le_bytes. rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
    replace (Z.to_nat (4 * j) - 4)%nat with (Z.to_nat (4 * (j - 1)))%nat by lia.
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition popfree_spec (SEGS : list Segment) (p : Z) : Prop :=
  forall regs mem (i e c s n : Z),
    getr regs 10%bv = Z_to_bv 64 i -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 c ->
    getr regs 21%bv = Z_to_bv 64 s -> getr regs 19%bv = Z_to_bv 64 n ->
    (0 <= i < n)%Z -> (4 * n <= e < 2 ^ 64)%Z -> (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
    store_ok SEGS mem (Z_to_bv 64 (e - 4 * n)) (Z.to_nat (4 * (n - i))) = true ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 p) mem (seg_rom SEGS))
                  (mkst regs' (Z_to_bv 64 (p + 32)) (wbytes mem (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) (seg_rom SEGS))
      /\ getr regs' 10%bv = Z_to_bv 64 n /\ getr regs' 12%bv = Z_to_bv 64 (c + (n - i) * s)
      /\ getr regs' 14%bv = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15%bv = Z_to_bv 64 (e - 4 * n)
      /\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).

Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.                       (* [comment removed for export] *)
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.

(* [comment removed for export] *)
Definition iter_regs (regs : bvmap 5 word) (i e c s : Z) : bvmap 5 word :=
  regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 (c / 16))) 10 (Z_to_bv 64 (i + 1)))
                 15 (Z_to_bv 64 (e - 4 * (i + 1)))) 12 (Z_to_bv 64 (c + s)).

Ltac red_if :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (if bv_eqb a b then x else y) with x
      | false => change (if bv_eqb a b then x else y) with y
      end
  end.

Lemma u64_of_Z : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

#[using="HF7 HF6 HF5 HF4 HF3 HF2 HF1 HF0 Hp"] Lemma pf_iter : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i + 1 <= n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + s < 2 ^ 64)%Z ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (if (i + 1 <? n)%Z then p else p + 32))
                      (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
    /\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 e /\ getr regs' 12 = Z_to_bv 64 (c + s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 (c / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hok.
  destruct Hp as [Hp0 Hp1].
  (* [comment removed for export] *)
  assert (V14 : v_srli (Z_to_bv 64 c) (bv_unsigned (4 : bv 6)) = Z_to_bv 64 (c / 16)).
  { unfold v_srli. rewrite u64_of_Z by lia. change (bv_unsigned (4 : bv 6)) with 4%Z.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (V15a : v_xori (Z_to_bv 64 i) (bv_signed (4095 : bv 12)) = Z_to_bv 64 (2 ^ 64 - 1 - i)).
  { unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (bv_signed (4095 : bv 12))) with (2 ^ 64 - 1)%Z.
    rewrite AX2S.lxor_ones64 by lia. reflexivity. }
  assert (V10 : v_addi (Z_to_bv 64 i) (bv_signed (1 : bv 12)) = Z_to_bv 64 (i + 1)).
  { change (bv_signed (1 : bv 12)) with 1%Z. apply v_addi_lit. }
  assert (V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) (bv_unsigned (2 : bv 6)) = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)).
  { unfold v_slli. rewrite u64_of_Z by lia. change (bv_unsigned (2 : bv 6)) with 2%Z.
    rewrite Z.shiftl_mul_pow2 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal. lia. }
  assert (V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { unfold v_add. rewrite u64_of_Z by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    rewrite Z.add_mod_idemp_r by lia.
    replace (e + (2 ^ 66 - 4 - 4 * i))%Z with ((e - 4 * (i + 1)) + 4 * 2 ^ 64)%Z by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) (bv_signed (0 : bv 12)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_lit. f_equal. lia. }
  assert (V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s)).
  { unfold v_add. rewrite !u64_of_Z by lia. reflexivity. }
  eexists. split.
  - eapply mst_step; [reflexivity | eapply (step_srli segs); [exact HF0 | reflexivity | exact PD0] |].
    red_if. rewrite v_addi_lit, H12, V14.
    eapply mst_step; [reflexivity | eapply (step_xori segs); [exact HF1 | reflexivity | exact PD1] |].
    red_if. rewrite v_addi_lit. replace (p + 4 + 4)%Z with (p + 8)%Z by lia. gr. rewrite H10, V15a.
    eapply mst_step; [reflexivity | eapply (step_addi segs); [exact HF2 | reflexivity | exact PD2] |].
    red_if. rewrite v_addi_lit. replace (p + 8 + 4)%Z with (p + 12)%Z by lia. gr. rewrite H10, V10.
    eapply mst_step; [reflexivity | eapply (step_slli segs); [exact HF3 | reflexivity | exact PD3] |].
    red_if. rewrite v_addi_lit. replace (p + 12 + 4)%Z with (p + 16)%Z by lia. gr. rewrite V15b.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF4 | reflexivity | exact PD4] |].
    red_if. rewrite v_addi_lit. replace (p + 16 + 4)%Z with (p + 20)%Z by lia. gr. rewrite H11, V15c.
    eapply mst_step; [reflexivity | eapply (step_sw_val segs); [exact HF5 | reflexivity | exact PD5 | gr; rewrite Vst; exact Hok] |].
    rewrite v_addi_lit. replace (p + 20 + 4)%Z with (p + 24)%Z by lia. gr. rewrite Vst.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF6 | reflexivity | exact PD6] |].
    red_if. rewrite v_addi_lit. replace (p + 24 + 4)%Z with (p + 28)%Z by lia. gr. rewrite H12, H21, V12.
    destruct (Z.ltb (i + 1) n) eqn:Hlt.
    + eapply mst_step; [reflexivity | eapply (step_bltu_tk segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite btgt_lit. change (bv_signed (8164 : bv 13)) with (-28)%Z.
      replace (p + 28 + -28)%Z with p by lia. apply mst_refl.
    + eapply mst_step; [reflexivity | eapply (step_bltu_ft segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite v_addi_lit. replace (p + 28 + 4)%Z with (p + 32)%Z by lia. apply mst_refl.
  - gr. rewrite H11, H21, H19.
    repeat (split; [reflexivity|]).
    intros r Hr10 Hr12 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.

#[using="HF7 HF6 HF5 HF4 HF3 HF2 HF1 HF0 Hp"] Lemma pf_loop : forall k regs mem rom i e c s n,
  n = (i + Z.of_nat (S k))%Z ->
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + Z.of_nat (S k) * s < 2 ^ 64)%Z ->
  (forall j, (i <= j < n)%Z -> RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true) ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (S k)) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + Z.of_nat (S k) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + Z.of_nat k * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  induction k as [|k IH]; intros regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok.
  - (* [comment removed for export] *)
    change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    (first [ pose proof ((pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia)))) as dR_1; dex1 dR_1 as regs'; dand9 dR_1 as Hms R10 R11 R12 R21 R19 R14 R15 Rothers | pose proof ((pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia)))) as dR_1; dand10 dR_1 as regs' Hms R10 R11 R12 R21 R19 R14 R15 Rothers | destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers) ]).
    exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
    cbn [pf_mem].
    split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
    repeat (split; [reflexivity|]). exact Rothers.
  - (* [comment removed for export] *)
    rewrite Nat2Z.inj_succ in Hn, Hcs |- *. rewrite Nat2Z.inj_succ in Hcs |- *.
    assert (Hks : (0 <= Z.of_nat k * s)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    (first [ pose proof ((pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia)))) as dR_2; dex1 dR_2 as regs1; dand9 dR_2 as Hms1 R10 R11 R12 R21 R19 R14 R15 Rothers | pose proof ((pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia)))) as dR_2; dand10 dR_2 as regs1 Hms1 R10 R11 R12 R21 R19 R14 R15 Rothers | destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs1 & Hms1 & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers) ]).
    destruct (Z.ltb_spec (i + 1) n); [|lia].
    (first [ pose proof ((IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
                 (i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
                 ltac:(rewrite Nat2Z.inj_succ; lia))) as dR_3; dex1 dR_3 as regs2; dand9 dR_3 as Hms2 S10 S11 S12 S21 S19 S14 S15 Sothers | pose proof ((IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
                 (i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
                 ltac:(rewrite Nat2Z.inj_succ; lia))) as dR_3; dand10 dR_3 as regs2 Hms2 S10 S11 S12 S21 S19 S14 S15 Sothers | destruct (IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
                 (i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
                 ltac:(rewrite Nat2Z.inj_succ; lia))
      as (regs2 & Hms2 & S10 & S11 & S12 & S21 & S19 & S14 & S15 & Sothers) ]).
    { intros j Hj. eapply store_ok_mono; [apply wbytes_grows | apply Hok; lia]. }
    exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    rewrite S10, S11, S12, S21, S19, S14, S15.
    split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; f_equal; lia|]. split; [reflexivity|].
    intros r A B C D. rewrite (Sothers r A B C D). apply Rothers; assumption.
Qed.


(* [comment removed for export] *)
Lemma pf_wbytes_inside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma pf_wbytes_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma pf_mem_frame : forall k mem e c s i (a : word),
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (bv_unsigned a < e - 4 * (i + Z.of_nat k) \/ e - 4 * i <= bv_unsigned a)%Z ->
  pf_mem mem e c s i k a = mem a.
Proof.
  induction k as [|k IH]; intros mem e c s i a Hi Hk He Ha; [reflexivity|].
  cbn [pf_mem]. rewrite IH by lia.
  apply pf_wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; cbn [Z.of_nat]; lia.
Qed.

Lemma word_to_le_bytes4_Z : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof. intros v. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. apply Z_to_le_bytes_wrap. cbn; lia. Qed.

(* [comment removed for export] *)
Lemma pf_mem_cell : forall k mem e c s i j t,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  pf_mem mem e c s i k (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t))
  = Some (nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0)).
Proof.
  induction k as [|k IH]; intros mem e c s i j t Hi Hk He Hj Ht; [lia|].
  rewrite Nat2Z.inj_succ in *.
  cbn [pf_mem].
  destruct (Z.eq_dec j (Z.of_nat k)) as [->|Hne].
  - (* [comment removed for export] *)
    rewrite pf_mem_frame; [| lia | lia | lia | rewrite u64_of_Z by lia; lia].
    rewrite pf_wbytes_inside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
    rewrite word_to_le_bytes4_Z. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
  - replace (e - 4 * (i + Z.succ (Z.of_nat k)) + 4 * j + Z.of_nat t)%Z
      with (e - 4 * ((i + 1) + Z.of_nat k) + 4 * j + Z.of_nat t)%Z by lia.
    rewrite (IH _ e (c + s)%Z s (i + 1)%Z j t) by lia.
    f_equal. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="HF7 HF6 HF5 HF4 HF3 HF2 HF1 HF0 Hp"] Theorem popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hwr.
  destruct (Z.to_nat (n - i)) as [|k] eqn:Hk; [lia|].
  assert (Hkz : (Z.of_nat (S k) = n - i)%Z) by lia.
  (first [ pose proof ((pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))) as dR_4; dex1 dR_4 as regs'; dand9 dR_4 as Hms R10 R11 R12 R21 R19 R14 R15 Ro | pose proof ((pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))) as dR_4; dand10 dR_4 as regs' Hms R10 R11 R12 R21 R19 R14 R15 Ro | destruct (pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))
    as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro) ]).
  { intros j Hj. replace (e - 4 * (j + 1))%Z with (e - 4 * n + 4 * (n - j - 1))%Z by lia. apply Hwr; lia. }
  exists regs'. rewrite R10, R11, R12, R21, R19, R14, R15, Hkz.
  replace (Z.of_nat k) with (n - i - 1)%Z by lia.
  repeat (split; [first [exact Hms | reflexivity]|]). exact Ro.
Qed.


(* [comment removed for export] *)

Lemma pf_mem_wbytes : forall k mem e c s i,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  pf_mem mem e c s i k = wbytes mem (Z_to_bv 64 (e - 4 * (i + Z.of_nat k))) (pf_bytes c s k).
Proof.
  intros k mem e c s i Hi Hk He. apply functional_extensionality. intros a.
  pose proof (u64_range a) as Ra. pose proof (pf_bytes_length c s k) as L.
  destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * (i + Z.of_nat k))) as [Hlt|Hge];
    [|destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * i)) as [Hlt2|Hge2]].
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
  - set (base := (e - 4 * (i + Z.of_nat k))%Z) in *.
    set (j := ((bv_unsigned a - base) / 4)%Z). set (t := Z.to_nat ((bv_unsigned a - base) mod 4)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hj : (0 <= j < Z.of_nat k)%Z) by (subst j base; lia).
    assert (Ht : (t < 4)%nat) by (subst t; lia).
    assert (Ha : a = Z_to_bv 64 (base + 4 * j + Z.of_nat t)).
    { apply bv_eq. rewrite u64_of_Z by (subst j t base; lia). subst j t base. lia. }
    rewrite Ha. subst base. rewrite (pf_mem_cell k mem e c s i j t Hi Hk He Hj Ht).
    rewrite pf_wbytes_inside; rewrite ?L, ?u64_of_Z by lia; [|lia|lia].
    replace (Z.to_nat (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t - (e - 4 * (i + Z.of_nat k)))) with (Z.to_nat (4 * j) + t)%nat by lia.
    symmetry. f_equal. apply pf_bytes_nth; assumption.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
Qed.

#[using="HF7 HF6 HF5 HF4 HF3 HF2 HF1 HF0 Hp"] Theorem popfree_spec_of_code : popfree_spec segs p.
Proof.
  intros regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok.
  (first [ pose proof ((popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs)) as dR_5; dex1 dR_5 as regs'; dand9 dR_5 as Hms R10 R11 R12 R21 R19 R14 R15 Ro | pose proof ((popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs)) as dR_5; dand10 dR_5 as regs' Hms R10 R11 R12 R21 R19 R14 R15 Ro | destruct (popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro) ]).
  { intros d m Hd Hdm. eapply (store_ok_sub segs mem _ _ (Z.to_nat (4 * (n - i))) m); [| exact Hok | |]; rewrite !u64_of_Z by lia; lia. }
  exists regs'. rewrite (pf_mem_wbytes (Z.to_nat (n - i)) mem e c s i) in Hms by lia.
  replace (i + Z.of_nat (Z.to_nat (n - i)))%Z with n in Hms by lia.
  split; [exact Hms|]. split; [exact R10|]. split; [exact R12|]. split; [exact R14|]. split; [exact R15|]. exact Ro.
Qed.

End PopFreeLoop.
End Asanvp3.

Module Asan59m.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanz3l AsanPlan Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asanvp3.   (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

Section Specs.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Definition fill_spec (entry cmax : Z) : Prop :=
  forall mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
    0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    bv_unsigned c < cmax ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = s.

(* [comment removed for export] *)
Definition copy_spec (entry : Z) : Prop :=
  forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn SEGS mem0 src (length bs) = Some bs ->
    store_ok SEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
Definition miz_spec (entry : Z) : Prop :=
  forall mem (beg sp : word) (N : Z) (regs : bvmap 5 word) (ret : word),
    0 <= N <= 2 ^ 40 -> bv_unsigned beg + N + 8 <= 2 ^ 64 -> 16 <= bv_unsigned sp ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
    (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg) ->
    (forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
       rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 1.

(* [comment removed for export] *)
Definition SEALED_BYTES : list byte :=
  [Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]
  ++ repeat (Z_to_bv 8 0) 4087.

(* [comment removed for export] *)
Definition istrncpy_spec (entry src : Z) : Prop :=
  forall mem0 (dst : word) (regs : bvmap 5 word) (ret : word),
    (forall i, src <= i < src + 9 -> mem0 (Z_to_bv 64 i) = None) ->
    store_ok SEGS mem0 dst 4095%nat = true ->
    bv_unsigned dst + 4095 < 2 ^ 64 ->
    (bv_unsigned dst + 4095 <= src \/ src + 9 <= bv_unsigned dst) ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = Z_to_bv 64 src -> getr regs 12%bv = Z_to_bv 64 4095 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => AP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - (first [ pose proof ((In_nth caller_saved (ridx r) 0%nat Hin)) as dR_1; dex1 dR_1 as j; destruct dR_1 as [Hj Hnth] | pose proof ((In_nth caller_saved (ridx r) 0%nat Hin)) as dR_1; dand3 dR_1 as j Hj Hnth | destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth) ]).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_same : forall bs m (a : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, (j < length bs)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  wbytes m a bs = m.
Proof.
  intros bs m a Hnw Hall. apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { apply wbytes_out; [exact Hnw | lia]. }
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
  2: { apply wbytes_out; [exact Hnw | lia]. }
  set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
  assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  { subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined : forall bs m (a : word) j,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_all : forall segs m n (a : word) b,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (bv_unsigned a + i)) = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat].
  pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_nth : forall segs m n (a : word) bs j,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs m a n = Some bs -> (j < n)%nat ->
  rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
  - cbn [nth]. destruct n as [|n'']; [lia|].
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
    apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
  rdn segs m a n = Some (map f (seq 0 n)).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs,
  (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
  length bs = n -> (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KnowTests.
Variable segs : list Segment.

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable] in H.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. (first [ dand4 Hfl' as F1 F2 F3 F4 | destruct Hfl' as (F1 & F2 & F3 & F4) ]).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
  { intros A B. split; [|lia].
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
    pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
  - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
    apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
    apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
    destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
    unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable_x allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. (first [ dand4 Hfl' as F1 F2 F3 F4 | destruct Hfl' as (F1 & F2 & F3 & F4) ]).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kzero_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kzero_x allkn k b off n = true ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. (first [ dand4 Hfl' as F1 F2 F3 F4 | destruct Hfl' as (F1 & F2 & F3 & F4) ]).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. (first [ dand3 HKK as H0 Hhi Hnone | destruct HKK as (H0 & Hhi & Hnone) ]).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 (estart E (SA b off))) w = Some bs /\ length bs = w
             /\ word_to_le_bytes w (edenot E v) = bs.

Lemma lookup_piece : forall E M k b off w v hs,
  know_ok segs E M k -> (1 <= w <= 8)%nat ->
  know_lookup segs k b off w false [] [] = LHit v [] hs ->
  flat E (SA b off) (Z.of_nat w) ->
  piece_ok E M b off w v.
Proof.
  intros E M k b off w v hs HK Hw HL Hfl.
  pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. (first [ pose proof ((X ltac:(constructor) Hfl)) as dR_6; dex1 dR_6 as bs; dand3 dR_6 as Hrd Hlen Hv | pose proof ((X ltac:(constructor) Hfl)) as dR_6; dand4 dR_6 as bs Hrd Hlen Hv | destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv) ]).
  exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
  unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

Lemma kread8e_piece : forall E M k b off v,
  know_ok segs E M k -> kread8e segs k b off = Some v -> flat E (SA b off) 8 ->
  piece_ok E M b off 8 v.
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

Lemma kreadZ1_byte : forall E M k b off z,
  know_ok segs E M k -> kreadZ segs k b off 1 = Some z -> flat E (SA b off) 1 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) 1 = Some [Z_to_bv 8 z] /\ 0 <= z < 256.
Proof.
  intros E M k b off z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. (first [ pose proof ((X ltac:(constructor) Hfl)) as dR_7; dex1 dR_7 as bs; dand3 dR_7 as Hrd Hlen Hv | pose proof ((X ltac:(constructor) Hfl)) as dR_7; dand4 dR_7 as bs Hrd Hlen Hv | destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv) ]).
  destruct bs as [|b0 [|]]; try discriminate.
  cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
  pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
  split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma kread_bytes_sound : forall E M k len b off zs,
  know_ok segs E M k -> kread_bytes segs len k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat len <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) len = Some (map (fun z => Z_to_bv 8 z) zs)
  /\ length zs = len /\ Forall (fun z => 0 <= z < 256) zs.
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
  - cbn [kread_bytes] in H.
    destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
    destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
    (first [ pose proof ((IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia))) as dR_8; dand3 dR_8 as Hrd2 Hlen Hall | destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall) ]).
    split; [| split; [cbn; lia | constructor; assumption]].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
    apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma zbytes_of_small : forall zs, Forall (fun z => 0 <= z < 256) zs ->
  zbytes_le_to_Z zs = bytes_le_to_Z (map (fun z => Z_to_bv 8 z) zs).
Proof.
  intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
  induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_facts_sound : forall E M k sb db fuel sk dk n kc,
  know_ok segs E M k ->
  copy_facts segs fuel k sb sk db dk n = Some kc -> 0 <= n -> (Z.to_nat n <= fuel)%nat ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + n <= 2 ^ 64 ->
  0 <= estart E (SA db dk) -> estart E (SA db dk) + n <= 2 ^ 64 ->
  exists bs, length bs = Z.to_nat n
    /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
    /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc.
Proof.
  intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
  - cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
    exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
  - cbn [copy_facts] in H.
    (* [comment removed for export] *)
    assert (STEP : forall (w : nat) v kr,
      (1 <= w <= 8)%nat -> Z.of_nat w <= n ->
      piece_ok E M sb sk w v ->
      copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
      kc = KWord (SA db dk) w v :: kr ->
      exists bs, length bs = Z.to_nat n
        /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
        /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
    { (intros w v kr Hw Hwn; (first [ intro dR_43; dex1 dR_43 as bsP; dand3 dR_43 as HrdP HlenP HvP | intro dR_43; dand4 dR_43 as bsP HrdP HlenP HvP | intros (bsP & HrdP & HlenP & HvP) ]); intros Hr ->).
      assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      (first [ pose proof ((IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))) as dR_9; dex1 dR_9 as bsR; dand3 dR_9 as HlenR HrdR HKR | pose proof ((IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))) as dR_9; dand4 dR_9 as bsR HlenR HrdR HKR | destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
        as (bsR & HlenR & HrdR & HKR) ]).
      exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
      - replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
        apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
        rewrite ES in HrdR.
        replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
      - intros M' HM'. constructor.
        + cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
          rewrite adenot_SA, HvP.
          pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
          rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
        + apply HKR. rewrite ED.
          pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
          replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
          replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
          rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
    + apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
      destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
        [|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
      assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
      destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
      * injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
      * destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
        apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
        (first [ pose proof ((kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia))) as dR_10; dand3 dR_10 as Hrd Hlen Hsmall | destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall) ]).
        exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
        cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
        replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
        apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
    + clear H8. destruct (Z.leb 1 n) eqn:H1.
      * apply Z.leb_le in H1.
        destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
        destruct scs; [|discriminate].
        destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
        injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
      * injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
        exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis NX0_ok : APS.nx0_ok nx0.
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A argH) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).

(* [comment removed for export] *)
#[local] Ltac aps_fill :=
  first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
        | exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT].

Lemma w_reg_sound : forall E cs R FULL model n,
  CSOK E cs R FULL model -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_reg_lit_sound : forall E cs R FULL model n z,
  CSOK E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ 0 <= z < two64.
Proof. intros. eapply reg_lit_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. eapply split_lit_denot; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_know_ok_havoc : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc k b o n).
Proof. intros. eapply know_ok_havoc; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_flat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> flat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof. intros. eapply flat_x_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [Hv Hb] Hle. split; [|exact Hb]. intros n Hn. apply Hv. lia. Qed.

Lemma w_cs_ok_agree : forall E E' cs R FULL model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> CSOK E cs R FULL model -> CSOK E' cs R FULL model.
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_hid_agree : forall b E E' cs model,
  env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  HID E' cs model = HID E cs model.
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
  CSOK E cs R FULL model -> same_but_materialized model model' -> MInv (allowA A E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (MR E cs model FULL') (s_know ss') ->
  (forall a, HID E cs model a = true -> FULL' a = FULL a) ->
  CSOK E (with_ss cs ss') R' FULL' model'.
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_lazy_cover_cs : forall E cs R FULL model,
  CSOK E cs R FULL model -> lazy_cover (HID E cs model) (m_vm_lazy model) (allowA A E cs).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
  AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.

(* [comment removed for export] *)

Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma wview_rd1 : forall M (a : word) b,
  wview SEGS M a = Some b ->
  (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
  intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (seg_writable seg) eqn:Hw; [|discriminate].
  rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.

Lemma store_ok_rdn : forall n M (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  exists bs, rdn SEGS M a n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros M a Hnw Hst.
  - exists []. split; reflexivity.
  - cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
    cbn [rdn]. rewrite (wview_rd1 M a b Hv).
    destruct n as [|n'].
    + exists [b]. split; reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      (first [ pose proof ((IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst)) as dR_11; dex1 dR_11 as bs; destruct dR_11 as [Hrd Hlen] | pose proof ((IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst)) as dR_11; dand3 dR_11 as bs Hrd Hlen | destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen) ]).
      rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma call_core : forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
  CSOK E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' MR' k' ->
  (forall R' FULL' model',
      CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' ret FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
  (first [ pose proof ((w_fresh_ok_parts cs Hfresh)) as dR_12; dand7 dR_12 as Fsr Fkn Fmaps Fallow Fbrk Ffd Fle | destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle) ]).
  set (H := HID E cs model).
  unfold cfg_of.
  apply (srz_msteps_restricted_T SEGS H
           (w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
           (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
           (w_lazy_cover_cs E cs R FULL model HC)
           (w_A_wf_allowA E cs)
           (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC)).
  - rewrite restrict_mkst. exact Hms.
  - intros model' Hinv' Hsame Hclean.
    set (FULL' := munrestrict H FULL MR').
    change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
      with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
    apply (Hk regs' FULL' model').
    + pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
      * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
      * exact HR'.
      * reflexivity.
      * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
        fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
        exact HK'.
      * intros a Ha. rewrite HH in Ha.
        unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
    + apply (same_but_materialized_frame _ _ Hsame).
Qed.

Lemma sr_vars_lt_fresh : forall rs sr nx b,
  AP.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> AP.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
  induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
  apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma call_node_sound : forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  (first [ pose proof ((w_fresh_ok_parts cs Hfresh)) as dR_13; dand7 dR_13 as Fsr Fkn Fmaps Fallow Fbrk Ffd Fle | destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle) ]).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
  ext_list (ext_call E nx R') (nx + NCS) vals.

Lemma ext_call2_agree : forall E nx R' vals, env_agree nx E (ext_call2 E nx R' vals).
Proof.
  intros E nx R' vals. unfold ext_call2.
  destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
  split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.

Lemma ext_call2_agree16 : forall E nx R' vals, env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals).
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.

Lemma ext_call2_at : forall E nx R' vals i, (i < length vals)%nat ->
  ev (ext_call2 E nx R' vals) (nx + NCS + i) = nth i vals (Z_to_bv 64 0).
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.

Lemma call_node_sound2 : forall cs cs' E R FULL model T (ret : Z) rv k' extra vals regs' MR',
  CSOK E cs R FULL model ->
  after_call2 nx0 cs ret rv k' extra = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
  unfold after_call2 in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  (first [ pose proof ((w_fresh_ok_parts cs Hfresh)) as dR_14; dand7 dR_14 as Fsr Fkn Fmaps Fallow Fbrk Ffd Fle | destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle) ]).
  set (E' := ext_call2 E (nxt cs) regs' vals).
  pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
  set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
  assert (Hsf : AP.sr_vars_lt (nxt cs + NCS) sr1 = true).
  { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
    unfold caller_saved, NCS. cbn [length]. lia. }
  assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
  { eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
    - destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
    - subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
      destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK').
  intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
  split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ret_lit_sound : forall E cs R FULL model r,
  CSOK E cs R FULL model -> ret_lit cs = Some r ->
  getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64.
Proof.
  intros E cs R FULL model r HC H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (w_reg_sound E cs R FULL model 1 HC ltac:(lia)) as R1.
  rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.


Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> AP.expr_vars_lt m e = true -> AP.expr_vars_lt m b = true.
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

(* [comment removed for export] *)
Lemma k0_sound : forall E M k db dk ne dst k0,
  know_ok SEGS E M k ->
  (if off_image_x A k db dk ne then Some k
   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
  know_ok SEGS E M k0.
Proof.
  intros E M k db dk ne dst k0 HK H.
  destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
  destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
  apply kimg_cut_sound. exact HK.
Qed.

(* [comment removed for export] *)
Lemma wbytes_fill_at : forall M (s : word) b n i,
  bv_unsigned s + n <= 2 ^ 64 -> 0 <= i < n ->
  wbytes M s (repeat b (Z.to_nat n)) (Z_to_bv 64 (bv_unsigned s + i)) = Some b.
Proof.
  intros M s b n i Hnw Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof.
  intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
Lemma summary_fill_sound : forall entry cmax,
  fill_spec SEGS entry cmax ->
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => summary_fill A nx0 cs entry cmax).
Proof.
  intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_fill_eq in Hn. (* [comment removed for export] *) unfold summary_fill_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
  destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  (* [comment removed for export] *)
  (first [ pose proof ((ret_lit_sound E cs R FULL model ret HC Hret)) as dR_15; dand3 dR_15 as R1 Hrok Hretr | destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr) ]).
  destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k',
     store_ok SEGS M s (Z.to_nat n) = true ->
     know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros k' Hst HK' Hac.
    (first [ pose proof ((SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))) as dR_16; dex1 dR_16 as regs'; dand3 dR_16 as Hms Hkept Ha0 | pose proof ((SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))) as dR_16; dand4 dR_16 as regs' Hms Hkept Ha0 | destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
      as (regs' & Hms & Hkept & Ha0) ]).
    rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
  assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
  { apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
    (first [ pose proof ((kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr)) as dR_17; dand3 dR_17 as Wst Wlo Whi | destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi) ]).
    (first [ pose proof ((kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz)) as dR_18; dand3 dR_18 as Zb _ _ | destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _) ]).
    rewrite Hse, Hlen in *.
    apply (FIN (kn cs)); [apply Wst; lia | | exact Hn].
    destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
    rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
  clear Hzb.
  (* [comment removed for export] *)
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
  destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
  (first [ pose proof ((kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr)) as dR_19; dand3 dR_19 as Wst Wlo Whi | destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi) ]).
  rewrite Hse, Hlen in *.
  eapply FIN; [apply Wst; lia | | exact Hn].
  set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
  assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
  { eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    subst M'. apply wbytes_out; rewrite repeat_length; lia. }
  destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
  assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
  assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
  { intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
  constructor; [|exact HK1].
  destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
  - apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
  - split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma store_ok_sub : forall M (a : word) n (b : word) m,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  bv_unsigned a <= bv_unsigned b -> bv_unsigned b + Z.of_nat m <= bv_unsigned a + Z.of_nat n ->
  store_ok SEGS M b m = true.
Proof.
  intros M a n b m Hnw Hst Hlo Hhi. apply store_ok_of_all; [lia|].
  intros x Hx. eapply (store_ok_all SEGS M n a Hnw Hst). lia.
Qed.

Lemma summary_miz_sound :
  miz_spec SEGS (x_memiszero A) ->
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => summary_miz A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_miz_eq in Hn. (* [comment removed for export] *) unfold summary_miz_ref in Hn.
  destruct (Z.eqb (pc cs) (x_memiszero A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eaddz (reg cs 2) (-16))) as [qb qk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hwr]. apply andb_prop in Hcond as [Hcond Hsphi'].
  apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hb8].
  apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.leb_le in Hb8. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'.
  unfold two64 in Hb8, Hsphi'.
  (* [comment removed for export] *)
  (first [ pose proof ((ret_lit_sound E cs R FULL model ret HC Hret)) as dR_20; dand3 dR_20 as R1 Hrok Hretr | destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr) ]).
  pose proof (w_reg_sound E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (beg := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *.
  set (nw := edenot E (reg cs 11)) in *. set (N := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold N in Hnr. pose proof (u64_range beg) as Hbr. pose proof (u64_range spw) as Hsr.
  assert (HnwN : Z_to_bv 64 N = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HlenN : elenZ E (reg cs 11) = N) by reflexivity.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
  (first [ pose proof ((kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia))) as dR_21; dand3 dR_21 as Qst Qlo Qhi | destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi) ]).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = bv_unsigned spw - 16).
  { apply (f_equal bv_unsigned) in Hq. rewrite !u_lit64 in Hq. unfold two64 in Hq.
    change (estart E (SA qb qk)) with Q in Hq.
    rewrite (Z.mod_small Q) in Hq by lia.
    rewrite <- Hq.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (Hstk : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 8)) 8 = true).
  { apply (store_ok_sub M (Z_to_bv 64 Q) 16); rewrite ?u64_lit by lia; try lia. exact Qst. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold beg in Hbeg.
  (first [ pose proof ((kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz)) as dR_22; dand3 dR_22 as Zb Blo Bhi | destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz) as (Zb & Blo & Bhi) ]).
  rewrite HlenN in Zb, Bhi.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) qb qk (ELit 16) bb bk (reg cs 11) HKN Hap) as Hapart.
  rewrite HlenN in Hapart. change (estart E (SA qb qk)) with Q in Hapart.
  replace (elenZ E (ELit 16)) with 16 in Hapart by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  set (B := estart E (SA bb bk)) in *.
  assert (HuB : bv_unsigned beg = B \/ (B = 2 ^ 64 /\ bv_unsigned beg = 0)).
  { destruct (Z.eq_dec B (2 ^ 64)) as [HB|HB].
    - right. split; [exact HB|]. rewrite Hbeg. change (bv_unsigned (edenot E bb) + bk) with B. rewrite HB. reflexivity.
    - left. rewrite Hbeg. apply u64_lit. lia. }
  assert (Hdisj : bv_unsigned beg + N <= bv_unsigned spw - 8 \/ bv_unsigned spw <= bv_unsigned beg) by lia.
  assert (Hz : forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
                 rdn SEGS M a 1 = Some [Z_to_bv 8 0]).
  { intros a Ha. apply rdn1_overlay.
    destruct HuB as [HuB|[HB Hu0]]; [|lia].
    replace a with (Z_to_bv 64 (B + (bv_unsigned a - B))) by (rewrite <- (Z_to_bv_bv_unsigned 64 a) at 2; f_equal; lia).
    apply Zb. lia. }
  (first [ pose proof ((SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
               ltac:(rewrite HnwN; exact R11))) as dR_23; dex1 dR_23 as regs'; dand3 dR_23 as Hms Hkept Ha0 | pose proof ((SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
               ltac:(rewrite HnwN; exact R11))) as dR_23; dand4 dR_23 as regs' Hms Hkept Ha0 | destruct (SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
               ltac:(rewrite HnwN; exact R11)) as (regs' & Hms & Hkept & Ha0) ]).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (ELit 1)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 16)) with 16 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

Lemma summary_copy_sound : forall entry,
  copy_spec SEGS entry ->
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => summary_copy SEGS A nx0 cs entry).
Proof.
  intros entry SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_copy_eq in Hn. (* [comment removed for export] *) unfold summary_copy_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  (* [comment removed for export] *)
  (first [ pose proof ((ret_lit_sound E cs R FULL model ret HC Hret)) as dR_24; dand3 dR_24 as R1 Hrok Hretr | destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr) ]).
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (w_split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
  assert (Hlen : elenZ E ne = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k' bs,
     length bs = Z.to_nat n ->
     rdn SEGS M sr (length bs) = Some bs ->
     store_ok SEGS M s (length bs) = true ->
     (bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
     know_ok SEGS E (wbytes M s bs) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
    (first [ pose proof ((SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12))) as dR_25; dex1 dR_25 as regs'; dand3 dR_25 as Hms Hkept Ha0 | pose proof ((SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12))) as dR_25; dand4 dR_25 as regs' Hms Hkept Ha0 | destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0) ]).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
  apply andb_prop in Hwa as [Hwr Hap].
  (first [ pose proof ((kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr)) as dR_26; dand3 dR_26 as Wst Wlo Whi | destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi) ]).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  rewrite Hse in Wst.
  (* [comment removed for export] *)
  assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
            know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
  { intros bs Hlbs Hpos.
    assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
    eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
    apply wbytes_out; rewrite Hlbs; lia. }
  (* [comment removed for export] *)
  assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
  { intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
  (* [comment removed for export] *)
  assert (VARS : fresh_ok nx0 cs = true ->
            AP.kn_vars_lt (nxt cs) (kn cs) = true /\ AP.expr_vars_lt (nxt cs) db = true /\ AP.expr_vars_lt (nxt cs) ne = true
            /\ AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
  { intros Hfresh. (first [ pose proof ((w_fresh_ok_parts cs Hfresh)) as dR_27; dand3 dR_27 as Fsr Fkn _ | destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _) ]).
    split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
    eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
    forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
    after_call2 nx0 cs ret (Some (reg cs 10))
      (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
       ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
      = Some cs' ->
    srealizes SEGS (cfg R (pc cs) FULL model) T).
  { intros Hswr Hsfl W u HW Hu Hac.
    (first [ pose proof ((kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr)) as dR_28; dand3 dR_28 as SWst Slo Shi | destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi) ]).
    (first [ pose proof ((w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl)) as dR_29; dand3 dR_29 as _ _ Spos | destruct (w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos) ]).
    rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
    change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
    destruct (HusD Spos Slo Shi) as [Hus Husr].
    (first [ pose proof ((store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia)))) as dR_30; dex1 dR_30 as bs; destruct dR_30 as [Hrd Hlbs] | pose proof ((store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia)))) as dR_30; dand3 dR_30 as bs Hrd Hlbs | destruct (store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs) ]).
    assert (Hfresh : fresh_ok nx0 cs = true).
    { unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
    (first [ pose proof ((VARS Hfresh)) as dR_31; dand4 dR_31 as Fkn Fdb Fne Fsr | destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr) ]).
    (first [ pose proof ((SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12))) as dR_32; dex1 dR_32 as regs'; dand3 dR_32 as Hms Hkept Ha0 | pose proof ((SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12))) as dR_32; dand4 dR_32 as regs' Hms Hkept Ha0 | destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0) ]).
    set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
    eapply (call_node_sound2 cs cs' E R FULL model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - set (E2 := ext_call2 E (nxt cs) regs' vals).
      pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
      assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
      assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
      assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
      assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
      pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
      apply Forall_app. split.
      + (* [comment removed for export] *)
        apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
        assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
        { unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
        cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
        rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
        subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
        assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
        rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
        pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
        pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
        replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
        rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
      + apply Forall_app. split.
        { (* [comment removed for export] *)
          unfold kblob_prefix.
          destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
          apply find_some in HF as [HinK HKt].
          destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
          apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
          apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
          pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
          assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          rewrite En0 in HKB. (first [ dand3 HKB as Bflat Blen Bbytes | destruct HKB as (Bflat & Blen & Bbytes) ]).
          change (estart E (SA sb sk)) with S in Bflat, Bbytes.
          destruct Hag2 as [Hag2a Heb2].
          assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
            [| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
          cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
          refine (conj _ (conj Blen _)).
          - unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
            change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
          - intros i Hi. rewrite <- Hus.
            replace i with (Z.of_nat (Z.to_nat i)) by lia.
            rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
            f_equal.
            pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
            rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
            cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
          }
      (* [comment removed for export] *)
        assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
        pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
        assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
        { eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
          intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
        destruct u; [|exact HAV2].
        constructor; [|exact HAV2].
        (* [comment removed for export] *)
        apply know_ok_unk_intro_pt.
        * unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
        * intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
          replace i with (Z.of_nat (Z.to_nat i)) by lia.
          apply wbytes_defined; rewrite Hlbs; lia.
    - exact Hk. }
  (* [comment removed for export] *)
  assert (HSRC :
    (if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
     then after_call2 nx0 cs ret (Some (reg cs 10))
            (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
                 (seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
             ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
            (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
     else None) = Some cs' ->
    srealizes SEGS (cfg R (pc cs) FULL model) T).
  { destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
    apply andb_prop in Hsw as [Hswr Hsfl].
    assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
    destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
    - apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
      apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
      apply (GEN Hswr Hsfl); [|exact Hu].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - apply (GEN Hswr Hsfl); [lia | exact Hu]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
  { apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
    (first [ pose proof ((kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz)) as dR_34; dand3 dR_34 as Zb Slo Shi | destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi) ]).
    rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
    destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
    apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
      [apply repeat_length | | | lia | | exact Hn].
    - rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
    - rewrite repeat_length. apply Wst. lia.
    - constructor; [| apply HAVOC; [apply repeat_length | lia]].
      cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
      intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
  clear Hzs.
  (* [comment removed for export] *)
  destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
  apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
  destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
  assert (Hnn : n = nhi).
  { cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
  (first [ pose proof ((w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl)) as dR_35; dand3 dR_35 as Slo Shi Spos | destruct (w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos) ]).
  change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
  destruct (HusD Spos Slo Shi) as [Hus Husr].
  (first [ pose proof ((copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))) as dR_36; dex1 dR_36 as bs; dand3 dR_36 as Hlbs Hrd HKC | pose proof ((copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))) as dR_36; dand4 dR_36 as bs Hlbs Hrd HKC | destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
    as (bs & Hlbs & Hrd & HKC) ]).
  change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
  rewrite <- Hnn in Hlbs, Hrd, HKC.
  apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
  - rewrite Hlbs, <- Hsre. exact Hrd.
  - rewrite Hlbs. apply Wst. lia.
  - apply Forall_app. split.
    + apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
    + apply HAVOC; [exact Hlbs | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma img_cov_sound : forall E M k a b,
  know_ok SEGS E M k -> img_cov k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
  destruct K as [| | |lo hi| | | | | |]; try discriminate.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. (first [ dand3 HK1 as _ _ HK1 | destruct HK1 as (_ & _ & HK1) ]).
  apply HK1. lia.
Qed.

Lemma SEALED_BYTES_length : length SEALED_BYTES = 4095%nat.
Proof. reflexivity. Qed.

Lemma SEALED_W_bytes : word_to_le_bytes 8 (Z_to_bv 64 SEALED_W) = firstn 8 SEALED_BYTES.
Proof.
  replace SEALED_W with (bytes_le_to_Z (firstn 8 SEALED_BYTES)) by (vm_compute; reflexivity).
  apply word_to_le_bytes_of_bytes_n; reflexivity.
Qed.

Lemma SEALED_BYTES_nth_hi : forall j, (8 <= j < 4095)%nat -> nth j SEALED_BYTES (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj. unfold SEALED_BYTES. rewrite app_nth2 by (cbn; lia). cbn [length]. apply nth_repeat_lt. lia.
Qed.

Lemma summary_istrncpy_sound :
  istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) ->
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => summary_istrncpy A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_istrncpy_eq in Hn. (* [comment removed for export] *) unfold summary_istrncpy_ref in Hn.
  destruct (Z.eqb (pc cs) (x_istrncpy A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [src|] eqn:H11; [|discriminate].
  destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate].
  destruct (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool eqn:Hsn; [|discriminate]. cbn [negb] in Hn.
  apply andb_prop in Hsn as [Hsrc Hn95]. apply Z.eqb_eq in Hsrc. apply Z.eqb_eq in Hn95. subst src n.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  rename Hcond into Hb. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  match goal with Hl : Z.leb 0 (x_sealed A) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hs0 end.
  match goal with Hl : Z.ltb (x_sealed A + 9) two64 = true |- _ => apply Z.ltb_lt in Hl; unfold two64 in Hl; rename Hl into Hs9 end.
  match goal with Hl : kwritable_x _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
  match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
  match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.
  (* [comment removed for export] *)
  (first [ pose proof ((ret_lit_sound E cs R FULL model ret HC Hret)) as dR_38; dand3 dR_38 as R1 Hrok Hretr | destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr) ]).
  destruct (w_reg_lit_sound E cs R FULL model 11 _ HC ltac:(lia) H11) as [R11 _].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *.
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  pose proof (k0_sound E M (kn cs) db dk (ELit 4095) (reg cs 10) k0 HKN
                ltac:(destruct (off_image_x A (kn cs) db dk (ELit 4095)); [exact Hk0 | destruct (reg cs 10); try discriminate; exact Hk0])) as HK0.
  (first [ pose proof ((kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr)) as dR_39; dand3 dR_39 as Wst Wlo Whi | destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi) ]).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9) HKN Hap) as Hapart.
  rewrite !elenZ_lit in * by lia.
  unfold estart in Hapart at 2 3; cbn [a_base a_off edenot] in Hapart. rewrite u_lit0 in Hapart.
  set (D := estart E (SA db dk)) in *.
  assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
  pose proof (img_cov_sound E M k0 _ _ HK0 Hcov) as Hnone.
  (first [ pose proof ((SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
               Hrok R1 R10 R11 R12)) as dR_40; dex1 dR_40 as regs'; dand3 dR_40 as Hms Hkept Ha0 | pose proof ((SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
               Hrok R1 R10 R11 R12)) as dR_40; dand4 dR_40 as regs' Hms Hkept Ha0 | destruct (SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
               Hrok R1 R10 R11 R12) as (regs' & Hms & Hkept & Ha0) ]).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - set (M' := wbytes M s SEALED_BYTES).
    assert (Hlen : bv_unsigned s + Z.of_nat (length SEALED_BYTES) <= 2 ^ 64) by (rewrite SEALED_BYTES_length; lia).
    assert (BY : forall j, (j < 4095)%nat -> M' (Z_to_bv 64 (D + Z.of_nat j)) = Some (nth j SEALED_BYTES (Z_to_bv 8 0))).
    { intros j Hj. subst M'. rewrite <- Hus. apply wbytes_nth; [exact Hlen | rewrite SEALED_BYTES_length; exact Hj]. }
    constructor; [|constructor].
    + (* [comment removed for export] *)
      cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
      rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
      cbn [edenot]. rewrite SEALED_W_bytes.
      replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
      apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
    + (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite elenZ_lit by lia.
      assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
      rewrite HD8. split; [unfold flat; lia|].
      intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
      rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
    + (* [comment removed for export] *)
      eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

Lemma firstn_skipn_map_nth : forall {T} (d : T) k (l : list T) m, (m + k <= length l)%nat ->
  firstn k (skipn m l) = map (fun q => nth (m + q)%nat l d) (seq 0 k).
Proof.
  intros T d k. induction k as [|k IH]; intros l m Hm; [reflexivity|].
  cbn [seq map]. rewrite <- seq_shift, map_map.
  destruct (skipn m l) as [|x rest] eqn:Hs.
  - exfalso. pose proof (f_equal (@length _) Hs) as HL. rewrite length_skipn in HL. cbn in HL. lia.
  - cbn [firstn]. f_equal.
    + rewrite <- nth_skipn, Hs. reflexivity.
    + replace rest with (skipn (S m) l).
      2: { replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
      rewrite (IH l (S m)) by lia. apply map_ext. intros q. f_equal. lia.
Qed.

Lemma popfree_facts_sound : forall E M lb lk cnt c s K (base : word),
  bv_unsigned base = estart E (SA lb lk) ->
  (K <= Z.to_nat cnt)%nat -> 0 < cnt -> estart E (SA lb lk) + 4 * cnt <= 2 ^ 64 -> 0 <= estart E (SA lb lk) ->
  know_ok SEGS E (wbytes M base (pf_bytes c s (Z.to_nat cnt))) (popfree_facts lb lk cnt c s K).
Proof.
  intros E M lb lk cnt c s K base Hbase HK Hcnt Hhi Hlo. unfold popfree_facts. apply Forall_forall. intros Kx Hin.
  apply in_map_iff in Hin as [t [<- Hint]]. apply in_seq in Hint.
  set (D := estart E (SA lb lk)) in *. set (j := cnt - 1 - Z.of_nat t).
  assert (Hj : 0 <= j < cnt) by lia.
  cbn [kentry_ok]. split; [lia|].
  assert (HDj : estart E (SA lb (lk + 4 * j)) = D + 4 * j) by (unfold D, estart; cbn [a_base a_off]; lia).
  split; [unfold flat; rewrite HDj; cbn [Z.of_nat]; lia|].
  rewrite adenot_SA, HDj. cbn [edenot].
  rewrite word_to_le_bytes4_Z.
  replace ((c + Z.of_nat t * s) / 16) with ((c + (Z.of_nat (Z.to_nat cnt) - 1 - j) * s) / 16) by (f_equal; f_equal; lia).
  rewrite <- (pf_bytes_cell c s (Z.to_nat cnt) j) by lia.
  assert (Hlen : length (pf_bytes c s (Z.to_nat cnt)) = (4 * Z.to_nat cnt)%nat) by apply pf_bytes_length.
  rewrite (firstn_skipn_map_nth (Z_to_bv 8 0) 4) by (rewrite Hlen; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (D + 4 * j)) = D + 4 * j) by (apply u64_lit; lia).
  apply rdn_of_nth; [rewrite Hu; lia|]. intros q Hq. apply rdn1_overlay. rewrite Hu.
  replace (D + 4 * j + Z.of_nat q) with (bv_unsigned base + Z.of_nat (Z.to_nat (4 * j) + q)) by lia.
  apply wbytes_nth; rewrite Hlen; lia.
Qed.

Lemma summary_popfree_sound :
  popfree_spec SEGS (x_popfree A) ->
  forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => summary_popfree A nx0 cs args).
Proof.
  intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  unfold summary_popfree in Hn.
  destruct (Z.eqb (pc cs) (x_popfree A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct args as [|[K| | | | | | |] [|]]; try discriminate.
  destruct (reg_lit cs 10) as [i|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 12) as [c|] eqn:H12; [|discriminate].
  destruct (reg_lit cs 21) as [s|] eqn:H21; [|discriminate].
  destruct (reg_lit cs 19) as [n|] eqn:H19; [|discriminate].
  destruct (split_lit (eaddz (reg cs 11) (- (4 * n)))) as [lb lk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 11)) as [el|] eqn:Hel; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [eh|] eqn:Heh; [|discriminate].
  match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  apply Z.leb_le in Hcond.
  repeat match goal with
         | Hl : Z.leb _ _ = true |- _ => apply Z.leb_le in Hl
         | Hl : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hl end.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  match goal with Hl : fresh_ok nx0 cs = true |- _ => rename Hl into Hfresh end.
  match goal with Hl : kwritable_x _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
  match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.
  (* [comment removed for export] *)
  destruct (w_reg_lit_sound E cs R FULL model 10 _ HC ltac:(lia) H10) as [R10 Hi].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 Hc].
  destruct (w_reg_lit_sound E cs R FULL model 21 _ HC ltac:(lia) H21) as [R21 Hs].
  destruct (w_reg_lit_sound E cs R FULL model 19 _ HC ltac:(lia) H19) as [R19 Hnn].
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hel) as Hel'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh'.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  set (ew := edenot E (reg cs 11)) in *. set (e := bv_unsigned ew) in *.
  pose proof (u64_range ew) as Her. fold e in Her.
  set (cnt := n - i) in *.
  (first [ pose proof ((kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr)) as dR_41; dand3 dR_41 as Wst Wlo Whi | destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi) ]).
  rewrite elenZ_lit in Wst, Whi by lia.
  set (D := estart E (SA lb lk)) in *.
  pose proof (w_split_lit_denot E _ lb lk Hspl) as Hsd.
  assert (HloD : edenot E (eaddz (reg cs 11) (- (4 * n))) = Z_to_bv 64 (e - 4 * n)).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64. fold ew. rewrite u_lit64. unfold two64.
    rewrite u64_lit by lia. fold e.
    replace (e + - (4 * n) mod 2 ^ 64) with ((e - 4 * n) + 1 * 2 ^ 64).
    2: { rewrite <- (Z.mod_add (- (4 * n)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HD : D = e - 4 * n).
  { assert (HDdef : D = bv_unsigned (edenot E lb) + lk) by reflexivity.
    rewrite HloD, <- HDdef in Hsd. apply (f_equal bv_unsigned) in Hsd. rewrite !u64_lit in Hsd by lia. lia. }
  (first [ pose proof ((SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite <- HD; apply Wst; lia))) as dR_42; dex1 dR_42 as regs'; dand6 dR_42 as Hms G10 G12 G14 G15 Gkeep | pose proof ((SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite <- HD; apply Wst; lia))) as dR_42; dand7 dR_42 as regs' Hms G10 G12 G14 G15 Gkeep | destruct (SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite <- HD; apply Wst; lia)) as (regs' & Hms & G10 & G12 & G14 & G15 & Gkeep) ]).
  set (M' := wbytes M (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) in *.
  eapply (call_core cs E E R FULL model T (pc cs + 32) _ _ (nxt cs) regs' M' HC Hfresh (env_agree_refl _ _)).
  (* [comment removed for export] *)
  4: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r) as HR. unfold sr_get in HR.
    assert (Hrz : bv_eqb r 0%bv = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros Hc0. apply Hr0. apply bv_eq. exact Hc0. }
    rewrite Hrz in HR.
    destruct (Nat.eqb (ridx r) 15) eqn:E15.
    { apply Nat.eqb_eq in E15. rewrite (reg_of_ridx r 15 E15). refine (eq_trans G15 _). rewrite HloD. reflexivity. }
    destruct (Nat.eqb (ridx r) 14) eqn:E14.
    { apply Nat.eqb_eq in E14. rewrite (reg_of_ridx r 14 E14). refine (eq_trans G14 _). cbn [edenot]. f_equal; f_equal; lia. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12.
    { apply Nat.eqb_eq in E12. rewrite (reg_of_ridx r 12 E12). refine (eq_trans G12 _). cbn [edenot]. f_equal; lia. }
    destruct (Nat.eqb (ridx r) 10) eqn:E10.
    { apply Nat.eqb_eq in E10. rewrite (reg_of_ridx r 10 E10). refine (eq_trans G10 _). reflexivity. }
    apply Nat.eqb_neq in E15. apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E10.
    rewrite Gkeep; [exact HR| | | |]; intros Hrr; [apply E10 | apply E12 | apply E14 | apply E15]; rewrite Hrr; reflexivity.
  - (* [comment removed for export] *)
    assert (Hlen : length (pf_bytes c s (Z.to_nat (n - i))) = (4 * Z.to_nat cnt)%nat) by (unfold cnt; apply pf_bytes_length).
    assert (Hbase : bv_unsigned (Z_to_bv 64 (e - 4 * n)) = D) by (rewrite HD; apply u64_lit; lia).
    unfold know_ok. apply Forall_app_intro; [|apply Forall_app_intro].
    + fold cnt. apply (popfree_facts_sound E M lb lk cnt c s (Z.to_nat K) (Z_to_bv 64 (e - 4 * n)) Hbase); lia.
    + destruct (Z.ltb K cnt) eqn:HKc; [|constructor]. apply Z.ltb_lt in HKc.
      constructor; [|constructor]. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [unfold flat; lia|].
      intros q Hq. fold D. replace (D + q) with (bv_unsigned (Z_to_bv 64 (e - 4 * n)) + Z.of_nat (Z.to_nat q)) by lia.
      subst M'. apply wbytes_defined; rewrite Hlen; lia.
    + eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite Hlen; lia.
Qed.

Theorem node_x_sound_XIMemset :
  fill_spec SEGS (x_imemset A) 256 -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XIMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

Theorem node_x_sound_XMemset :
  fill_spec SEGS (x_memset A) two64 -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

Theorem node_x_sound_XIMemcpy :
  copy_spec SEGS (x_imemcpy A) -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XIMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemcpy :
  copy_spec SEGS (x_memcpy A) -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemIsZero :
  miz_spec SEGS (x_memiszero A) -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XMemIsZero.
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.

Theorem node_x_sound_XIStrncpy :
  istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XIStrncpy.
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.

Theorem node_x_sound_XPopFree :
  popfree_spec SEGS (x_popfree A) -> x_stmt SEGS A nx0 LIMIT SINV argH FS0 XPopFree.
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.

End Sound.

End APSX.
End Asan59m.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.

Module AsanMsb.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asangat.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanmsb_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hstep (k z : Z) : Z := Z.lor z (Z.shiftr z k).
Definition sm5 (u : Z) : Z := hstep 16 (hstep 8 (hstep 4 (hstep 2 (hstep 1 u)))).
Definition hi5 (u : Z) : Z := Z.shiftr (sm5 u) 32.
Definition sm6 (u : Z) : Z := Z.lor (sm5 u) (hi5 u).

Lemma hstep_lor : forall k a b, hstep k (Z.lor a b) = Z.lor (hstep k a) (hstep k b).
Proof.
  intros k a b. unfold hstep. rewrite Z.shiftr_lor.
  rewrite <- !Z.lor_assoc. f_equal. rewrite !Z.lor_assoc. rewrite (Z.lor_comm b (Z.shiftr a k)). reflexivity.
Qed.

Lemma sm5_lor : forall a b, sm5 (Z.lor a b) = Z.lor (sm5 a) (sm5 b).
Proof. intros. unfold sm5. rewrite !hstep_lor. reflexivity. Qed.

Lemma lor_bound : forall a b n, 0 <= a < 2 ^ n -> 0 <= b <= a -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n [Ha Hb] [Hb0 Hba].
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec b 0) as [->|Hbz]; [rewrite Z.lor_0_r; lia|].
  destruct (Z.eq_dec a 0) as [->|Haz]; [lia|].
  assert (Hn : 0 <= n) by (destruct (Z.neg_nonneg_cases n) as [Hn|Hn]; [rewrite Z.pow_neg_r in Hb by lia; lia | exact Hn]).
  assert (L1 : Z.log2 a < n) by (apply Z.log2_lt_pow2; lia).
  assert (L2 : Z.log2 b <= Z.log2 a) by (apply Z.log2_le_mono; lia).
  assert (Lp : 0 < Z.lor a b).
  { pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)). assert (Z.lor a b <> 0) by (intros H0; apply Z.lor_eq_0_iff in H0; lia). lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Lp)). rewrite Z.log2_lor by lia. lia.
Qed.

Lemma hstep_bound : forall k a n, 0 <= k -> 0 <= a < 2 ^ n -> 0 <= hstep k a < 2 ^ n.
Proof.
  intros k a n Hk [Ha Hb]. unfold hstep. apply lor_bound; [lia|].
  split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  destruct (Z.eq_dec a 0) as [->|Hnz]; [rewrite Z.div_0_l; lia|].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma sm5_bound : forall a n, 0 <= a < 2 ^ n -> 0 <= sm5 a < 2 ^ n.
Proof. intros. unfold sm5. repeat (apply hstep_bound; [lia|]). assumption. Qed.

Lemma lor_pow46 : forall u, 2 ^ 46 <= u < 2 ^ 47 -> Z.lor (2 ^ 46) u = u.
Proof.
  intros u Hu. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 46 n) as [<-|Hne]; [|reflexivity]. cbn [orb].
  symmetry. apply Z.testbit_true; [lia|]. replace (u / 2 ^ 46) with 1; [reflexivity|].
  apply Z.div_unique with (r := u - 2 ^ 46); [left|]; lia.
Qed.

Lemma sm5_46 : sm5 (2 ^ 46) = 2 ^ 47 - 2 ^ 15.
Proof. vm_compute. reflexivity. Qed.
Lemma hi5_46 : Z.shiftr (2 ^ 47 - 2 ^ 15) 32 = Z.ones 15.
Proof. vm_compute. reflexivity. Qed.

Lemma sm5_val : forall u, 2 ^ 46 <= u < 2 ^ 47 -> sm5 u = Z.lor (2 ^ 47 - 2 ^ 15) (sm5 u) /\ 0 <= sm5 u < 2 ^ 47.
Proof.
  intros u Hu. pose proof (sm5_bound u 47 ltac:(lia)) as B. split; [|exact B].
  rewrite <- (lor_pow46 u Hu) at 1. rewrite sm5_lor, sm5_46. reflexivity.
Qed.

Lemma hi5_val : forall u, 2 ^ 46 <= u < 2 ^ 47 -> hi5 u = Z.ones 15.
Proof.
  intros u Hu. unfold hi5. destruct (sm5_val u Hu) as [E B]. rewrite E, Z.shiftr_lor, hi5_46, Z.lor_comm.
  apply Z.lor_ones_low; [apply Z.shiftr_nonneg; lia|].
  destruct (Z.eq_dec (Z.shiftr (sm5 u) 32) 0) as [->|Hz]; [cbn; lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.shiftr_nonneg (sm5 u) 32) ltac:(lia)); lia|].
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 32 * 2 ^ 15) with (2 ^ 47). lia.
Qed.

Lemma sm6_val : forall u, 2 ^ 46 <= u < 2 ^ 47 -> sm6 u = Z.ones 47.
Proof.
  intros u Hu. unfold sm6. rewrite (hi5_val u Hu). destruct (sm5_val u Hu) as [E B]. rewrite E.
  replace (Z.lor (2 ^ 47 - 2 ^ 15) (sm5 u)) with (Z.lor (sm5 u) (2 ^ 47 - 2 ^ 15)) by apply Z.lor_comm.
  rewrite <- Z.lor_assoc. change (Z.lor (2 ^ 47 - 2 ^ 15) (Z.ones 15)) with (Z.ones 47).
  apply Z.lor_ones_low; [lia|].
  destruct (Z.eq_dec (sm5 u) 0) as [->|Hz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wstep (k : Z) (w : word) : word := v_or w (v_srli w k).

Lemma u_lit' : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u_lit. assumption. Qed.

Lemma wstep_Z : forall k z, 0 <= k -> 0 <= z < 2 ^ 47 -> wstep k (Z_to_bv 64 z) = Z_to_bv 64 (hstep k z) /\ 0 <= hstep k z < 2 ^ 47.
Proof.
  intros k z Hk Hz. pose proof (hstep_bound k z 47 Hk Hz) as B. split; [|exact B].
  unfold wstep, v_or, v_srli, hstep. rewrite !u_lit' by lia.
  assert (Hs : 0 <= Z.shiftr z k < 2 ^ 64).
  { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
    apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite u_lit' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition W1 (a : word) : word := wstep 1 a.
Definition W2 (a : word) : word := wstep 2 (W1 a).
Definition W3 (a : word) : word := wstep 4 (W2 a).
Definition W4 (a : word) : word := wstep 8 (W3 a).
Definition W5 (a : word) : word := wstep 16 (W4 a).
Definition A5 (a : word) : word := v_srli (W5 a) 32.
Definition W6 (a : word) : word := v_or (W5 a) (A5 a).

Lemma msb_values : forall a : word, 2 ^ 46 <= bv_unsigned a < 2 ^ 47 ->
  W6 a = Z_to_bv 64 (Z.ones 47) /\ A5 a = Z_to_bv 64 (Z.ones 15).
Proof.
  intros a Ha. set (u := bv_unsigned a).
  assert (Ea : a = Z_to_bv 64 u) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (wstep_Z 1 u ltac:(lia) ltac:(lia)) as [E1 B1].
  destruct (wstep_Z 2 _ ltac:(lia) B1) as [E2 B2].
  destruct (wstep_Z 4 _ ltac:(lia) B2) as [E3 B3].
  destruct (wstep_Z 8 _ ltac:(lia) B3) as [E4 B4].
  destruct (wstep_Z 16 _ ltac:(lia) B4) as [E5 B5].
  assert (E5' : W5 a = Z_to_bv 64 (sm5 u)).
  { unfold W5, W4, W3, W2, W1, sm5. rewrite Ea, E1, E2, E3, E4, E5. reflexivity. }
  assert (B5' : 0 <= sm5 u < 2 ^ 47) by (unfold sm5; exact B5).
  assert (EA5 : A5 a = Z_to_bv 64 (hi5 u)).
  { unfold A5, hi5, v_srli. rewrite E5', u_lit' by lia. reflexivity. }
  assert (Bh : 0 <= hi5 u < 2 ^ 15).
  { unfold hi5. split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|].
    change (2 ^ 32 * 2 ^ 15) with (2 ^ 47). lia. }
  split.
  - unfold W6, v_or. rewrite E5', EA5, !u_lit' by lia. fold (sm6 u). rewrite (sm6_val u ltac:(lia)). reflexivity.
  - rewrite EA5, (hi5_val u ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
Definition MK (imm20 : bv 20) (imm12 : bv 12) : word :=
  let lo := v_addiw (v_lui (Z.shiftl (bv_signed imm20) 12)) (bv_signed imm12) in v_add lo (v_slli lo 32).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NZ.
  Variable SEGS : list Segment.
  Lemma step_srli_nz : forall regs pc mem rom w rd rs (sh : bv 6),
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
    bv_eqb rd 0%bv = false ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
  Proof. intros * F E D Z. rewrite (step_srli SEGS regs pc mem rom w rd rs sh F E D), Z. reflexivity. Qed.
  Lemma step_slli_nz : forall regs pc mem rom w rd rs (sh : bv 6),
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
    bv_eqb rd 0%bv = false ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
  Proof. intros * F E D Z. rewrite (step_slli SEGS regs pc mem rom w rd rs sh F E D), Z. reflexivity. Qed.
  Lemma step_lui_nz : forall regs pc mem rom w rd (imm : bv 20),
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Lui rd imm, 4%Z) ->
    bv_eqb rd 0%bv = false ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
  Proof. intros * F E D Z. rewrite (step_lui SEGS regs pc mem rom w rd imm F E D), Z. reflexivity. Qed.
  Lemma step_or_nz : forall regs pc mem rom w rd rs1 rs2,
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
    bv_eqb rd 0%bv = false ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
  Proof. intros * F E D Z. rewrite (step_or SEGS regs pc mem rom w rd rs1 rs2 F E D), Z. reflexivity. Qed.
  Lemma step_add_nz : forall regs pc mem rom w rd rs1 rs2,
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
    bv_eqb rd 0%bv = false ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
  Proof. intros * F E D Z. rewrite (step_add SEGS regs pc mem rom w rd rs1 rs2 F E D), Z. reflexivity. Qed.
  Lemma step_addiw_nz : forall regs pc mem rom w rd rs (imm : bv 12),
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
    bv_eqb rd 0%bv = false ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd (v_addiw (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
  Proof. intros * F E D Z. rewrite (step_addiw SEGS regs pc mem rom w rd rs imm F E D), Z. reflexivity. Qed.
End NZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition spec6 (R0 R : bvmap 5 word) (t10 t11 t12 t13 t14 t15 : word) : Prop :=
  getr R 10 = t10 /\ getr R 11 = t11 /\ getr R 12 = t12 /\ getr R 13 = t13 /\ getr R 14 = t14 /\ getr R 15 = t15
  /\ forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr R r = getr R0 r.

Local Ltac rneq := let Hc := fresh "Hc" in intro Hc; apply (f_equal bv_unsigned) in Hc; cbv in Hc; discriminate Hc.
Local Ltac solve_upd :=
  intros R0 R t10 t11 t12 t13 t14 t15 v (H10 & H11 & H12 & H13 & H14 & H15 & Ho); unfold spec6;
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit;
  first [ rewrite getr_same by rneq; reflexivity
        | rewrite getr_other by rneq; assumption
        | intros r N10 N11 N12 N13 N14 N15; rewrite getr_other by assumption; apply Ho; assumption ].

Lemma upd10 : forall R0 R t10 t11 t12 t13 t14 t15 v, spec6 R0 R t10 t11 t12 t13 t14 t15 -> spec6 R0 (regupd R 10 v) v t11 t12 t13 t14 t15.
Proof. solve_upd. Qed.
Lemma upd11 : forall R0 R t10 t11 t12 t13 t14 t15 v, spec6 R0 R t10 t11 t12 t13 t14 t15 -> spec6 R0 (regupd R 11 v) t10 v t12 t13 t14 t15.
Proof. solve_upd. Qed.
Lemma upd12 : forall R0 R t10 t11 t12 t13 t14 t15 v, spec6 R0 R t10 t11 t12 t13 t14 t15 -> spec6 R0 (regupd R 12 v) t10 t11 v t13 t14 t15.
Proof. solve_upd. Qed.
Lemma upd13 : forall R0 R t10 t11 t12 t13 t14 t15 v, spec6 R0 R t10 t11 t12 t13 t14 t15 -> spec6 R0 (regupd R 13 v) t10 t11 t12 v t14 t15.
Proof. solve_upd. Qed.
Lemma upd14 : forall R0 R t10 t11 t12 t13 t14 t15 v, spec6 R0 R t10 t11 t12 t13 t14 t15 -> spec6 R0 (regupd R 14 v) t10 t11 t12 t13 v t15.
Proof. solve_upd. Qed.
Lemma upd15 : forall R0 R t10 t11 t12 t13 t14 t15 v, spec6 R0 R t10 t11 t12 t13 t14 t15 -> spec6 R0 (regupd R 15 v) t10 t11 t12 t13 t14 v.
Proof. solve_upd. Qed.
Lemma spec6_10 : forall R0 R t10 t11 t12 t13 t14 t15, spec6 R0 R t10 t11 t12 t13 t14 t15 -> getr R 10 = t10. Proof. intros * H; apply H. Qed.
Lemma spec6_11 : forall R0 R t10 t11 t12 t13 t14 t15, spec6 R0 R t10 t11 t12 t13 t14 t15 -> getr R 11 = t11. Proof. intros * H; apply H. Qed.
Lemma spec6_12 : forall R0 R t10 t11 t12 t13 t14 t15, spec6 R0 R t10 t11 t12 t13 t14 t15 -> getr R 12 = t12. Proof. intros * H; apply H. Qed.
Lemma spec6_13 : forall R0 R t10 t11 t12 t13 t14 t15, spec6 R0 R t10 t11 t12 t13 t14 t15 -> getr R 13 = t13. Proof. intros * H; apply H. Qed.
Lemma spec6_14 : forall R0 R t10 t11 t12 t13 t14 t15, spec6 R0 R t10 t11 t12 t13 t14 t15 -> getr R 14 = t14. Proof. intros * H; apply H. Qed.
Lemma spec6_15 : forall R0 R t10 t11 t12 t13 t14 t15, spec6 R0 R t10 t11 t12 t13 t14 t15 -> getr R 15 = t15. Proof. intros * H; apply H. Qed.
Lemma spec6_refl : forall R, spec6 R R (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15).
Proof. intros R. unfold spec6. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity || (intros; reflexivity). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Msb.
  Variable SEGS : list Segment.
  Variable x : Z.
  Hypothesis Hx : 0 <= x /\ x + 112 < 2 ^ 64.
  (* [comment removed for export] *)
  Variables w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : bv 32.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 x) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w3.
  Hypothesis F4 : fetch_word SEGS (Z_to_bv 64 (x + 12)) = Some w4.
  Hypothesis F5 : fetch_word SEGS (Z_to_bv 64 (x + 16)) = Some w5.
  Hypothesis F6 : fetch_word SEGS (Z_to_bv 64 (x + 20)) = Some w6.
  Hypothesis F7 : fetch_word SEGS (Z_to_bv 64 (x + 24)) = Some w7.
  Hypothesis F8 : fetch_word SEGS (Z_to_bv 64 (x + 28)) = Some w8.
  Hypothesis F9 : fetch_word SEGS (Z_to_bv 64 (x + 32)) = Some w9.
  Hypothesis F10 : fetch_word SEGS (Z_to_bv 64 (x + 36)) = Some w10.
  Hypothesis F11 : fetch_word SEGS (Z_to_bv 64 (x + 40)) = Some w11.
  Hypothesis F12 : fetch_word SEGS (Z_to_bv 64 (x + 44)) = Some w12.
  Hypothesis F13 : fetch_word SEGS (Z_to_bv 64 (x + 48)) = Some w13.
  Hypothesis F14 : fetch_word SEGS (Z_to_bv 64 (x + 52)) = Some w14.
  Hypothesis F15 : fetch_word SEGS (Z_to_bv 64 (x + 56)) = Some w15.
  Hypothesis F16 : fetch_word SEGS (Z_to_bv 64 (x + 60)) = Some w16.
  Hypothesis F17 : fetch_word SEGS (Z_to_bv 64 (x + 64)) = Some w17.
  Hypothesis F18 : fetch_word SEGS (Z_to_bv 64 (x + 68)) = Some w18.
  Hypothesis F19 : fetch_word SEGS (Z_to_bv 64 (x + 72)) = Some w19.
  Hypothesis F20 : fetch_word SEGS (Z_to_bv 64 (x + 76)) = Some w20.
  Hypothesis F21 : fetch_word SEGS (Z_to_bv 64 (x + 80)) = Some w21.
  Hypothesis F22 : fetch_word SEGS (Z_to_bv 64 (x + 84)) = Some w22.
  Hypothesis F23 : fetch_word SEGS (Z_to_bv 64 (x + 88)) = Some w23.
  Hypothesis F24 : fetch_word SEGS (Z_to_bv 64 (x + 92)) = Some w24.
  Hypothesis F25 : fetch_word SEGS (Z_to_bv 64 (x + 96)) = Some w25.
  Hypothesis F26 : fetch_word SEGS (Z_to_bv 64 (x + 100)) = Some w26.
  Hypothesis F27 : fetch_word SEGS (Z_to_bv 64 (x + 104)) = Some w27.
  Hypothesis F28 : fetch_word SEGS (Z_to_bv 64 (x + 108)) = Some w28.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis E4 : is_ecall w4 = false.
  Hypothesis E5 : is_ecall w5 = false.
  Hypothesis E6 : is_ecall w6 = false.
  Hypothesis E7 : is_ecall w7 = false.
  Hypothesis E8 : is_ecall w8 = false.
  Hypothesis E9 : is_ecall w9 = false.
  Hypothesis E10 : is_ecall w10 = false.
  Hypothesis E11 : is_ecall w11 = false.
  Hypothesis E12 : is_ecall w12 = false.
  Hypothesis E13 : is_ecall w13 = false.
  Hypothesis E14 : is_ecall w14 = false.
  Hypothesis E15 : is_ecall w15 = false.
  Hypothesis E16 : is_ecall w16 = false.
  Hypothesis E17 : is_ecall w17 = false.
  Hypothesis E18 : is_ecall w18 = false.
  Hypothesis E19 : is_ecall w19 = false.
  Hypothesis E20 : is_ecall w20 = false.
  Hypothesis E21 : is_ecall w21 = false.
  Hypothesis E22 : is_ecall w22 = false.
  Hypothesis E23 : is_ecall w23 = false.
  Hypothesis E24 : is_ecall w24 = false.
  Hypothesis E25 : is_ecall w25 = false.
  Hypothesis E26 : is_ecall w26 = false.
  Hypothesis E27 : is_ecall w27 = false.
  Hypothesis E28 : is_ecall w28 = false.
  Hypothesis D1 : decode_any w1 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (Lui 12 349525, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Lui 13 209715, 4%Z).
  Hypothesis D4 : decode_any w4 = Some (Lui 14 61681, 4%Z).
  Hypothesis D5 : decode_any w5 = Some (Lui 15 4112, 4%Z).
  Hypothesis D6 : decode_any w6 = Some (Op ALU_OR 10 10 11, 4%Z).
  Hypothesis D7 : decode_any w7 = Some (OpImm32 11 12 1365, 4%Z).
  Hypothesis D8 : decode_any w8 = Some (OpImm32 12 13 819, 4%Z).
  Hypothesis D9 : decode_any w9 = Some (OpImm32 13 14 3855, 4%Z).
  Hypothesis D10 : decode_any w10 = Some (OpImm32 14 15 257, 4%Z).
  Hypothesis D11 : decode_any w11 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
  Hypothesis D12 : decode_any w12 = Some (Op ALU_OR 10 10 15, 4%Z).
  Hypothesis D13 : decode_any w13 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
  Hypothesis D14 : decode_any w14 = Some (Op ALU_ADD 11 11 15, 4%Z).
  Hypothesis D15 : decode_any w15 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
  Hypothesis D16 : decode_any w16 = Some (Op ALU_ADD 12 12 15, 4%Z).
  Hypothesis D17 : decode_any w17 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
  Hypothesis D18 : decode_any w18 = Some (Op ALU_ADD 13 13 15, 4%Z).
  Hypothesis D19 : decode_any w19 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
  Hypothesis D20 : decode_any w20 = Some (Op ALU_ADD 14 14 15, 4%Z).
  Hypothesis D21 : decode_any w21 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
  Hypothesis D22 : decode_any w22 = Some (Op ALU_OR 10 10 15, 4%Z).
  Hypothesis D23 : decode_any w23 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
  Hypothesis D24 : decode_any w24 = Some (Op ALU_OR 10 10 15, 4%Z).
  Hypothesis D25 : decode_any w25 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
  Hypothesis D26 : decode_any w26 = Some (Op ALU_OR 10 10 15, 4%Z).
  Hypothesis D27 : decode_any w27 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
  Hypothesis D28 : decode_any w28 = Some (Op ALU_OR 10 10 15, 4%Z).

  Definition msb_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 10 = Z_to_bv 64 (Z.ones 47)
    /\ getr regs' 11 = MK 349525 1365 /\ getr regs' 12 = MK 209715 819 /\ getr regs' 13 = MK 61681 3855 /\ getr regs' 14 = MK 4112 257
    /\ getr regs' 15 = Z_to_bv 64 (Z.ones 15)
    /\ forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r.

  (* [comment removed for export] *)
  Definition lo20 (imm20 : bv 20) : word := v_lui (Z.shiftl (bv_signed imm20) 12).
  Definition lo32 (imm20 : bv 20) (imm12 : bv 12) : word := v_addiw (lo20 imm20) (bv_signed imm12).
  Definition msb_rf (regs : bvmap 5 word) : bvmap 5 word :=
    let a := getr regs 10 in
    let r1 := regupd regs 11 (v_srli a 1) in
    let r2 := regupd r1 12 (lo20 349525) in
    let r3 := regupd r2 13 (lo20 209715) in
    let r4 := regupd r3 14 (lo20 61681) in
    let r5 := regupd r4 15 (lo20 4112) in
    let r6 := regupd r5 10 (W1 a) in
    let r7 := regupd r6 11 (lo32 349525 1365) in
    let r8 := regupd r7 12 (lo32 209715 819) in
    let r9 := regupd r8 13 (lo32 61681 3855) in
    let r10 := regupd r9 14 (lo32 4112 257) in
    let r11 := regupd r10 15 (v_srli (W1 a) 2) in
    let r12 := regupd r11 10 (W2 a) in
    let r13 := regupd r12 15 (v_slli (lo32 349525 1365) 32) in
    let r14 := regupd r13 11 (MK 349525 1365) in
    let r15 := regupd r14 15 (v_slli (lo32 209715 819) 32) in
    let r16 := regupd r15 12 (MK 209715 819) in
    let r17 := regupd r16 15 (v_slli (lo32 61681 3855) 32) in
    let r18 := regupd r17 13 (MK 61681 3855) in
    let r19 := regupd r18 15 (v_slli (lo32 4112 257) 32) in
    let r20 := regupd r19 14 (MK 4112 257) in
    let r21 := regupd r20 15 (v_srli (W2 a) 4) in
    let r22 := regupd r21 10 (W3 a) in
    let r23 := regupd r22 15 (v_srli (W3 a) 8) in
    let r24 := regupd r23 10 (W4 a) in
    let r25 := regupd r24 15 (v_srli (W4 a) 16) in
    let r26 := regupd r25 10 (W5 a) in
    let r27 := regupd r26 15 (A5 a) in
    regupd r27 10 (W6 a).

  (* [comment removed for export] *)
  Local Ltac istep tac upd k :=
    lazymatch goal with
    | S : spec6 ?regs ?R _ _ _ _ _ _ |- msteps _ (mkst ?R _ _ _) _ =>
        eapply mst_step; [ reflexivity | tac | ];
        (* [comment removed for export] *)
        rewrite ?(spec6_10 _ _ _ _ _ _ _ _ S), ?(spec6_11 _ _ _ _ _ _ _ _ S), ?(spec6_12 _ _ _ _ _ _ _ _ S),
                ?(spec6_13 _ _ _ _ _ _ _ _ S), ?(spec6_14 _ _ _ _ _ _ _ _ S), ?(spec6_15 _ _ _ _ _ _ _ _ S);
        let S' := fresh "S" in
        lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => pose proof (upd _ _ _ _ _ _ _ _ v S) as S' end;
        clear S;
        lazymatch type of S' with spec6 _ ?R' _ _ _ _ _ _ => let Rn := fresh "R" in set (Rn := R') in * end;
        rename S' into S;
        rewrite v_addi_lit by lia;
        lazymatch goal with |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => replace q with (x + k) by lia end
    end.

  Lemma msb_steps : forall regs M rom,
    msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst (msb_rf regs) (Z_to_bv 64 (x + 112)) M rom)
    /\ spec6 regs (msb_rf regs) (W6 (getr regs 10)) (MK 349525 1365) (MK 209715 819) (MK 61681 3855) (MK 4112 257) (A5 (getr regs 10)).
  Proof.
    intros regs M rom. set (a := getr regs 10). split.
    2: { cbv beta zeta delta [msb_rf]. fold a.
         (* [comment removed for export] *)
         repeat (first [ lazymatch goal with |- spec6 _ (regupd _ ?r _) _ _ _ _ _ _ =>
                           lazymatch r with
                           | 10%bv => eapply upd10 | 11%bv => eapply upd11 | 12%bv => eapply upd12
                           | 13%bv => eapply upd13 | 14%bv => eapply upd14 | 15%bv => eapply upd15 end end
                       | eapply upd10 | eapply upd11 | eapply upd12 | eapply upd13 | eapply upd14 | eapply upd15]).
         apply spec6_refl. }
    pose proof (spec6_refl regs) as S. fold a in S.
    istep ltac:(eapply (step_srli_nz SEGS); [exact F1 | exact E1 | exact D1 | reflexivity]) upd11 4.
    istep ltac:(eapply (step_lui_nz SEGS); [exact F2 | exact E2 | exact D2 | reflexivity]) upd12 8.
    istep ltac:(eapply (step_lui_nz SEGS); [exact F3 | exact E3 | exact D3 | reflexivity]) upd13 12.
    istep ltac:(eapply (step_lui_nz SEGS); [exact F4 | exact E4 | exact D4 | reflexivity]) upd14 16.
    istep ltac:(eapply (step_lui_nz SEGS); [exact F5 | exact E5 | exact D5 | reflexivity]) upd15 20.
    istep ltac:(eapply (step_or_nz SEGS); [exact F6 | exact E6 | exact D6 | reflexivity]) upd10 24.
    istep ltac:(eapply (step_addiw_nz SEGS); [exact F7 | exact E7 | exact D7 | reflexivity]) upd11 28.
    istep ltac:(eapply (step_addiw_nz SEGS); [exact F8 | exact E8 | exact D8 | reflexivity]) upd12 32.
    istep ltac:(eapply (step_addiw_nz SEGS); [exact F9 | exact E9 | exact D9 | reflexivity]) upd13 36.
    istep ltac:(eapply (step_addiw_nz SEGS); [exact F10 | exact E10 | exact D10 | reflexivity]) upd14 40.
    istep ltac:(eapply (step_srli_nz SEGS); [exact F11 | exact E11 | exact D11 | reflexivity]) upd15 44.
    istep ltac:(eapply (step_or_nz SEGS); [exact F12 | exact E12 | exact D12 | reflexivity]) upd10 48.
    istep ltac:(eapply (step_slli_nz SEGS); [exact F13 | exact E13 | exact D13 | reflexivity]) upd15 52.
    istep ltac:(eapply (step_add_nz SEGS); [exact F14 | exact E14 | exact D14 | reflexivity]) upd11 56.
    istep ltac:(eapply (step_slli_nz SEGS); [exact F15 | exact E15 | exact D15 | reflexivity]) upd15 60.
    istep ltac:(eapply (step_add_nz SEGS); [exact F16 | exact E16 | exact D16 | reflexivity]) upd12 64.
    istep ltac:(eapply (step_slli_nz SEGS); [exact F17 | exact E17 | exact D17 | reflexivity]) upd15 68.
    istep ltac:(eapply (step_add_nz SEGS); [exact F18 | exact E18 | exact D18 | reflexivity]) upd13 72.
    istep ltac:(eapply (step_slli_nz SEGS); [exact F19 | exact E19 | exact D19 | reflexivity]) upd15 76.
    istep ltac:(eapply (step_add_nz SEGS); [exact F20 | exact E20 | exact D20 | reflexivity]) upd14 80.
    istep ltac:(eapply (step_srli_nz SEGS); [exact F21 | exact E21 | exact D21 | reflexivity]) upd15 84.
    istep ltac:(eapply (step_or_nz SEGS); [exact F22 | exact E22 | exact D22 | reflexivity]) upd10 88.
    istep ltac:(eapply (step_srli_nz SEGS); [exact F23 | exact E23 | exact D23 | reflexivity]) upd15 92.
    istep ltac:(eapply (step_or_nz SEGS); [exact F24 | exact E24 | exact D24 | reflexivity]) upd10 96.
    istep ltac:(eapply (step_srli_nz SEGS); [exact F25 | exact E25 | exact D25 | reflexivity]) upd15 100.
    istep ltac:(eapply (step_or_nz SEGS); [exact F26 | exact E26 | exact D26 | reflexivity]) upd10 104.
    istep ltac:(eapply (step_srli_nz SEGS); [exact F27 | exact E27 | exact D27 | reflexivity]) upd15 108.
    istep ltac:(eapply (step_or_nz SEGS); [exact F28 | exact E28 | exact D28 | reflexivity]) upd10 112.
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma msb_run : forall regs M rom,
    2 ^ 46 <= bv_unsigned (getr regs 10) < 2 ^ 47 ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 112)) M rom) /\ msb_post regs regs'.
  Proof.
    intros regs M rom Ha. destruct (msb_steps regs M rom) as [MS (S10 & S11 & S12 & S13 & S14 & S15 & So)].
    destruct (msb_values (getr regs 10) Ha) as [V0 V5].
    exists (msb_rf regs). split; [exact MS|]. unfold msb_post.
    rewrite S10, S11, S12, S13, S14, S15, V0, V5. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. exact So.
  Qed.
End Msb.

(* [comment removed for export] *)
Lemma MK1_val : MK 349525 1365 = Z_to_bv 64 0x5555555555555555. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma MK2_val : MK 209715 819 = Z_to_bv 64 0x3333333333333333. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma MK3_val : MK 61681 3855 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma MK4_val : MK 4112 257 = Z_to_bv 64 0x0101010101010101. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ones47_val : Z_to_bv 64 (Z.ones 47) = Z_to_bv 64 0x7fffffffffff. Proof. reflexivity. Qed.
Lemma ones15_val : Z_to_bv 64 (Z.ones 15) = Z_to_bv 64 0x7fff. Proof. reflexivity. Qed.
End AsanMsb.

Module Asanpid.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec ShapeAlg SpinAlg CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require RefMocc AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asanfjy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.AsanMsb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma regs_ok_ext : forall E sr R R', (forall r, getr R' r = getr R r) -> regs_ok E sr R -> regs_ok E sr R'.
Proof. intros E sr R R' H HR r. rewrite H. apply HR. Qed.

Local Ltac case_reg r lit G :=
  let Q := fresh "Q" in
  destruct (bv_eqb r lit) eqn:Q;
  [ unfold bv_eqb in Q; apply Z.eqb_eq in Q; apply bv_eq in Q; subst r;
    rewrite getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; discriminate Hc); symmetry; exact G
  | assert (r <> lit) by (intros ->; rewrite bv_eqb_refl in Q; discriminate Q);
    rewrite (getr_other _ lit _ r) by assumption ].

Lemma regs_ok_post6 : forall E sr R R' e10 e11 e12 e13 e14 e15,
  regs_ok E sr R ->
  getr R' 10%bv = edenot E e10 -> getr R' 11%bv = edenot E e11 -> getr R' 12%bv = edenot E e12 ->
  getr R' 13%bv = edenot E e13 -> getr R' 14%bv = edenot E e14 -> getr R' 15%bv = edenot E e15 ->
  (forall r : Prelude.reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr R' r = getr R r) ->
  regs_ok E (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 10 e10) 11 e11) 12 e12) 13 e13) 14 e14) 15 e15) R'.
Proof.
  intros E sr R R' e10 e11 e12 e13 e14 e15 HR G10 G11 G12 G13 G14 G15 Go.
  pose proof (regs_ok_set_n E _ _ 15 e15 _ (regs_ok_set_n E _ _ 14 e14 _ (regs_ok_set_n E _ _ 13 e13 _
             (regs_ok_set_n E _ _ 12 e12 _ (regs_ok_set_n E _ _ 11 e11 _ (regs_ok_set_n E sr R 10 e10 _ HR
              ltac:(lia) eq_refl) ltac:(lia) eq_refl) ltac:(lia) eq_refl) ltac:(lia) eq_refl) ltac:(lia) eq_refl) ltac:(lia) eq_refl) as K.
  replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in K by (apply bv_eq; reflexivity). replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in K by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in K by (apply bv_eq; reflexivity). replace (Z_to_bv 5 (Z.of_nat 13)) with (13%bv : bv 5) in K by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) in K by (apply bv_eq; reflexivity). replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) in K by (apply bv_eq; reflexivity).
  eapply regs_ok_ext; [|exact K]. intros r. symmetry.
  case_reg r (15%bv : bv 5) G15. case_reg r (14%bv : bv 5) G14. case_reg r (13%bv : bv 5) G13.
  case_reg r (12%bv : bv 5) G12. case_reg r (11%bv : bv 5) G11. case_reg r (10%bv : bv 5) G10.
  symmetry. apply Go; assumption.
Qed.

Section HookSound.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis NX0_ok : nx0_ok nx0.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
  #[local] Notation node1_stmt := (APS.node1_stmt SEGS A nx0 LIMIT SINV argH FS0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable msbpc : Z.
  Hypothesis Hmsbpc : 0 <= msbpc /\ msbpc + 112 < 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis MSB : forall regs M rom,
    2 ^ 46 <= bv_unsigned (getr regs 10%bv) < 2 ^ 47 ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 msbpc) M rom) (mkst regs' (Z_to_bv 64 (msbpc + 112)) M rom)
                  /\ msb_post regs regs'.

  (* [comment removed for export] *)
  Lemma msb_state_eq : forall (cs : acs) (p : Z) (e0 e1 e2 e3 e4 e5 : expr),
    set_pc (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg cs 10 e0) 11 e1) 12 e2) 13 e3) 14 e4) 15 e5) p
    = with_ss cs (mk_ss p (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs)) 10 e0) 11 e1) 12 e2) 13 e3) 14 e4) 15 e5)
                       (s_know (a_ss cs)) (s_next (a_ss cs))).
  Proof. reflexivity. Qed.
  Lemma xn_msb_sound : node1_stmt always (fun cs => xn_msb msbpc cs).
  Proof.
    intros cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold xn_msb in Hn.
    destruct (Z.eqb (pc cs) msbpc) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc.
    destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
    destruct (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool eqn:Hb; [|discriminate].
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    injection Hn as <-.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 10) lo HK Hlo) as L1.
    pose proof (xhi_sound SEGS E _ (kn cs) (reg cs 10) hi HK Hhi) as L2.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    assert (Ha : 2 ^ 46 <= bv_unsigned (getr R 10%bv) < 2 ^ 47) by (rewrite H10; lia).
    set (H2 := Hv A E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    destruct (MSB R (mrestrict H2 FULL) (seg_rom SEGS) Ha) as [R' [Hms Hpost]].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (msbpc + 112)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis SEGS A SEGS_in_hull E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (msbpc + 112)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (msbpc + 112)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, AP.pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk.
    change (msbpc + MSB_LEN) with (msbpc + 112) in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    rewrite msb_state_eq.
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact HK | intros; reflexivity].
    cbn [s_regs]. (first [ dand7 Hpost as P10 P11 P12 P13 P14 P15 Po | destruct Hpost as (P10 & P11 & P12 & P13 & P14 & P15 & Po) ]).
    eapply regs_ok_post6; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | | | | | | | exact Po];
      cbn [edenot]; [rewrite P10, ones47_val | rewrite P11, MK1_val | rewrite P12, MK2_val | rewrite P13, MK3_val
                    | rewrite P14, MK4_val | rewrite P15, ones15_val]; reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc_cover_sound : forall allk k b o,
    qc_cover allk k b o = true ->
    exists zb zk zn, In (KZero (SA zb zk) zn) k
      /\ xinside allk b (o - 7) (ELit 8) zb zk zn = true /\ 3 <= ealign allk (eaddz (eadd zb zn) zk).
  Proof.
    intros allk k b o. induction k as [|K k IH]; intros H; [discriminate|].
    assert (STEP : qc_cover allk k b o = true ->
              exists zb zk zn, In (KZero (SA zb zk) zn) (K :: k)
                /\ xinside allk b (o - 7) (ELit 8) zb zk zn = true /\ 3 <= ealign allk (eaddz (eadd zb zn) zk)).
    { intros H'. (first [ pose proof ((IH H')) as dR_2; dex3 dR_2 as zb zk zn; dand3 dR_2 as Hin Hx Ha | pose proof ((IH H')) as dR_2; dand6 dR_2 as zb zk zn Hin Hx Ha | destruct (IH H') as (zb & zk & zn & Hin & Hx & Ha) ]). exists zb, zk, zn. split; [right; exact Hin | split; assumption]. }
    cbn [qc_cover] in H. destruct K as [| [zb zk] zn | | | | | | | |]; try exact (STEP H).
    apply orb_prop in H as [H|H]; [|exact (STEP H)].
    apply andb_prop in H as [Hx Ha]. apply Z.leb_le in Ha.
    exists zb, zk, zn. split; [left; reflexivity | split; assumption].
  Qed.

  Lemma qc_fact_sound : forall E M k r, know_ok SEGS E M k -> know_ok SEGS E M (qc_fact k (facts_of k) r).
  Proof.
    intros E M k r HK. unfold qc_fact.
    destruct (split_lit r) as [b o] eqn:Hbo.
    destruct (qc_cover k k b o) eqn:Hc; [|constructor].
    destruct (split_lit (mkAluK (facts_of k) Instr.ALU_AND r (ELit (-8)))) as [c q] eqn:Hcq.
    destruct (flat_x k c q (ELit 8)) eqn:Hf; [|constructor].
    (first [ pose proof ((qc_cover_sound k k b o Hc)) as dR_3; dex3 dR_3 as zb zk zn; dand3 dR_3 as Hin Hx Ha | pose proof ((qc_cover_sound k k b o Hc)) as dR_3; dand6 dR_3 as zb zk zn Hin Hx Ha | destruct (qc_cover_sound k k b o Hc) as (zb & zk & zn & Hin & Hx & Ha) ]).
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HZ. cbn [kentry_ok] in HZ. destruct HZ as [HZf HZ0].
    destruct (xinside_sound SEGS E M k b (o - 7) (ELit 8) zb zk zn HK Hx) as [X1 X2].
    (first [ pose proof ((flat_x_sound SEGS E M k c q (ELit 8) HK Hf)) as dR_4; dand3 dR_4 as F1 F2 F3 | pose proof (flat_x_sound SEGS E M k c q (ELit 8) HK Hf) as (F1 & F2 & F3) ]).
    destruct (ealign_sound SEGS E M k (eaddz (eadd zb zn) zk) HK) as [_ Hal].
    (* [comment removed for export] *)
    unfold elenZ in *. rewrite !edenot_lit, !u64_lit in * by lia.
    unfold estart in *. cbn [a_base a_off] in *. unfold flat in HZf. unfold estart in HZf. cbn [a_base a_off] in HZf.
    set (ub := bv_unsigned (edenot E b)) in *. set (uzb := bv_unsigned (edenot E zb)) in *. set (uzn := bv_unsigned (edenot E zn)) in *.
    set (uc := bv_unsigned (edenot E c)) in *.
    (* [comment removed for export] *)
    assert (Hend : (8 | uzb + zk + uzn)).
    { unfold eaddz, eadd in Hal. rewrite !mkAlu_denot, edenot_lit, !u_add64, Z_to_bv_unsigned in Hal. unfold bv_wrap in Hal.
      change (bv_modulus 64) with (2 ^ 64) in Hal. fold uzb uzn in Hal.
      assert (H8 : (8 | 2 ^ ealign k (eaddz (eadd zb zn) zk))).
      { exists (2 ^ (ealign k (eaddz (eadd zb zn) zk) - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      pose proof (Z.divide_trans _ _ _ H8 Hal) as D. clear H8 Hal.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (E1 : ((uzb + uzn) mod 2 ^ 64 + zk mod 2 ^ 64) mod 2 ^ 64 = (uzb + zk + uzn) mod 2 ^ 64).
      { rewrite <- Z.add_mod by lia. f_equal. lia. }
      rewrite E1 in D.
      destruct (Z.eq_dec (uzb + zk + uzn) (2 ^ 64)) as [E64|N64].
      - rewrite E64. exists (2 ^ 61). reflexivity.
      - rewrite Z.mod_small in D by lia. exact D. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    (* [comment removed for export] *)
    assert (Hr : bv_unsigned (edenot E r) = ub + o).
    { rewrite (split_lit_denot E r b o Hbo). rewrite u64_lit; [reflexivity|]. fold ub. lia. }
    assert (Hround : uc + q = ub + o - (ub + o) mod 8).
    { pose proof (split_lit_denot E _ c q Hcq) as D. rewrite (mkAluK_denot SEGS E M (facts_of k)) in D by (apply facts_of_ok; exact HK).
      apply (f_equal bv_unsigned) in D. rewrite u_and64, Hr, edenot_lit in D.
      replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3) in D by reflexivity.
      rewrite land_highmask in D by lia. rewrite u64_lit in D by lia. change (2 ^ 3) with 8 in D. fold uc in D. lia. }
    constructor; [|constructor]. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite edenot_lit, u64_lit by lia. fold uc.
    split; [lia|]. intros i Hi. destruct Hend as [m Hm].
    replace (uc + q + i) with (uzb + zk + (uc + q + i - uzb - zk)) by lia. apply HZ0. lia.
  Qed.

  Lemma xn_qczero_sound : node1_stmt always xn_qczero.
  Proof.
    intros cs cs' E R FULL model T HC _ Hn Hk. unfold xn_qczero in Hn. injection Hn as <-.
    apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [|reflexivity].
    apply cs_ok_set_kn; [exact HC|].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    apply Forall_app; split; [apply qc_fact_sound; exact HK|]. apply Forall_app; split; [apply qc_fact_sound; exact HK| exact HK].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma two_atom_sound : forall E ts x y kx ky,
    two_atom ts x y = Some (kx, ky) -> tden E ts = kx * AX2S.uE E x + ky * AX2S.uE E y.
  Proof.
    intros E ts x y kx ky H. unfold two_atom in H.
    destruct ts as [|[k1 a1] [|[k2 a2] [|? ?]]]; try discriminate.
    destruct (expr_eqb a1 x && expr_eqb a2 y)%bool eqn:H1.
    - injection H as <- <-. apply andb_prop in H1 as [Ha Hb]. apply expr_eqb_eq in Ha. apply expr_eqb_eq in Hb. subst.
      cbn [tden]. lia.
    - destruct (expr_eqb a1 y && expr_eqb a2 x)%bool eqn:H2; [|discriminate].
      injection H as <- <-. apply andb_prop in H2 as [Ha Hb]. apply expr_eqb_eq in Ha. apply expr_eqb_eq in Hb. subst.
      cbn [tden]. lia.
  Qed.

  Lemma find_fact2_sound : forall E M allk k x y kx ky l h,
    know_ok SEGS E M allk -> know_ok SEGS E M k ->
    find_fact2 allk k x y = Some (kx, ky, l, h) ->
    l <= kx * AX2S.uE E x + ky * AX2S.uE E y <= h.
  Proof.
    intros E M allk k x y kx ky l h Hall HK. induction k as [|K k IH]; intros H; [discriminate|].
    inversion HK as [|K' k' HKK HK']; subst.
    cbn [find_fact2] in H.
    destruct K as [| | | | |e lo hi| | | |]; try exact (IH HK' H).
    destruct (two_atom (snd (lin_of e)) x y) as [[kx' ky']|] eqn:Ht; [|exact (IH HK' H)].
    destruct (fact_nowrap allk e hi) eqn:Hnw; [|exact (IH HK' H)].
    injection H as <- <- <- <-.
    cbn [kentry_ok] in HKK.
    pose proof (fact_nowrap_sound SEGS E M allk e lo hi Hall Hnw HKK) as Hv.
    rewrite (two_atom_sound E _ _ _ _ _ Ht) in Hv. lia.
  Qed.

  Lemma xn_pgdiff_sound : forall args, node1_stmt always (xn_pgdiff args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk.
    assert (SAME : cs' = cs -> srealizes SEGS (cfg_of SEGS R (AP.pc cs) FULL model) T).
    { intros ->. apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [exact HC|reflexivity]. }
    unfold xn_pgdiff in Hn.
    (* [comment removed for export] *)
    destruct args as [|a1 args]; [discriminate|]. destruct a1 as [|v| | | | | |]; try discriminate.
    destruct args as [|a2 args]; [discriminate|]. destruct a2 as [|w| | | | | |]; try discriminate.
    destruct args as [|a3 args]; [discriminate|]. destruct a3 as [|x| | | | | |]; try discriminate.
    destruct args as [|a4 args]; [discriminate|]. destruct a4 as [c| | | | | | |]; try discriminate.
    destruct args as [|? ?]; [|discriminate].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (find_fact2 (kn cs) (kn cs) (EVar x) (EVar v)) as [[[[kx1 kv] l1] h1]|] eqn:F1; [|injection Hn as <-; exact (SAME eq_refl)].
    destruct (find_fact2 (kn cs) (kn cs) (EVar x) (EVar w)) as [[[[kx2 kw] l2] h2]|] eqn:F2; [|injection Hn as <-; exact (SAME eq_refl)].
    destruct (Z.eqb kx1 kx2 && Z.eqb kv (- c) && Z.eqb kw (- c) && Z.ltb 0 c && negb (Nat.eqb v w))%bool eqn:Hc;
      [|injection Hn as <-; exact (SAME eq_refl)].
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc H0c]. apply andb_prop in Hc as [Hc Hkw]. apply andb_prop in Hc as [Hkx Hkv].
    apply Z.eqb_eq in Hkx. apply Z.eqb_eq in Hkv. apply Z.eqb_eq in Hkw. apply Z.ltb_lt in H0c. subst kx2 kv kw.
    set (a := zcdiv (l2 - h1) c) in Hn. set (b := (h2 - l1) / c) in Hn.
    destruct (Z.leb 0 a && Z.leb a b && Z.ltb b two64)%bool eqn:Hab; [|injection Hn as <-; exact (SAME eq_refl)].
    apply andb_prop in Hab as [Hab Hb]. apply andb_prop in Hab as [Ha Hab]. apply Z.leb_le in Ha. apply Z.leb_le in Hab. apply Z.ltb_lt in Hb.
    unfold two64 in Hb. injection Hn as <-.
    apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    pose proof (find_fact2_sound E _ (kn cs) (kn cs) (EVar x) (EVar v) kx1 (- c) l1 h1 HK HK F1) as R1.
    pose proof (find_fact2_sound E _ (kn cs) (kn cs) (EVar x) (EVar w) kx1 (- c) l2 h2 HK HK F2) as R2.
    unfold AX2S.uE in R1, R2. cbn [edenot] in R1, R2.
    set (X := bv_unsigned (ev E x)) in *. set (V := bv_unsigned (ev E v)) in *. set (W := bv_unsigned (ev E w)) in *.
    assert (HcVW : l2 - h1 <= c * (V - W) <= h2 - l1) by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HVW : a <= V - W <= b) by (unfold a, b, zcdiv; nia).
    cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. fold V W.
    pose proof (u64_range (ev E v)) as UV. pose proof (u64_range (ev E w)) as UW. fold V in UV. fold W in UW.
    rewrite Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Z_to_bv_succ : forall z, (Z_to_bv 64 z + 1)%bv = Z_to_bv 64 (z + 1).
  Proof.
    intros z. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Z.add_mod_idemp_l by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_hit_sound : forall E M k b m off,
    know_ok SEGS E M k -> bytes_hit SEGS k b off m = true ->
    0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat m <= 2 ^ 64 ->
    exists bs, length bs = m /\ rdn SEGS M (Z_to_bv 64 (estart E (SA b off))) m = Some bs.
  Proof.
    intros E M k b m. induction m as [|m IH]; intros off HK H Hlo Hhi.
    - exists []. split; reflexivity.
    - cbn [bytes_hit] in H.
      pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as L.
      destruct (know_lookup SEGS k b off 1 false [] []) as [v [|? ?] hints| | ]; try discriminate.
      (first [ pose proof ((L ltac:(constructor) ltac:(unfold flat; lia))) as dR_5; dex1 dR_5 as bs1; dand3 dR_5 as R1 L1 _ | pose proof ((L ltac:(constructor) ltac:(unfold flat; lia))) as dR_5; dand4 dR_5 as bs1 R1 L1 _ | destruct (L ltac:(constructor) ltac:(unfold flat; lia)) as (bs1 & R1 & L1 & _) ]).
      destruct bs1 as [|b1 [|? ?]]; try (cbn in L1; lia).
      (first [ pose proof ((IH (off + 1) HK H ltac:(unfold estart in *; cbn [a_base a_off] in *; lia) ltac:(unfold estart in *; cbn [a_base a_off] in *; lia))) as dR_6; dex1 dR_6 as bs; destruct dR_6 as [Lbs Rbs] | pose proof ((IH (off + 1) HK H ltac:(unfold estart in *; cbn [a_base a_off] in *; lia) ltac:(unfold estart in *; cbn [a_base a_off] in *; lia))) as dR_6; dand3 dR_6 as bs Lbs Rbs | destruct (IH (off + 1) HK H ltac:(unfold estart in *; cbn [a_base a_off] in *; lia) ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (bs & Lbs & Rbs) ]).
      exists (b1 :: bs). split; [cbn; lia|].
      apply rdn_cons1.
      + unfold adenot, v_addi in R1. cbn [a_base a_off] in R1. unfold estart. cbn [a_base a_off]. exact R1.
      + rewrite Z_to_bv_succ. unfold estart in *. cbn [a_base a_off] in *. rewrite <- Z.add_assoc. exact Rbs.
  Qed.

  Lemma xn_wordcell_sound : forall args, node1_stmt always (xn_wordcell SEGS nx0 args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_wordcell in Hn.
    destruct args as [|b [|[off| | | | | | |] [|[n| | | | | | |] [|? ?]]]]; try discriminate.
    destruct (Z.leb 1 n && Z.leb n 8 && fresh_ok nx0 cs && AP.expr_vars_lt (nxt cs) b && flat_x (kn cs) b off (ELit n)
              && bytes_hit SEGS (kn cs) b off (Z.to_nat n))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hhit]. apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hc Hvb].
    apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [H1 H8]. apply Z.leb_le in H1. apply Z.leb_le in H8.
    injection Hn as <-.
    set (w := Z.to_nat n) in *. set (v := nxt cs) in *.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    (first [ pose proof ((flat_x_sound SEGS E _ (kn cs) b off (ELit n) HK Hflat)) as dR_7; dand3 dR_7 as F1 F2 F3 | pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit n) HK Hflat) as (F1 & F2 & F3) ]).
    rewrite edenot_lit, u64_lit in F2, F3 by lia.
    (first [ pose proof ((bytes_hit_sound E _ (kn cs) b w off HK Hhit F1 ltac:(lia))) as dR_8; dex1 dR_8 as bs; destruct dR_8 as [Lbs Rbs] | pose proof ((bytes_hit_sound E _ (kn cs) b w off HK Hhit F1 ltac:(lia))) as dR_8; dand3 dR_8 as bs Lbs Rbs | destruct (bytes_hit_sound E _ (kn cs) b w off HK Hhit F1 ltac:(lia)) as (bs & Lbs & Rbs) ]).
    pose proof (lez_bound_len bs w Lbs) as Bbs.
    assert (Bw : 2 ^ (8 * Z.of_nat w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    set (a := Z_to_bv 64 (lez bs)). set (E' := ext1 E v a).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    (first [ pose proof ((fresh_ok_parts nx0 cs Hfresh)) as dR_9; dand7 dR_9 as Fsr Fkn Fmaps Fallow Fbrk Ffd Fle | destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle) ]).
    pose proof (cs_ok_agree SEGS A nx0 LIMIT NX0_ok SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
    assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
    pose proof (hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow) as HH.
    apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
    (* [comment removed for export] *)
    assert (KW : kentry_ok SEGS E' (Mr A argH E' cs model FULL) (KWord (SA b off) w (EVar v))).
    { cbn [kentry_ok]. unfold flat, estart, adenot, v_addi. cbn [a_base a_off edenot]. rewrite Hbv.
      unfold estart in F1, F2, Rbs. cbn [a_base a_off] in F1, F2, Rbs.
      split; [lia|]. split; [lia|].
      unfold Mr. rewrite HH. fold (Mr A argH E cs model FULL). rewrite Rbs. f_equal.
      unfold E'. rewrite ext1_at. unfold a, word_to_le_bytes. rewrite u64_lit by lia. rewrite <- Lbs. symmetry. apply Z_to_le_bytes_lez. }
    destruct HC'; constructor; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
      try assumption; try reflexivity.
    (* [comment removed for export] *)
    constructor; [exact KW | exact co_know0].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem XN1_sound : ext_stmt SEGS A nx0 LIMIT (XN1 SEGS A nx0 msbpc) SINV argH FS0.
  Proof.
    intros id args. unfold XN1.
    destruct id as [|[|[|[|[|[|id]]]]]].
    - intros cs cs' E R FULL model T _ _ H; discriminate H.
    - apply xn_msb_sound.
    - apply xn_wordcell_sound.
    - apply xn_qczero_sound.
    - intros cs cs' E R FULL model T _ _ H; discriminate H.
    - apply xn_pgdiff_sound.
    - intros cs cs' E R FULL model T _ _ H; discriminate H.
  Qed.
End HookSound.
End Asanpid.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asan59m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asanfjy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asanpid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx2 : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section HookSound2.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  #[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
  #[local] Notation node1_stmt := (APS.node1_stmt SEGS A nx0 LIMIT SINV argH FS0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cut_cell1_sound : forall E M b off n K,
    kentry_ok SEGS E M K -> Forall (kentry_ok SEGS E M) (cut_cell1 b off n K).
  Proof.
    intros E M b off n K HK. unfold cut_cell1.
    destruct K as [| [zb zk] zn | | lo hi | | | | | |]; try (constructor; [exact HK | constructor]).
    - (* [comment removed for export] *)
      destruct zn as [l0| | | | | | |]; try (constructor; [exact HK | constructor]).
      destruct (expr_eqb zb b && Z.leb zk off && Z.leb (off + Z.of_nat n) (zk + l0) && Z.leb 0 l0 && Z.ltb l0 two64)%bool eqn:Hc;
        [|constructor; [exact HK | constructor]].
      apply andb_prop in Hc as [Hc Hl2]. apply andb_prop in Hc as [Hc Hl1]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [_ Hlo].
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hl1. apply Z.ltb_lt in Hl2. unfold two64 in Hl2.
      cbn [kentry_ok] in HK. destruct HK as [Hf Hz]. unfold elenZ in Hf, Hz. rewrite edenot_lit, u64_lit in Hf, Hz by lia.
      destruct Hf as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4, Hz. cbn [a_base a_off] in F1, F2, F4, Hz.
      unfold ktrim. rewrite (Z.mod_small l0 (2 ^ 64)) by lia.
      apply Forall_app. split.
      + destruct (Z.ltb zk (Z.min off (zk + l0))) eqn:H1; [|constructor]. apply Z.ltb_lt in H1.
        constructor; [|constructor]. cbn [kentry_ok]. unfold elenZ. rewrite edenot_lit, u64_lit by lia.
        split.
        * unfold flat, estart. cbn [a_base a_off]. lia.
        * intros i Hi. unfold estart. cbn [a_base a_off]. apply Hz. lia.
      + destruct (Z.ltb (Z.max zk (off + Z.of_nat n)) (zk + l0)) eqn:H2; [|constructor]. apply Z.ltb_lt in H2.
        constructor; [|constructor]. cbn [kentry_ok]. unfold elenZ. rewrite edenot_lit, u64_lit by lia.
        split.
        * unfold flat, estart. cbn [a_base a_off]. lia.
        * intros i Hi. unfold estart. cbn [a_base a_off].
          replace (bv_unsigned (edenot E zb) + Z.max zk (off + Z.of_nat n) + i)
            with (bv_unsigned (edenot E zb) + zk + (Z.max zk (off + Z.of_nat n) - zk + i)) by lia.
          apply Hz. lia.
    - (* [comment removed for export] *)
      destruct b as [z| | | | | | |]; try (constructor; [exact HK | constructor]).
      destruct z; try (constructor; [exact HK | constructor]).
      destruct (Z.leb lo off && Z.leb (off + Z.of_nat n) hi)%bool eqn:Hc; [|constructor; [exact HK | constructor]].
      cbn [kentry_ok] in HK. destruct HK as (I1 & I2 & I3).
      apply Forall_app. split.
      + destruct (Z.ltb lo (Z.min off hi)) eqn:H1; [|constructor]. apply Z.ltb_lt in H1.
        constructor; [|constructor]. cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi. apply I3. lia.
      + cbv zeta. destruct (Z.ltb (Z.max lo (off + Z.of_nat n)) hi) eqn:H2; [|constructor]. apply Z.ltb_lt in H2.
        constructor; [|constructor]. cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi. apply I3. lia.
  Qed.

  Lemma cut_cell_sound : forall E M b off n k,
    know_ok SEGS E M k -> know_ok SEGS E M (flat_map (cut_cell1 b off n) k).
  Proof.
    intros E M b off n k HK. unfold know_ok in *. induction k as [|K k IH]; [constructor|].
    inversion HK as [|K' k' HKK HK']; subst. cbn [flat_map]. apply Forall_app. split.
    - apply cut_cell1_sound. exact HKK.
    - apply IH. exact HK'.
  Qed.

  Lemma xn_cell_sound : forall args, node1_stmt always (xn_cell SEGS args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_cell in Hn.
    destruct args as [|b [|[off| | | | | | |] [|[n| | | | | | |] [|? ?]]]]; try discriminate.
    destruct (Z.leb 1 n && Z.leb n 8 && flat_x (kn cs) b off (ELit n))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [H1 H8]. apply Z.leb_le in H1. apply Z.leb_le in H8.
    set (w := Z.to_nat n) in *.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (know_lookup_sound SEGS E _ (kn cs) b off w false [] [] HK ltac:(unfold w; lia) ltac:(unfold w; lia)) as L.
    destruct (know_lookup SEGS (kn cs) b off w false [] []) as [v [|? ?] hints| | ]; try discriminate.
    injection Hn as <-.
    pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit n) HK Hflat) as (F1 & F2 & F3).
    rewrite edenot_lit, u64_lit in F2, F3 by lia.
    assert (Hfl : flat E (SA b off) (Z.of_nat w)) by (unfold flat, w; rewrite Z2Nat.id by lia; lia).
    destruct (L ltac:(constructor) Hfl) as (bs & Rbs & Lbs & Vbs).
    apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [|reflexivity].
    apply cs_ok_set_kn; [exact HC|].
    constructor; [|apply cut_cell_sound; exact HK].
    cbn [kentry_ok]. split; [unfold w; lia|]. split; [exact Hfl|].
    rewrite Rbs. f_equal. unfold extz in Vbs. rewrite <- Vbs. symmetry.
    apply APSX.word_to_le_bytes_of_bytes_n; [exact Lbs | unfold w; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma respell_first_sound : forall E M allk k a e k',
    know_ok SEGS E M allk -> know_ok SEGS E M k -> respell_first allk k a e = Some k' -> know_ok SEGS E M k'.
  Proof.
    intros E M allk k a e. induction k as [|K k IH]; intros k' Hall HK H; [discriminate|].
    inversion HK as [|K0 k0 HKK HK']; subst.
    assert (STEP : forall r', respell_first allk k a e = Some r' -> know_ok SEGS E M (K :: r')).
    { intros r' Hr. constructor; [exact HKK | exact (IH r' Hall HK' Hr)]. }
    cbn [respell_first] in H.
    destruct K as [a' w v| | | | | | | | |];
      try (destruct (respell_first allk k a e) as [r'|] eqn:Hr; [injection H as <-; exact (STEP r' eq_refl) | discriminate]).
    destruct (saddr_eqb a' a).
    - destruct (respell_ok allk v e) eqn:Hre; [|discriminate]. injection H as <-.
      constructor; [|exact HK'].
      pose proof (respell_ok_sound SEGS E M allk v e Hall Hre) as Hev.
      cbn [kentry_ok] in HKK |- *. rewrite <- Hev. exact HKK.
    - destruct (respell_first allk k a e) as [r'|] eqn:Hr; [injection H as <-; exact (STEP r' eq_refl) | discriminate].
  Qed.

  Lemma xn_respell_cell_sound : forall args, node1_stmt always (xn_respell_cell args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_respell_cell in Hn.
    destruct args as [|b [|[off| | | | | | |] [|e [|? ?]]]]; try discriminate.
    destruct (AP.expr_vars_lt (nxt cs) e); [|discriminate].
    destruct (respell_first (kn cs) (kn cs) (SA b off) e) as [k'|] eqn:Hr; [|discriminate].
    injection Hn as <-.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. exact (respell_first_sound E _ (kn cs) (kn cs) (SA b off) e k' HK HK Hr).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xn_bitpin_sound : forall args, node1_stmt always (xn_bitpin args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_bitpin in Hn.
    destruct args as [|X [|[|b| | | | | |] [|[k| | | | | | |] [|? ?]]]]; try discriminate.
    cbv zeta in Hn.
    destruct (xlo (kn cs) X) as [lo1|] eqn:L1; [|discriminate].
    destruct (xhi (kn cs) X) as [hi1|] eqn:H1; [|discriminate].
    destruct (xlo (kn cs) (esub X (escale k (EVar b)))) as [lo2|] eqn:L2; [|discriminate].
    destruct (xhi (kn cs) (esub X (escale k (EVar b)))) as [hi2|] eqn:H2; [|discriminate].
    destruct (xhi (kn cs) (EVar b)) as [bh|] eqn:HB; [|discriminate].
    destruct (Z.ltb 0 k && Z.ltb k BITPIN_MAX && Z.leb 0 bh && Z.ltb (k * bh) BITPIN_MAX
              && Z.ltb hi1 BITPIN_MAX && Z.ltb hi2 BITPIN_MAX)%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc C6]. apply andb_prop in Hc as [Hc C5]. apply andb_prop in Hc as [Hc C4].
    apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
    apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. apply Z.leb_le in C3. apply Z.ltb_lt in C4. apply Z.ltb_lt in C5. apply Z.ltb_lt in C6.
    unfold BITPIN_MAX in *.
    destruct (Z.leb (Z.max 0 (zcdiv (lo1 - hi2) k)) (Z.min bh ((hi1 - lo2) / k))) eqn:Hac; [|discriminate].
    injection Hn as <-.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) X lo1 HK L1) as B1. pose proof (xhi_sound SEGS E _ (kn cs) X hi1 HK H1) as B2.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo2 HK L2) as B3. pose proof (xhi_sound SEGS E _ (kn cs) _ hi2 HK H2) as B4.
    pose proof (xhi_sound SEGS E _ (kn cs) (EVar b) bh HK HB) as B5.
    unfold esub, escale in B3, B4. rewrite mkAlu_denot, u_sub64, mkMd_denot, u_mul64, edenot_lit in B3, B4.
    cbn [edenot] in B3, B4, B5.
    set (x := bv_unsigned (edenot E X)) in *. set (B := bv_unsigned (ev E b)) in *.
    pose proof (u64_range (edenot E X)) as RX. pose proof (u64_range (ev E b)) as RB. fold x in RX. fold B in RB.
    rewrite (u64_lit k) in B3, B4 by lia.
    (* [comment removed for export] *)
    assert (HkB : 0 <= k * B < 2 ^ 62).
    { split; [apply Z.mul_nonneg_nonneg; lia|].
      apply Z.le_lt_trans with (k * bh); [apply Z.mul_le_mono_nonneg_l; lia | exact C4]. }
    rewrite (Z.mod_small (k * B) (2 ^ 64)) in B3, B4 by lia.
    assert (Hge : k * B <= x).
    { destruct (Z_le_gt_dec (k * B) x) as [Hle|Hgt]; [exact Hle|exfalso].
      assert (Hm : (x - k * B) mod 2 ^ 64 = x - k * B + 2 ^ 64).
      { symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
      rewrite Hm in B4. lia. }
    rewrite (Z.mod_small (x - k * B) (2 ^ 64)) in B3, B4 by lia.
    apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    cbn [kentry_ok edenot]. fold B.
    assert (Hlo : zcdiv (lo1 - hi2) k <= B).
    { unfold zcdiv. apply Z.opp_le_mono. rewrite Z.opp_involutive.
      apply Z.div_le_lower_bound; [exact C1|]. rewrite Z.mul_opp_r. lia. }
    assert (Hhi : B <= (hi1 - lo2) / k).
    { apply Z.div_le_lower_bound; [exact C1|]. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  Lemma take_kword0_sound : forall E M k a w k',
    know_ok SEGS E M k -> take_kword0 k a w = Some k' ->
    know_ok SEGS E M k' /\ kentry_ok SEGS E M (KWord a w (ELit 0)).
  Proof.
    intros E M k a w. induction k as [|K k IH]; intros k' HK H; [discriminate|].
    inversion HK as [|K0 k0 HKK HK']; subst. cbn [take_kword0] in H.
    assert (STEP : forall r', take_kword0 k a w = Some r' -> know_ok SEGS E M (K :: r') /\ kentry_ok SEGS E M (KWord a w (ELit 0))).
    { intros r' Hr. destruct (IH r' HK' Hr) as [I1 I2]. split; [constructor; [exact HKK | exact I1] | exact I2]. }
    destruct K as [a' w' v| | | | | | | | |];
      try (destruct (take_kword0 k a w) as [r'|] eqn:Hr; [injection H as <-; exact (STEP r' eq_refl) | discriminate]).
    destruct (saddr_eqb a' a) eqn:Ha.
    - destruct v as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
      destruct (Nat.eqb w' w) eqn:Hw; [|discriminate]. injection H as <-. apply Nat.eqb_eq in Hw. subst w'.
      unfold saddr_eqb in Ha. apply andb_prop in Ha as [Ha1 Ha2]. apply expr_eqb_eq in Ha1. apply Z.eqb_eq in Ha2.
      destruct a' as [ab ao], a as [bb bo]. cbn [a_base a_off] in Ha1, Ha2. subst. split; [exact HK' | exact HKK].
    - destruct (take_kword0 k a w) as [r'|] eqn:Hr; [injection H as <-; exact (STEP r' eq_refl) | discriminate].
  Qed.

  Lemma take_kzero_sound : forall E M k a m k',
    know_ok SEGS E M k -> take_kzero k a = Some (m, k') ->
    know_ok SEGS E M k' /\ kentry_ok SEGS E M (KZero a (ELit m)).
  Proof.
    intros E M k a m. induction k as [|K k IH]; intros k' HK H; [discriminate|].
    inversion HK as [|K0 k0 HKK HK']; subst. cbn [take_kzero] in H.
    assert (STEP : forall r', take_kzero k a = Some (m, r') -> know_ok SEGS E M (K :: r') /\ kentry_ok SEGS E M (KZero a (ELit m))).
    { intros r' Hr. destruct (IH r' HK' Hr) as [I1 I2]. split; [constructor; [exact HKK | exact I1] | exact I2]. }
    destruct K as [| a' zn | | | | | | | |];
      try (destruct (take_kzero k a) as [[m' r']|] eqn:Hr; [injection H as <- <-; exact (STEP r' eq_refl) | discriminate]).
    destruct zn as [z| | | | | | |];
      try (destruct (take_kzero k a) as [[m' r']|] eqn:Hr; [injection H as <- <-; exact (STEP r' eq_refl) | discriminate]).
    destruct (saddr_eqb a' a) eqn:Ha.
    - injection H as <- <-.
      unfold saddr_eqb in Ha. apply andb_prop in Ha as [Ha1 Ha2]. apply expr_eqb_eq in Ha1. apply Z.eqb_eq in Ha2.
      destruct a' as [ab ao], a as [bb bo]. cbn [a_base a_off] in Ha1, Ha2. subst. split; [exact HK' | exact HKK].
    - destruct (take_kzero k a) as [[m' r']|] eqn:Hr; [injection H as <- <-; exact (STEP r' eq_refl) | discriminate].
  Qed.

  Lemma wleb_zero_nth : forall w j, (w <= 8)%nat -> (j < w)%nat -> nth j (word_to_le_bytes w (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0.
  Proof.
    intros w j Hw Hj.
    do 9 (destruct w as [|w]; [ try lia; do 9 (destruct j as [|j]; [try lia; reflexivity|]); lia |]). lia.
  Qed.

  Lemma xn_zjoin_sound : forall args, node1_stmt always (xn_zjoin A args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_zjoin in Hn.
    destruct args as [|b [|[off| | | | | | |] [|[n| | | | | | |] [|? ?]]]]; try discriminate.
    destruct (Z.leb 1 n && Z.leb n 8 && Z.leb (img_lo A) (img_hi A) && flat_x (kn cs) b off (ELit n) && off_image_x A (kn cs) b off (ELit n))%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hoff]. apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [H1 H8].
    apply Z.leb_le in H1. apply Z.leb_le in H8. apply Z.leb_le in Himg.
    set (w := Z.to_nat n) in *.
    destruct (take_kword0 (kn cs) (SA b off) w) as [k1|] eqn:T1; [|discriminate].
    destruct (take_kzero k1 (SA b (off + n))) as [[m k2]|] eqn:T2; [|discriminate].
    destruct (Z.leb 0 m && Z.ltb (n + m) two64)%bool eqn:Hm; [|discriminate].
    apply andb_prop in Hm as [Hm0 Hm1]. apply Z.leb_le in Hm0. apply Z.ltb_lt in Hm1. unfold two64 in Hm1.
    injection Hn as <-.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    set (M := Mr A argH E cs model FULL) in *.
    destruct (take_kword0_sound E M _ _ _ _ HK T1) as [HK1 HW].
    destruct (take_kzero_sound E M _ _ _ _ HK1 T2) as [HK2 HZ].
    pose proof (flat_x_sound SEGS E M (kn cs) b off (ELit n) HK Hflat) as (F1 & F2 & F3).
    rewrite edenot_lit, u64_lit in F2, F3 by lia.
    pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HK Hoff) as AP0.
    pose proof HULL_ok as HU; unfold hull_ok, KHI in HU.
    rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
    unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
    apply (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))); [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. fold M. constructor; [|exact HK2].
    cbn [kentry_ok] in HW, HZ |- *. destruct HW as (W1 & W2 & W3). destruct HZ as [Z1 Z2].
    unfold elenZ in *. rewrite edenot_lit in *. rewrite (u64_lit m) in Z1, Z2 by lia. rewrite (u64_lit (n + m)) by lia.
    unfold flat, estart in *. cbn [a_base a_off] in *.
    set (ub := bv_unsigned (edenot E b)) in *.
    split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i n) as [Hlt|Hge].
    - (* [comment removed for export] *)
      assert (Hj : (Z.to_nat i < w)%nat) by (unfold w; lia).
      assert (Hua : bv_unsigned (adenot E (SA b off)) = ub + off).
      { unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. fold ub. apply Z.mod_small. lia. }
      pose proof (APSX.rdn_nth SEGS M w (adenot E (SA b off)) _ (Z.to_nat i) ltac:(rewrite Hua; unfold w; lia) W3 Hj) as R1.
      rewrite Hua, Z2Nat.id in R1 by lia.
      rewrite (wleb_zero_nth w (Z.to_nat i)) in R1 by (unfold w; lia).
      cbn [rdn] in R1.
      set (x := Z_to_bv 64 (ub + off + i)) in *.
      assert (Hx : bv_unsigned x = ub + off + i) by (unfold x; apply u64_lit; lia).
      assert (Hh : in_hull A (bv_unsigned x) = false).
      { rewrite Hx. unfold in_hull. apply andb_false_iff. destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
      destruct (M x) as [bx|] eqn:HMx.
      + injection R1 as ->. reflexivity.
      + rewrite (seg_rom_off_hull SEGS A SEGS_in_hull x Hh) in R1. discriminate.
    - replace (ub + off + i) with (ub + (off + n) + (i - n)) by lia. apply Z2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem XN2_sound : forall msbpc,
    ext_stmt SEGS A nx0 LIMIT (XN1 SEGS A nx0 msbpc) SINV argH FS0 ->
    ext_stmt SEGS A nx0 LIMIT (XN2 SEGS A nx0 msbpc) SINV argH FS0.
  Proof.
    intros msbpc H1 id args. unfold XN2.
    destruct id as [|[|[|[|[|[|[|[|[|[|id]]]]]]]]]]; try exact (H1 _ args).
    - apply xn_cell_sound.
    - apply xn_respell_cell_sound.
    - apply xn_bitpin_sound.
    - apply xn_zjoin_sound.
  Qed.
End HookSound2.
