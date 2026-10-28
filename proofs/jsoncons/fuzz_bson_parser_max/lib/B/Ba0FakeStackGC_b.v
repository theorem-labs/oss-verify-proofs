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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b
  Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_r69818_698c8_b Ba0_code_r69654_69674_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma v_sll_lit : forall i k, (0 <= k < 64)%Z -> (0 <= i < 2 ^ 64)%Z -> v_sll (Z_to_bv 64 i) (Z_to_bv 64 k) = Z_to_bv 64 (i * 2 ^ k).
Proof.
  intros i k Hk Hi. unfold v_sll. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma v_srl_lit : forall i k, (0 <= k < 64)%Z -> (0 <= i < 2 ^ 64)%Z -> v_srl (Z_to_bv 64 i) (Z_to_bv 64 k) = Z_to_bv 64 (i / 2 ^ k).
Proof.
  intros i k Hk Hi. unfold v_srl. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma u_Z2bv8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. Qed.

Lemma wbytes_out_any_gc : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  intros bs m addr x Hnw [Hx|Hx]; [apply wbytes_below; assumption | apply wbytes_above; exact Hx].
Qed.

Section FPX_0. Context {fx : PropExec.FPState}.
Lemma step_sll_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sll (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sll segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_srl_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SRL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_srl (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_srl segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
End FPX_0.
(* [comment removed for export] *)
Ltac stepsv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) => eapply step_sll_at with (v := vv)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) => eapply step_srl_at with (v := vv)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) => eapply step_subw_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac mlbq F D z R :=
  chain_step; [reflexivity
    | eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section INNER.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variables fs c nfr nlog frsz flb sparg bot : Z.      (* [comment removed for export] *)
  Variables flag rs : Z -> Z.                          (* [comment removed for export] *)
  Hypothesis Hc : (0 <= c <= 10)%Z.
  Hypothesis Hnlog : nlog = (14 - c)%Z.
  Hypothesis Hnfr : nfr = (2 ^ nlog)%Z.
  Hypothesis Hfrsz : frsz = (2 ^ (6 + c))%Z.
  Hypothesis Hflb : flb = (fs + 4096 + 32768 - 2 * nfr)%Z.                 (* [comment removed for export] *)
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis HL : rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
  Hypothesis HF : forall i, (0 <= i < nfr)%Z -> rdn ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag i)] /\ (0 <= flag i < 256)%Z.
  Hypothesis HR : forall i, (0 <= i < nfr)%Z -> flag i <> 0%Z ->
    rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs i)))
    /\ (0 <= rs i < 2 ^ 64)%Z /\ (rs i <= bot \/ sparg <= rs i)%Z.        (* [comment removed for export] *)

  Lemma nfr_facts : (16 <= nfr <= 16384)%Z /\ (64 <= frsz <= 65536)%Z /\ (nfr * frsz = 2 ^ 20)%Z /\ (0 <= nlog <= 14)%Z.
  Proof.
    subst nlog nfr frsz. assert (E : (14 - c + (6 + c) = 20)%Z) by lia.
    repeat split; try lia.
    - change 16%Z with (2 ^ 4)%Z. apply Z.pow_le_mono_r; lia.
    - change 16384%Z with (2 ^ 14)%Z. apply Z.pow_le_mono_r; lia.
    - change 64%Z with (2 ^ 6)%Z. apply Z.pow_le_mono_r; lia.
    - change 65536%Z with (2 ^ 16)%Z. apply Z.pow_le_mono_r; lia.
    - rewrite <- Z.pow_add_r by lia. rewrite E. reflexivity.
  Qed.

  Definition gi_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 27 = Z_to_bv 64 i /\ getr rg 24 = Z_to_bv 64 flb /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 20 = Z_to_bv 64 c
    /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096) /\ getr rg 21 = Z_to_bv 64 (6 + c) /\ getr rg 18 = Z_to_bv 64 bot
    /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 19 = Z_to_bv 64 nlog.
  (* [comment removed for export] *)
  Definition gi_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> getr regs' r = getr regs r.

  #[local] Ltac kp := intros r N10 N11 N12 N27; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

(* [comment removed for export] *)
End INNER.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gc_facts (c nfr frsz k1 : Z) : Prop :=
  nfr = (2 ^ (14 - c))%Z /\ frsz = (2 ^ (6 + c))%Z /\ (64 * 2 ^ c = frsz)%Z /\ (32 * k1 = 32768 - 2 * nfr)%Z /\ (0 <= k1 < 1024)%Z
  /\ Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c)))) 1023) = Z_to_bv 64 k1.

Lemma gc_facts_all : forall c, (0 <= c <= 10)%Z -> exists nfr frsz k1, gc_facts c nfr frsz k1.
Proof.
  intros c Hc.
  assert (E : (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10)%Z) by lia.
  exists (2 ^ (14 - c))%Z, (2 ^ (6 + c))%Z, (1024 - 2 ^ (10 - c))%Z. unfold gc_facts.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    repeat split; first [reflexivity | apply bv_eq; vm_compute; reflexivity | vm_compute; first [reflexivity | discriminate]].
Qed.

Lemma swrap32_small : forall z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLASS.
  Variable mem0 : word -> option byte.       (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables t fs sparg bot : Z.              (* [comment removed for export] *)
  Variables flag rs : Z -> Z -> Z.           (* [comment removed for export] *)
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  (* [comment removed for export] *)
  Hypothesis HCF : forall M, (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x) ->
    rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
    /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
          rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z)
    /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
          rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
          /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= bot \/ sparg <= rs c i)%Z).

  Definition gcl_inv (rg : bvmap 5 word) (c : Z) : Prop :=
    getr rg 20 = Z_to_bv 64 c /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096)
    /\ getr rg 18 = Z_to_bv 64 bot /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 2 = Z_to_bv 64 (t - 144).
  Definition gcl_keeps (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> r <> 21%bv -> r <> 24%bv -> r <> 19%bv -> r <> 20%bv -> getr regs' r = getr regs r.
  Definition out_gc (M : word -> option byte) : Prop := forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x.
  (* [comment removed for export] *)
  Definition slot32 (M M' : word -> option byte) : Prop := forall x : word, ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M' x = M x.

  #[local] Ltac hide_dj := try hide Hfs.
  #[local] Ltac kp8 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

(* [comment removed for export] *)

  (* [comment removed for export] *)
(* [comment removed for export] *)
End CLASS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WHOLE.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables t fs sparg tpv key tsd ctx th top botth g48 g50 g58 g60 g40 g35 : Z.
  Variables flag rs : Z -> Z -> Z.           (* [comment removed for export] *)
  Hypothesis Hs_def : bv_unsigned sp = t.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= sparg <= top)%Z.   (* [comment removed for export] *)
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true.
  Hypothesis Hg : (0 <= g48 < 2 ^ 64)%Z /\ (0 <= g50 < 2 ^ 64)%Z /\ (0 <= g58 < 2 ^ 64)%Z /\ (0 <= g60 < 2 ^ 64)%Z /\ (0 <= g40 < 2 ^ 64)%Z /\ (0 <= g35 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0x13f4a0 : word) 1%nat = Some [Z_to_bv 8 1] /\                                       (* [comment removed for export] *)
     rdn ASEGS M' (0x13f4a4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\                                  (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\        (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\     (* [comment removed for export] *)
     rdn ASEGS M' (0x1374c0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g48)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (0x1374c8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g50)) /\
     rdn ASEGS M' (0x1374d0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g58)) /\
     rdn ASEGS M' (0x1374d8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g60)) /\
     rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
     rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)) /\       (* [comment removed for export] *)
     (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
          rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z) /\
     (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
          rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
          /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= botth \/ sparg <= rs c i)%Z).                    (* [comment removed for export] *)

  #[local] Ltac hide_dj := try hide Hfs.
  Lemma sp_sg : sp = Z_to_bv 64 t.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  (* [comment removed for export] *)
  Definition F13 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).

(* [comment removed for export] *)
End WHOLE.
End FPX_1.
