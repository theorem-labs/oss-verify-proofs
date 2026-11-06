(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q3bI QU0c QJ4Q Qo8J Q85Z QHup QG64 QBCP QiyH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QBCP.Mq1.
Import QiyH.Mq0.
Import QWTC. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.

#[local] Ltac pclits :=
repeat match goal with
| |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
end.

#[local] Ltac stepat L F D vv tac :=
chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].

Section Walk.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.

#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

#[local] Ltac msb F D oo :=
chain_step; [reflexivity
| eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| lia | lia]
| step_simpl].
#[local] Ltac msw F D oo :=
chain_step; [reflexivity
| eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb4_c32
| lia | lia]
| step_simpl].
#[local] Ltac msd F D oo :=
chain_step; [reflexivity
| eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb8_c64
| lia | lia]
| step_simpl].

#[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).

#[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

Lemma A_exit0 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(n = 0)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_tk Fo_000 Do_000 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_exit2 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(1 <= n <= 2)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_tk Fo_014 Do_014 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_exit6 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(3 <= n <= 6)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_tk Fo_02c Do_02c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_exit8 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(7 <= n <= 8)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_ft Fo_02c Do_02c ltac:(cond).
msb Fo_030 Do_030 3%Z.
stepn Fo_034 Do_034.
msb Fo_038 Do_038 (n-4)%Z.
stepb_tk Fo_03c Do_03c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(9 <= n)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' (PC 0x40) (CF L8) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = cv /\ getr regs' 12 = Z_to_bv 64 n
/\ getr regs' 13 = at_ d n /\ getr regs' 15 = Z_to_bv 64 9 /\ getr regs' 1 = ret
/\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_ft Fo_02c Do_02c ltac:(cond).
msb Fo_030 Do_030 3%Z.
stepn Fo_034 Do_034.
msb Fo_038 Do_038 (n-4)%Z.
stepb_ft Fo_03c Do_03c ltac:(cond).
apply mst_refl.
- post.
Qed.

Section Aligned.
Variables k n1 : Z.
Hypothesis Hk : (0 <= k <= 3)%Z.
Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
Definition LD (s4 : Z) : list (Z * Z) :=
((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
:: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.

#[local] Ltac blockB :=
stepn Fo_040 Do_040;
stepn Fo_044 Do_044;
stepn Fo_048 Do_048;
stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);
stepn Fo_050 Do_050;
stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);
stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);
stepn Fo_05c Do_05c;
stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);
stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);
msw Fo_068 Do_068 k;
stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);
msw Fo_070 Do_070 (k + n1 - 4)%Z.

Lemma B_exit : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
(9 <= n)%Z -> (n1 < 9)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockB.
stepb_tk Fo_074 Do_074 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma B_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
(9 <= n)%Z -> (9 <= n1)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' (PC 0x78) (CF LB) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
/\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
/\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockB.
stepb_ft Fo_074 Do_074 ltac:(cond).
apply mst_refl.
- post.
Qed.

#[local] Ltac blockC :=
msw Fo_078 Do_078 (k + 4)%Z;
msw Fo_07c Do_07c (k + 8)%Z;
stepn Fo_080 Do_080;
msw Fo_084 Do_084 (k + n1 - 12)%Z;
msw Fo_088 Do_088 (k + n1 - 8)%Z.

Lemma C_exit : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockC.
stepb_tk Fo_08c Do_08c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma C_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (25 <= n1)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' (PC 0x90) (CF LC) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
/\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
/\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockC.
stepb_ft Fo_08c Do_08c ltac:(cond).
apply mst_refl.
- post.
Qed.

Section D.
Variable s4 : Z.
Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

#[local] Ltac blockD :=
msw Fo_090 Do_090 (k + 12)%Z;
msw Fo_094 Do_094 (k + 16)%Z;
msw Fo_098 Do_098 (k + 20)%Z;
msw Fo_09c Do_09c (k + 24)%Z;
stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);
stepn Fo_0a4 Do_0a4;
stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);
stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);
msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;
msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;
msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;
msw Fo_0bc Do_0bc (k + n1 - 16)%Z.

Lemma D_exit : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockD.
stepb_tk Fo_0c0 Do_0c0 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma D_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (28 <= n1)%Z -> (32 <= n1 - s4 - 24)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' (PC 0xc4) (CF (LD s4)) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
/\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24) /\ getr regs' 15 = Z_to_bv 64 (s4 + 24)
/\ getr regs' 1 = ret /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockD.
stepb_ft Fo_0c0 Do_0c0 ltac:(cond).
apply mst_refl.
- post.
Qed.

Lemma E_run : forall regs L,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
(9 <= n)%Z -> (28 <= n1)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
/\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
/\ getr regs' 1 = ret /\ ms_agree regs regs'.
Proof.
intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).
stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);
stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).
stepn Fo_0d4 Do_0d4.
apply mst_refl.
- post.
Qed.
End D.
End Aligned.

#[local] Ltac ms_cov_eq :=
intros i Hi; rewrite !ms_cov_cons;
match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

Lemma loop_run : forall (q : nat) regs L a r,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
(0 <= a)%Z -> (a + r <= n)%Z ->
(32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0xd8) (CF L) rom)
(mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
Proof.
induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
pose proof (u64_range d) as Hd; pclits.
-
eexists. split.
+ msd Fo_0d8 Do_0d8 a.
msd Fo_0dc Do_0dc (a + 8)%Z.
msd Fo_0e0 Do_0e0 (a + 16)%Z.
msd Fo_0e4 Do_0e4 (a + 24)%Z.
stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_ft Fo_0f0 Do_0f0 ltac:(cond).
replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
apply mst_refl.
+ post.
- eapply (runs_trans MSEGS _
(fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
(fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
/\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
/\ ms_agree regs rg)).
+ cbv beta. pclits. eexists. split.
* msd Fo_0d8 Do_0d8 a.
msd Fo_0dc Do_0dc (a + 8)%Z.
msd Fo_0e0 Do_0e0 (a + 16)%Z.
msd Fo_0e4 Do_0e4 (a + 24)%Z.
stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_tk Fo_0f0 Do_0f0 ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split.
* replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
by (apply cfill_ext; ms_cov_eq).
revert RUN. pclits. intros RUN. exact RUN.
* repeat split; try assumption. eapply ms_agree_trans; eassumption.
Qed.

Lemma ret_run : forall regs (M : word -> option byte),
getr regs 1 = ret ->
exists regs',
msteps MSEGS (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
/\ regs' = regs.
Proof.
intros regs M H1. pclits. eexists. split.
- mret. apply mst_refl.
- reflexivity.
Qed.

End Walk.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWZn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn.Mq0 QiyH.Mq4.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Lemma b1_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
(0 <= k)%Z -> (k + 1 = n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdde08 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 Hk Hkn.
eexists. split.
- mlbu F_dde54 D_dde54 k.
msb F_dde58 D_dde58 k ltac:(apply sb_val_plain).
replace (k + 1)%Z with n by lia.
stepret F_dde5c D_dde5c ret ltac:(exact H1).
apply mst_refl.
- solve_keeps.
Qed.

Lemma t2_run : forall regs (ret : word) k m,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z ->
(Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
(0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdddd0 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
-
eexists. split.
+ stepn F_dde1c D_dde1c.
stepb_ft F_dde20 D_dde20 ltac:(cond).
stepn F_dde24 D_dde24.
stepb_ft F_dde28 D_dde28 ltac:(cond).
stepret F_dde2c D_dde2c ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdde08 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
+ eexists. split.
* stepn F_dde1c D_dde1c.
stepb_ft F_dde20 D_dde20 ltac:(cond).
stepn F_dde24 D_dde24.
stepb_tk F_dde28 D_dde28 ltac:(cond).
apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
eexists. split.
+ stepn F_dde1c D_dde1c.
stepb_tk F_dde20 D_dde20 ltac:(cond).
mlbu F_dde30 D_dde30 k.
mlbu F_dde34 D_dde34 (k + 1)%Z.
stepn F_dde38 D_dde38.
stepn F_dde3c D_dde3c.
msb F_dde40 D_dde40 k ltac:(apply sb_val_plain).
msb F_dde44 D_dde44 (k + 1)%Z ltac:(apply sb_val_plain).
stepn F_dde48 D_dde48.
stepn F_dde4c D_dde4c.
stepb_tk F_dde50 D_dde50 ltac:(cond).
stepret F_dde2c D_dde2c ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdde08 : word) (MK (k + 2)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
+ eexists. split.
* stepn F_dde1c D_dde1c.
stepb_tk F_dde20 D_dde20 ltac:(cond).
mlbu F_dde30 D_dde30 k.
mlbu F_dde34 D_dde34 (k + 1)%Z.
stepn F_dde38 D_dde38.
stepn F_dde3c D_dde3c.
msb F_dde40 D_dde40 k ltac:(apply sb_val_plain).
msb F_dde44 D_dde44 (k + 1)%Z ltac:(apply sb_val_plain).
stepn F_dde48 D_dde48.
stepn F_dde4c D_dde4c.
stepb_ft F_dde50 D_dde50 ltac:(cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
| gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

Lemma al4_run : forall regs (ret : word) k m,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddb8c : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
- eexists. split.
+ stepn F_ddbd8 D_ddbd8.
stepb_tk F_ddbdc D_ddbdc ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn F_ddbd8 D_ddbd8.
stepb_ft F_ddbdc D_ddbdc ltac:(cond).
mlw F_ddbe0 D_ddbe0 k.
stepn F_ddbe4 D_ddbe4.
msw F_ddbe8 D_ddbe8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_ddbec D_ddbec.
stepn F_ddbf0 D_ddbf0.
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.

Lemma al8_run : forall regs (ret : word) k m e8,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddb6c : word) (MK k) rom)
(mkst regs' (0xddb8c : word) (MK (k + e8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
/\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
- eexists. split.
+ stepn F_ddbb8 D_ddbb8.
stepb_tk F_ddbbc D_ddbbc ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn F_ddbb8 D_ddbb8.
stepb_ft F_ddbbc D_ddbbc ltac:(cond).
mlw F_ddbc0 D_ddbc0 k.
mlw F_ddbc4 D_ddbc4 (k + 4)%Z.
msw F_ddbc8 D_ddbc8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddbcc D_ddbcc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_ddbd0 D_ddbd0.
stepn F_ddbd4 D_ddbd4.
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.

Lemma al_loop : forall (q : nat) regs (ret : word) k,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = Z_to_bv 64 15 ->
(0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddb3c : word) (MK k) rom)
(mkst regs' (0xddb6c : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
/\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
-
eexists. split.
+ mlw F_ddb88 D_ddb88 k.
mlw F_ddb8c D_ddb8c (k + 4)%Z.
mlw F_ddb90 D_ddb90 (k + 8)%Z.
mlw F_ddb94 D_ddb94 (k + 12)%Z.
stepn F_ddb98 D_ddb98.
stepn F_ddb9c D_ddb9c.
msw F_ddba0 D_ddba0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddba4 D_ddba4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddba8 D_ddba8 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddbac D_ddbac (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_ddbb0 D_ddbb0.
stepb_ft F_ddbb4 D_ddbb4 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
* unfold v_addi. unorm. f_equal. lia.
* solve_keeps.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddb3c : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
/\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* mlw F_ddb88 D_ddb88 k.
mlw F_ddb8c D_ddb8c (k + 4)%Z.
mlw F_ddb90 D_ddb90 (k + 8)%Z.
mlw F_ddb94 D_ddb94 (k + 12)%Z.
stepn F_ddb98 D_ddb98.
stepn F_ddb9c D_ddb9c.
msw F_ddba0 D_ddba0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddba4 D_ddba4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddba8 D_ddba8 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_ddbac D_ddbac (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_ddbb0 D_ddbb0.
stepb_tk F_ddbb4 D_ddbb4 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
-- unfold v_addi. unorm. f_equal. lia.
-- solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma al16_run : forall regs (ret : word) k,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddb30 : word) (MK k) rom)
(mkst regs' (0xddb6c : word) (MK (n - (n - k) mod 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
/\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
/\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 Hk.
destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
-
eexists. split.
+ stepn F_ddb7c D_ddb7c.
stepb_tk F_ddb80 D_ddb80 ltac:(cond).
replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
apply mst_refl.
+ rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
repeat split; gres; rwH; try reflexivity. solve_keeps.
- set (q := Z.to_nat ((n - k) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddb3c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
/\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* stepn F_ddb7c D_ddb7c.
stepb_ft F_ddb80 D_ddb80 ltac:(cond).
stepn F_ddb84 D_ddb84.
apply mst_refl.
* cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QBCP.Mq1.
Import QiyH.Mq3.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.

#[local] Ltac pclits :=
repeat match goal with
| |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
end.

#[local] Ltac stepat L F D vv tac :=
chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].

Section Walk.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.

#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

#[local] Ltac msb F D oo :=
chain_step; [reflexivity
| eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| lia | lia]
| step_simpl].
#[local] Ltac msw F D oo :=
chain_step; [reflexivity
| eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb4_c32
| lia | lia]
| step_simpl].
#[local] Ltac msd F D oo :=
chain_step; [reflexivity
| eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
[exact F | reflexivity | exact D
| gres; rwH; rewrite ?at_addi; reflexivity
| imm_norm; lia
| gres; rwH; reflexivity
| apply wleb8_c64
| lia | lia]
| step_simpl].

#[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).

#[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

Lemma A_exit0 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(n = 0)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF []) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_tk Fo_000 Do_000 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_exit2 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(1 <= n <= 2)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L2) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_tk Fo_014 Do_014 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_exit6 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(3 <= n <= 6)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L6) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_tk Fo_02c Do_02c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_exit8 : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(7 <= n <= 8)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret (CF L8) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_ft Fo_02c Do_02c ltac:(cond).
msb Fo_030 Do_030 3%Z.
stepn Fo_034 Do_034.
msb Fo_038 Do_038 (n-4)%Z.
stepb_tk Fo_03c Do_03c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma A_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
(9 <= n)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' (PC 0x40) (CF L8) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = cv /\ getr regs' 12 = Z_to_bv 64 n
/\ getr regs' 13 = at_ d n /\ getr regs' 15 = Z_to_bv 64 9 /\ getr regs' 1 = ret
/\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepb_ft Fo_000 Do_000 ltac:(cond).
msb Fo_004 Do_004 0%Z.
stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepn Fo_00c Do_00c.
msb Fo_010 Do_010 (n-1)%Z.
stepb_ft Fo_014 Do_014 ltac:(cond).
msb Fo_018 Do_018 1%Z.
msb Fo_01c Do_01c 2%Z.
stepn Fo_020 Do_020.
msb Fo_024 Do_024 (n-3)%Z.
msb Fo_028 Do_028 (n-2)%Z.
stepb_ft Fo_02c Do_02c ltac:(cond).
msb Fo_030 Do_030 3%Z.
stepn Fo_034 Do_034.
msb Fo_038 Do_038 (n-4)%Z.
stepb_ft Fo_03c Do_03c ltac:(cond).
apply mst_refl.
- post.
Qed.

Section Aligned.
Variables k n1 : Z.
Hypothesis Hk : (0 <= k <= 3)%Z.
Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
Definition LD (s4 : Z) : list (Z * Z) :=
((k+n1-16,4) :: (k+n1-20,4) :: (k+n1-24,4) :: (k+n1-28,4)
:: (k+24,4) :: (k+20,4) :: (k+16,4) :: (k+12,4) :: LC)%Z.

#[local] Ltac blockB :=
stepn Fo_040 Do_040;
stepn Fo_044 Do_044;
stepn Fo_048 Do_048;
stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);
stepn Fo_050 Do_050;
stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);
stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);
stepn Fo_05c Do_05c;
stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);
stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);
msw Fo_068 Do_068 k;
stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);
msw Fo_070 Do_070 (k + n1 - 4)%Z.

Lemma B_exit : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
(9 <= n)%Z -> (n1 < 9)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' ret (CF LB) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockB.
stepb_tk Fo_074 Do_074 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma B_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n ->
getr regs 13 = at_ d n -> getr regs 15 = Z_to_bv 64 9 -> getr regs 1 = ret ->
(9 <= n)%Z -> (9 <= n1)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x40) (CF L8) rom) (mkst regs' (PC 0x78) (CF LB) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
/\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
/\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockB.
stepb_ft Fo_074 Do_074 ltac:(cond).
apply mst_refl.
- post.
Qed.

#[local] Ltac blockC :=
msw Fo_078 Do_078 (k + 4)%Z;
msw Fo_07c Do_07c (k + 8)%Z;
stepn Fo_080 Do_080;
msw Fo_084 Do_084 (k + n1 - 12)%Z;
msw Fo_088 Do_088 (k + n1 - 8)%Z.

Lemma C_exit : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (12 <= n1)%Z -> (n1 < 25)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' ret (CF LC) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockC.
stepb_tk Fo_08c Do_08c ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma C_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (25 <= n1)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x78) (CF LB) rom) (mkst regs' (PC 0x90) (CF LC) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
/\ getr regs' 13 = at_ d (k + n1) /\ getr regs' 14 = Z_to_bv 64 n1 /\ getr regs' 1 = ret
/\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockC.
stepb_ft Fo_08c Do_08c ltac:(cond).
apply mst_refl.
- post.
Qed.

Section D.
Variable s4 : Z.
Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

#[local] Ltac blockD :=
msw Fo_090 Do_090 (k + 12)%Z;
msw Fo_094 Do_094 (k + 16)%Z;
msw Fo_098 Do_098 (k + 20)%Z;
msw Fo_09c Do_09c (k + 24)%Z;
stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);
stepn Fo_0a4 Do_0a4;
stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);
stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);
msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;
msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;
msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;
msw Fo_0bc Do_0bc (k + n1 - 16)%Z.

Lemma D_exit : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (28 <= n1)%Z -> (n1 - s4 - 24 < 32)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' ret (CF (LD s4)) rom)
/\ getr regs' 10 = at_ d 0 /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockD.
stepb_tk Fo_0c0 Do_0c0 ltac:(cond).
mret.
apply mst_refl.
- post.
Qed.

Lemma D_cont : forall regs,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 13 = at_ d (k + n1) -> getr regs 14 = Z_to_bv 64 n1 -> getr regs 1 = ret ->
(9 <= n)%Z -> (28 <= n1)%Z -> (32 <= n1 - s4 - 24)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0x90) (CF LC) rom) (mkst regs' (PC 0xc4) (CF (LD s4)) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d k /\ getr regs' 12 = c32 cv
/\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24) /\ getr regs' 15 = Z_to_bv 64 (s4 + 24)
/\ getr regs' 1 = ret /\ ms_agree regs regs'.
Proof.
intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- blockD.
stepb_ft Fo_0c0 Do_0c0 ltac:(cond).
apply mst_refl.
- post.
Qed.

Lemma E_run : forall regs L,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d k -> getr regs 12 = c32 cv ->
getr regs 14 = Z_to_bv 64 (n1 - s4 - 24) -> getr regs 15 = Z_to_bv 64 (s4 + 24) -> getr regs 1 = ret ->
(9 <= n)%Z -> (28 <= n1)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0xc4) (CF L) rom) (mkst regs' (PC 0xd8) (CF L) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 11 = at_ d (k + s4 + 24) /\ getr regs' 12 = c64 cv
/\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 (n1 - s4 - 24)
/\ getr regs' 1 = ret /\ ms_agree regs regs'.
Proof.
intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
eexists. split.
- stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).
stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);
stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).
stepn Fo_0d4 Do_0d4.
apply mst_refl.
- post.
Qed.
End D.
End Aligned.

#[local] Ltac ms_cov_eq :=
intros i Hi; rewrite !ms_cov_cons;
match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

Lemma loop_run : forall (q : nat) regs L a r,
getr regs 10 = at_ d 0 -> getr regs 11 = at_ d a -> getr regs 12 = c64 cv ->
getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r -> getr regs 1 = ret ->
(0 <= a)%Z -> (a + r <= n)%Z ->
(32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
exists regs',
msteps MSEGS (mkst regs (PC 0xd8) (CF L) rom)
(mkst regs' (PC 0xf4) (CF ((a, 32 * (Z.of_nat q + 1))%Z :: L)) rom)
/\ getr regs' 10 = at_ d 0 /\ getr regs' 1 = ret /\ ms_agree regs regs'.
Proof.
induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
pose proof (u64_range d) as Hd; pclits.
-
eexists. split.
+ msd Fo_0d8 Do_0d8 a.
msd Fo_0dc Do_0dc (a + 8)%Z.
msd Fo_0e0 Do_0e0 (a + 16)%Z.
msd Fo_0e4 Do_0e4 (a + 24)%Z.
stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_ft Fo_0f0 Do_0f0 ltac:(cond).
replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
apply mst_refl.
+ post.
- eapply (runs_trans MSEGS _
(fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
(fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
/\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
/\ ms_agree regs rg)).
+ cbv beta. pclits. eexists. split.
* msd Fo_0d8 Do_0d8 a.
msd Fo_0dc Do_0dc (a + 8)%Z.
msd Fo_0e0 Do_0e0 (a + 16)%Z.
msd Fo_0e4 Do_0e4 (a + 24)%Z.
stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
stepb_tk Fo_0f0 Do_0f0 ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
exists r2. split.
* replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
by (apply cfill_ext; ms_cov_eq).
revert RUN. pclits. intros RUN. exact RUN.
* repeat split; try assumption. eapply ms_agree_trans; eassumption.
Qed.

Lemma ret_run : forall regs (M : word -> option byte),
getr regs 1 = ret ->
exists regs',
msteps MSEGS (mkst regs (PC 0xf4) M rom) (mkst regs' ret M rom)
/\ regs' = regs.
Proof.
intros regs M H1. pclits. eexists. split.
- mret. apply mst_refl.
- reflexivity.
Qed.

End Walk.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJ4Q.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWZn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWZn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiyH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiyH.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Lemma b1_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
(0 <= k)%Z -> (k + 1 = n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb744 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 Hk Hkn.
eexists. split.
- mlbu F_db768 D_db768 k.
msb F_db76c D_db76c k ltac:(apply sb_val_plain).
replace (k + 1)%Z with n by lia.
stepret F_db770 D_db770 ret ltac:(exact H1).
apply mst_refl.
- solve_keeps.
Qed.

Lemma t2_run : forall regs (ret : word) k m,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z ->
(Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
(0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb70c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
-
eexists. split.
+ stepn F_db730 D_db730.
stepb_ft F_db734 D_db734 ltac:(cond).
stepn F_db738 D_db738.
stepb_ft F_db73c D_db73c ltac:(cond).
stepret F_db740 D_db740 ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb744 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
+ eexists. split.
* stepn F_db730 D_db730.
stepb_ft F_db734 D_db734 ltac:(cond).
stepn F_db738 D_db738.
stepb_tk F_db73c D_db73c ltac:(cond).
apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
eexists. split.
+ stepn F_db730 D_db730.
stepb_tk F_db734 D_db734 ltac:(cond).
mlbu F_db744 D_db744 k.
mlbu F_db748 D_db748 (k + 1)%Z.
stepn F_db74c D_db74c.
stepn F_db750 D_db750.
msb F_db754 D_db754 k ltac:(apply sb_val_plain).
msb F_db758 D_db758 (k + 1)%Z ltac:(apply sb_val_plain).
stepn F_db75c D_db75c.
stepn F_db760 D_db760.
stepb_tk F_db764 D_db764 ltac:(cond).
stepret F_db740 D_db740 ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb744 : word) (MK (k + 2)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
+ eexists. split.
* stepn F_db730 D_db730.
stepb_tk F_db734 D_db734 ltac:(cond).
mlbu F_db744 D_db744 k.
mlbu F_db748 D_db748 (k + 1)%Z.
stepn F_db74c D_db74c.
stepn F_db750 D_db750.
msb F_db754 D_db754 k ltac:(apply sb_val_plain).
msb F_db758 D_db758 (k + 1)%Z ltac:(apply sb_val_plain).
stepn F_db75c D_db75c.
stepn F_db760 D_db760.
stepb_ft F_db764 D_db764 ltac:(cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
| gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

Lemma al4_run : forall regs (ret : word) k m,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb4c8 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
- eexists. split.
+ stepn F_db4ec D_db4ec.
stepb_tk F_db4f0 D_db4f0 ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn F_db4ec D_db4ec.
stepb_ft F_db4f0 D_db4f0 ltac:(cond).
mlw F_db4f4 D_db4f4 k.
stepn F_db4f8 D_db4f8.
msw F_db4fc D_db4fc k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_db500 D_db500.
stepn F_db504 D_db504.
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.

Lemma al8_run : forall regs (ret : word) k m e8,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb4a8 : word) (MK k) rom)
(mkst regs' (0xdb4c8 : word) (MK (k + e8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
/\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
- eexists. split.
+ stepn F_db4cc D_db4cc.
stepb_tk F_db4d0 D_db4d0 ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn F_db4cc D_db4cc.
stepb_ft F_db4d0 D_db4d0 ltac:(cond).
mlw F_db4d4 D_db4d4 k.
mlw F_db4d8 D_db4d8 (k + 4)%Z.
msw F_db4dc D_db4dc k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4e0 D_db4e0 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_db4e4 D_db4e4.
stepn F_db4e8 D_db4e8.
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.

Lemma al_loop : forall (q : nat) regs (ret : word) k,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = Z_to_bv 64 15 ->
(0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb478 : word) (MK k) rom)
(mkst regs' (0xdb4a8 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
/\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
-
eexists. split.
+ mlw F_db49c D_db49c k.
mlw F_db4a0 D_db4a0 (k + 4)%Z.
mlw F_db4a4 D_db4a4 (k + 8)%Z.
mlw F_db4a8 D_db4a8 (k + 12)%Z.
stepn F_db4ac D_db4ac.
stepn F_db4b0 D_db4b0.
msw F_db4b4 D_db4b4 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4b8 D_db4b8 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4bc D_db4bc (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4c0 D_db4c0 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_db4c4 D_db4c4.
stepb_ft F_db4c8 D_db4c8 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
* unfold v_addi. unorm. f_equal. lia.
* solve_keeps.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb478 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
/\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* mlw F_db49c D_db49c k.
mlw F_db4a0 D_db4a0 (k + 4)%Z.
mlw F_db4a4 D_db4a4 (k + 8)%Z.
mlw F_db4a8 D_db4a8 (k + 12)%Z.
stepn F_db4ac D_db4ac.
stepn F_db4b0 D_db4b0.
msw F_db4b4 D_db4b4 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4b8 D_db4b8 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4bc D_db4bc (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_db4c0 D_db4c0 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_db4c4 D_db4c4.
stepb_tk F_db4c8 D_db4c8 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
-- unfold v_addi. unorm. f_equal. lia.
-- solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma al16_run : forall regs (ret : word) k,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb46c : word) (MK k) rom)
(mkst regs' (0xdb4a8 : word) (MK (n - (n - k) mod 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
/\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
/\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 Hk.
destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
-
eexists. split.
+ stepn F_db490 D_db490.
stepb_tk F_db494 D_db494 ltac:(cond).
replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
apply mst_refl.
+ rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
repeat split; gres; rwH; try reflexivity. solve_keeps.
- set (q := Z.to_nat ((n - k) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb478 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
/\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* stepn F_db490 D_db490.
stepb_ft F_db494 D_db494 ltac:(cond).
stepn F_db498 D_db498.
apply mst_refl.
* cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
