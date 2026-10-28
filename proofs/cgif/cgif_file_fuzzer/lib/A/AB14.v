(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE08 YE21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition imemcpy_words : list (bv 32) :=
[W_e2430; W_e2434; W_e2438; W_e243c; W_e2440; W_e2444; W_e2448; W_e244c; W_e2450].
Definition imemcpy_clob : list reg := [11; 12; 13; 14].
Section b.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 imemcpy_words.
Hypothesis HOK : cpyH segs mem0 dst src n bs.
#[local] Abbreviation MK := (memk mem0 dst bs).
#[local] Abbreviation B := (b_ bs).
#[local] Abbreviation CL := (fun r => In r imemcpy_clob).
Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & _).
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vn.
Ltac msb F D kk :=
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | apply sb_val_b | lia | lia]
| step_simpl]; vn.
Lemma imemcpy_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
(0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 12) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
-
eexists. split.
+ mlbu C12 D_e243c k.
msb C16 D_e2440 k.
an C20 D_e2444.
an C24 D_e2448.
ab_ft C28 D_e244c ltac:(condz).
aret C32 D_e2450 ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemcpy_clob. solve_regs_agree.
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C12 D_e243c k.
msb C16 D_e2440 k.
an C20 D_e2444.
an C24 D_e2448.
ab_tk C28 D_e244c ltac:(condz).
apply mst_refl.
* post. unfold imemcpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Theorem imemcpy_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
destruct (Z.eq_dec n 0) as [Hz|Hnz].
-
eexists. split.
+ ab_tk C0 D_e2430 ltac:(condz).
aret C32 D_e2450 ret.
rewrite Hz. apply mst_refl.
+ apply regs_agree_refl.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C0 D_e2430 ltac:(condz).
av C4 D_e2434 (at_ dst n) ltac:(apply v_add_at; lia).
an C8 D_e2438.
apply mst_refl.
* post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End b.
End a.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_imemcpy_entry : word := 0x638ec.
Lemma tfib_imemcpy_code :
code_at Asan.M.loaded_segments tfib_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.
Theorem tfib_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
cpyH Asan.M.loaded_segments mem0 dst src n bs ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps Asan.M.loaded_segments
(mkst regs tfib_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
intros mem0 dst src n bs rom regs ret HOK.
rewrite <- (at_0 tfib_imemcpy_entry).
apply (imemcpy_run _ _ mem0 dst src n bs rom tfib_imemcpy_code HOK).
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
