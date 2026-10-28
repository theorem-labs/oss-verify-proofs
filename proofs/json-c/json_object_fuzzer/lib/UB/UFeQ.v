(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QsV0 QBxa QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4.
Export QBxa.Mq7 QSpR.Mq2.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma ref_wseg_28 : wseg_ok RSEGS (0x66000 : word) 208896%nat = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma store_ok_data : forall m (a : word) n,
(0x66000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x99000)%Z ->
store_ok RSEGS m a n = true.
Proof.
intros m a n Hlo Hhi.
eapply (store_ok_window RSEGS m (0x66000 : word) a 208896%nat n 0x66000 0x99000);
[reflexivity | reflexivity | lia | exact ref_wseg_28 | exact Hlo | exact Hhi].
Qed.
End FPGEN1.

Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

Ltac sok_frame SOK :=
store_ok_peel;
eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
/\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
/\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
/\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

Definition stdio_globals (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0x97e93) 1%nat = Some [Z_to_bv 8 0]
/\ rdn RSEGS mem (Z_to_bv 64 0x98338) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0x98328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0x66f10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66e28))
/\ rdn RSEGS mem (Z_to_bv 64 0x66e20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66d38)).

Definition atx_state (armed : bool) (mem : word -> option byte) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0x97c4c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
/\ if armed then
rdn RSEGS mem (Z_to_bv 64 0x97c58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x97c60))
/\ rdn RSEGS mem (Z_to_bv 64 0x97c50) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
/\ rdn RSEGS mem (Z_to_bv 64 0x97c60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
/\ rdn RSEGS mem (Z_to_bv 64 0x97c68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50e18))
/\ rdn RSEGS mem (Z_to_bv 64 0x97d68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20fac))
/\ rdn RSEGS mem (Z_to_bv 64 0x76f84) 1%nat = Some [Z_to_bv 8 0]
else rdn RSEGS mem (Z_to_bv 64 0x97c58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

#[using="Type"] Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
(bv_unsigned a + 4 <= 2^64)%Z ->
rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
intros segs m a v Hnw.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.
End FPGEN2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN UqHD UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq3 QRjH.Mq4 Qn1e.Mq1 QBxa.Mq3.
Import UeDN UqHD.Mq0 UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MIS.
Context {fF : FPF} {fC : FPC}.
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

Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac sbp := apply sb_val_plain.

#[using="HOK"] Lemma b4_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 4 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f7cc : word) (MK k) rom) (mkst regs' (0x5f7f8 : word) (MK (k + 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu F_5d9f0 D_5d9f0 k. mlbu F_5d9f4 D_5d9f4 (k+1)%Z. mlbu F_5d9f8 D_5d9f8 (k+2)%Z. mlbu F_5d9fc D_5d9fc (k+3)%Z.
stepn F_5da00 D_5da00.
stepn F_5da04 D_5da04.
msb F_5da08 D_5da08 k ltac:(sbp). msb F_5da0c D_5da0c (k+1)%Z ltac:(sbp).
msb F_5da10 D_5da10 (k+2)%Z ltac:(sbp). msb F_5da14 D_5da14 (k+3)%Z ltac:(sbp).
stepn F_5da18 D_5da18.
mk_eq. apply mst_refl.
- post.
Qed.

#[using="HOK"] Lemma b8_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 8 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f778 : word) (MK k) rom) (mkst regs' (0x5f7c4 : word) (MK (k + 8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu F_5d99c D_5d99c k. mlbu F_5d9a0 D_5d9a0 (k+1)%Z. mlbu F_5d9a4 D_5d9a4 (k+2)%Z. mlbu F_5d9a8 D_5d9a8 (k+3)%Z.
mlbu F_5d9ac D_5d9ac (k+4)%Z. mlbu F_5d9b0 D_5d9b0 (k+5)%Z. mlbu F_5d9b4 D_5d9b4 (k+6)%Z. mlbu F_5d9b8 D_5d9b8 (k+7)%Z.
stepn F_5d9bc D_5d9bc.
msb F_5d9c0 D_5d9c0 k ltac:(sbp). msb F_5d9c4 D_5d9c4 (k+1)%Z ltac:(sbp).
msb F_5d9c8 D_5d9c8 (k+2)%Z ltac:(sbp). msb F_5d9cc D_5d9cc (k+3)%Z ltac:(sbp).
stepn F_5d9d0 D_5d9d0.
msb F_5d9d4 D_5d9d4 (k+4)%Z ltac:(sbp). msb F_5d9d8 D_5d9d8 (k+5)%Z ltac:(sbp).
msb F_5d9dc D_5d9dc (k+6)%Z ltac:(sbp). msb F_5d9e0 D_5d9e0 (k+7)%Z ltac:(sbp).
stepn F_5d9e4 D_5d9e4.
mk_eq. apply mst_refl.
- post.
Qed.

#[using="HOK"] Lemma b16_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 16 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f6e4 : word) (MK k) rom) (mkst regs' (0x5f770 : word) (MK (k + 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu F_5d908 D_5d908 k. mlbu F_5d90c D_5d90c (k+1)%Z. mlbu F_5d910 D_5d910 (k+2)%Z. mlbu F_5d914 D_5d914 (k+3)%Z.
mlbu F_5d918 D_5d918 (k+4)%Z. mlbu F_5d91c D_5d91c (k+5)%Z. mlbu F_5d920 D_5d920 (k+6)%Z. mlbu F_5d924 D_5d924 (k+7)%Z.
msb F_5d928 D_5d928 k ltac:(sbp). msb F_5d92c D_5d92c (k+1)%Z ltac:(sbp).
msb F_5d930 D_5d930 (k+2)%Z ltac:(sbp). msb F_5d934 D_5d934 (k+3)%Z ltac:(sbp).
mlbu F_5d938 D_5d938 (k+8)%Z. mlbu F_5d93c D_5d93c (k+9)%Z. mlbu F_5d940 D_5d940 (k+10)%Z. mlbu F_5d944 D_5d944 (k+11)%Z.
msb F_5d948 D_5d948 (k+4)%Z ltac:(sbp). msb F_5d94c D_5d94c (k+5)%Z ltac:(sbp).
msb F_5d950 D_5d950 (k+6)%Z ltac:(sbp). msb F_5d954 D_5d954 (k+7)%Z ltac:(sbp).
mlbu F_5d958 D_5d958 (k+12)%Z. mlbu F_5d95c D_5d95c (k+13)%Z. mlbu F_5d960 D_5d960 (k+14)%Z. mlbu F_5d964 D_5d964 (k+15)%Z.
stepn F_5d968 D_5d968.
msb F_5d96c D_5d96c (k+8)%Z ltac:(sbp). msb F_5d970 D_5d970 (k+9)%Z ltac:(sbp).
msb F_5d974 D_5d974 (k+10)%Z ltac:(sbp). msb F_5d978 D_5d978 (k+11)%Z ltac:(sbp).
stepn F_5d97c D_5d97c.
msb F_5d980 D_5d980 (k+12)%Z ltac:(sbp). msb F_5d984 D_5d984 (k+13)%Z ltac:(sbp).
msb F_5d988 D_5d988 (k+14)%Z ltac:(sbp). msb F_5d98c D_5d98c (k+15)%Z ltac:(sbp).
stepn F_5d990 D_5d990.
mk_eq. apply mst_refl.
- post.
Qed.

#[using="HOK"] Lemma t4_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f4a0 : word) (MK k) rom) (mkst regs' (0x5f7f8 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_5d6c4 D_5d6c4.
stepb_ft F_5d6c8 D_5d6c8 ltac:(cond).
stepn F_5d6cc D_5d6cc.
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f7cc : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6c4 D_5d6c4.
stepb_tk F_5d6c8 D_5d6c8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma b8_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f7c4 : word) (MK k) rom) (mkst regs' (0x5f7f8 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_5d9e8 D_5d9e8.
stepb_tk F_5d9ec D_5d9ec ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f7cc : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d9e8 D_5d9e8.
stepb_ft F_5d9ec D_5d9ec ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma t8_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f498 : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f4a0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6bc D_5d6bc.
stepb_ft F_5d6c0 D_5d6c0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f778 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6bc D_5d6bc.
stepb_tk F_5d6c0 D_5d6c0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f7c4 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma b16_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f770 : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f4a0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d994 D_5d994.
stepb_tk F_5d998 D_5d998 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f778 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d994 D_5d994.
stepb_ft F_5d998 D_5d998 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f7c4 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma t16_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 32)%Z -> (0 <= k)%Z ->
(k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f490 : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f498 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6b4 D_5d6b4.
stepb_ft F_5d6b8 D_5d6b8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f6e4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6b4 D_5d6b4.
stepb_tk F_5d6b8 D_5d6b8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f770 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QSpR.Mq3.
Import UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition memset304_ws : list (Z * nat) :=
[(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

#[using="Type"] Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

#[using="Type"] Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
getr regs 1 = ret -> ret_ok ret ->
getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
(bv_unsigned d mod 8 = 0)%Z ->
(bv_unsigned d + 304 < 2^64)%Z ->
store_ok SEGS mem d 304 = true ->
exists regs' mem',
msteps SEGS (mkst regs (0x5f9b8 : word) mem rom) (mkst regs' ret mem' rom)
/\ mem' = wbytes mem d (zeros 304)
/\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
pose proof (u64_range d) as Hdr.
assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
{ rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
eexists. eexists. split; [|split].
-
stepb_ft F_5dbdc D_5dbdc ltac:(pin; cond_compute).
stw F_5dbe0 D_5dbe0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sv F_5dbe4 D_5dbe4 (Z_to_bv 64 (bv_unsigned d + 304)).
sn F_5dbe8 D_5dbe8.
stw F_5dbec D_5dbec (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft F_5dbf0 D_5dbf0 ltac:(pin; cond_compute).
stw F_5dbf4 D_5dbf4 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dbf8 D_5dbf8 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dbfc D_5dbfc.
stw F_5dc00 D_5dc00 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc04 D_5dc04 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft F_5dc08 D_5dc08 ltac:(pin; cond_compute).
stw F_5dc0c D_5dc0c (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dc10 D_5dc10.
stw F_5dc14 D_5dc14 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft F_5dc18 D_5dc18 ltac:(pin; cond_compute).
sn F_5dc1c D_5dc1c.
sn F_5dc20 D_5dc20.
sn F_5dc24 D_5dc24.
stepiv F_5dc28 D_5dc28 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
sn F_5dc2c D_5dc2c.
sn F_5dc30 D_5dc30.
sv F_5dc34 D_5dc34 (d).
sn F_5dc38 D_5dc38.
sn F_5dc3c D_5dc3c.
sn F_5dc40 D_5dc40.
stw F_5dc44 D_5dc44 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sv F_5dc48 D_5dc48 (Z_to_bv 64 (bv_unsigned d + 304)).
stw F_5dc4c D_5dc4c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft F_5dc50 D_5dc50 ltac:(pin; cond_compute).
stw F_5dc54 D_5dc54 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc58 D_5dc58 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dc5c D_5dc5c.
stw F_5dc60 D_5dc60 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc64 D_5dc64 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft F_5dc68 D_5dc68 ltac:(pin; cond_compute).
stw F_5dc6c D_5dc6c (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc70 D_5dc70 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc74 D_5dc74 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc78 D_5dc78 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepiv F_5dc7c D_5dc7c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
sn F_5dc80 D_5dc80.
sn F_5dc84 D_5dc84.
sn F_5dc88 D_5dc88.
stw F_5dc8c D_5dc8c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc90 D_5dc90 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc94 D_5dc94 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dc98 D_5dc98 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stepb_ft F_5dc9c D_5dc9c ltac:(pin; cond_compute).
sn F_5dca0 D_5dca0.
sv F_5dca4 D_5dca4 (Z_to_bv 64 (bv_unsigned d + 24)).
sn F_5dca8 D_5dca8.
sn F_5dcac D_5dcac.
sn F_5dcb0 D_5dcb0.
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 56)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 88)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 120)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 152)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 184)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 216)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 248)).
stepb_tk F_5dccc D_5dccc ltac:(pin; cond_compute).
stw F_5dcb4 D_5dcb4 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcb8 D_5dcb8 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcbc D_5dcbc (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
stw F_5dcc0 D_5dcc0 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
sn F_5dcc4 D_5dcc4.
sv F_5dcc8 D_5dcc8 (Z_to_bv 64 (bv_unsigned d + 280)).
stepb_ft F_5dccc D_5dccc ltac:(pin; cond_compute).
stepret F_5dcd0 D_5dcd0 ret ltac:(pin; reflexivity).
apply mst_refl.
- rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
reflexivity.
- unfold memset_clob. solve_regs_agree.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uhzw U1SW ULxO U5hz UoL3 UuT1 USPu UU2A U8LG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QSpR.Mq3 QRjH.Mq0 QBxa.Mq6.
Import Uhzw U1SW ULxO U5hz UoL3 UuT1 USPu UU2A U8LG UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition regs_init (sp0 : word) : bvmap 5 word :=
regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.
End FPGEN1.

Section P1.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av ev : list (list byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

Local Notation mem0 := (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd) (only parsing).
Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd)) (only parsing).

Let argc : word := argcN av.
Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
Let envp : word := envp_ptr sp0 av.
Let pn : word := cat_argv_ptr sp0 av ev 0.

#[using="Hva"] Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
Proof. exact (u_argcN av Hva). Qed.

#[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Definition J1 (J : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes
(wbytes (wbytes (wbytes (wbytes J
(Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x5083c)))
(Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x20b84)).

#[using="Hva Hve Hlo Hhi Hal"] Lemma p1_run : forall rom (J : word -> option byte),
wfJ sp0 J ->
exists regs',
msteps SEGS (mkst (regs_init sp0) (0x20a38 : word) (CM J (fun _ => None)) rom)
(mkst regs' (0x5f9b8 : word) (CM (J1 J) (fun _ => None)) rom)
/\ getr regs' 1 = Z_to_bv 64 0x505bc
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
/\ getr regs' 3 = Z_to_bv 64 0x10800
/\ getr regs' 4 = Z_to_bv 64 0
/\ getr regs' 8 = pn
/\ getr regs' 9 = envp
/\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 304
/\ getr regs' 18 = Z_to_bv 64 0x20b84
/\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
Proof.
intros rom J HJ.
pose proof len_av as Hlen. pose proof u_argc as Hargc.
eexists. split.
- unfold regs_init.
stepn F_20814 D_20814.
stepn F_20818 D_20818.
stepn F_2081c D_2081c.
stepn F_20820 D_20820.
stepn F_20824 D_20824.
stepiv F_20828 D_20828 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).

stepn F_2082c D_2082c.

chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
[ exact F_20830 | reflexivity | exact D_20830
| addr_norm; rewrite rdn_cmem_above by region_side;
apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
exact (read_argc_w SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hhi)
| apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
| step_simpl]; vnorm.
rewrite (v_lw_small argc) by (rewrite Hargc; lia).
stepn F_20834 D_20834.
stepn F_20838 D_20838.
stepn F_2083c D_2083c.

chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x20b84);
[exact F_20840 | reflexivity | exact D_20840 | rd_img img_63ce0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x5058c);
[exact F_20844 | reflexivity | exact D_20844 | rd_img img_63ce8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x50e1c);
[exact F_20848 | reflexivity | exact D_20848 | rd_img img_63cf0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
sv F_2084c D_2084c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
stepn F_20850 D_20850.
stepn F_20854 D_20854.
stepn F_20858 D_20858.

sv F_4ea20 D_4ea20 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stw F_4ea24 D_4ea24 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea28 D_4ea28 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea2c D_4ea2c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea30 D_4ea30 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stepn F_4ea34 D_4ea34.
stepn F_4ea38 D_4ea38.
stepn F_4ea3c D_4ea3c.

chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
[ exact F_4ea40 | reflexivity | exact D_4ea40
| addr_norm; rewrite rdn_cmem_above by region_side;
replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
by (rewrite word_add_nat; f_equal; lia);
exact (read_argv_ptr_w SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hlo Hhi 0 ltac:(lia))
| apply bytes_le_to_Z_8 ]
| step_simpl]; vnorm.
stepiv F_4ea44 D_4ea44 (Z_to_bv 64 (8 * Z.of_nat (length av)))
ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).

stepiv F_4ea48 D_4ea48 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.

stepiv F_4ea4c D_4ea4c envp
ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).

stepn F_4ea50 D_4ea50.

sv F_4e7a8 D_4e7a8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stw F_4e7ac D_4e7ac (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x5083c) ltac:(ok_win HJ).
stw F_4e7b0 D_4e7b0 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw F_4e7b4 D_4e7b4 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
stw F_4e7b8 D_4e7b8 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x20b84) ltac:(ok_win HJ).
stepn F_4e7bc D_4e7bc.
stepn F_4e7c0 D_4e7c0.
sv F_4e7c4 D_4e7c4 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
stepn F_4e7c8 D_4e7c8.
stepn F_4e7cc D_4e7cc.
stepn F_4e7d0 D_4e7d0.
apply mst_refl.
- repeat split; gres; try reflexivity.
intros r Hr. cbn [In] in Hr.
repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
[ .. | contradiction]; gres; apply getr_empty.
Qed.
End P1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq3 QRjH.Mq4 Qn1e.Mq1 QBxa.Mq1 QBxa.Mq3.
Import UeDN UqHD UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SNL.
Context {fF : FPF} {fC : FPC}.
Variable mem : word -> option byte.
Variables s sp : word.
Variable buf : list byte.
Variables K n : Z.
Variable rom : word -> option byte.
Hypothesis HOK : mchrH mem s buf K n.
Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
Hypothesis Hspr : (0x13428 <= bv_unsigned sp - 32)%Z.
Hypothesis Hdisj : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32
\/ bv_unsigned sp <= bv_unsigned s)%Z.

#[local] Notation usp := (bv_unsigned sp).
#[local] Notation W8 v := (word_to_le_bytes 8 v).

Definition mem1 (ra s0 s1 : word) : word -> option byte :=
wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
(Z_to_bv 64 (usp - 24)) (W8 s1).

#[using="Type"] Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
Proof. intros v. apply length_N_to_le_bytes. Qed.

#[using="Hspr"] Lemma mem1_out : forall ra s0 s1 (a : word),
(bv_unsigned a < usp - 24 \/ usp <= bv_unsigned a)%Z -> mem1 ra s0 s1 a = mem a.
Proof.
clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
Qed.

#[using="HOK HsK Hspr Hdisj"] Lemma HOK1 : forall ra s0 s1, mchrH (mem1 ra s0 s1) s buf K n.
Proof.
intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
- rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
- intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
Qed.

#[using="Hspr"] Lemma frame1 : forall ra s0 s1, frame_mod mem (mem1 ra s0 s1) [(Z_to_bv 64 (usp - 32), 32%Z)].
Proof.
clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
- intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
- unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
Qed.

#[using="Hspr"] Lemma rd_ra : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 ra).
Proof.
clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
apply rdn_wbytes_hit8. u_norm. lia.
Qed.
#[using="Hspr"] Lemma rd_s0 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s0).
Proof.
clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
apply rdn_wbytes_hit8. u_norm. lia.
Qed.
#[using="Hspr"] Lemma rd_s1 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s1).
Proof.
clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
Qed.

Ltac okstk :=
repeat (eapply store_ok_mono; [apply wbytes_grows|]);
eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
[u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

Ltac kept_cs := cbv [callee_saved In]; tauto.

Ltac msd F D aa :=
chain_step; [reflexivity
| eapply step_sd_at with (a := aa);
[exact F | reflexivity | exact D
| gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
| gres; rwH; reflexivity
| okstk ]
| step_simpl]; vnorm.

Ltac mld8 F D vv RD :=
chain_step; [reflexivity
| eapply step_ld with (v := vv);
[exact F | reflexivity | exact D
| gres; imm_norm; rwH;
lazymatch goal with |- rdn _ _ ?a _ = _ =>
lazymatch type of RD with rdn _ _ ?c _ = _ =>
replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
exact RD
| apply bytes_le_to_Z_8 ]
| step_simpl]; vnorm.

#[using="buf HOK HsK Hstk Hspr Hdisj"] Lemma strnlen_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
exists regs',
msteps RSEGS (mkst regs (0x5fe24 : word) mem rom)
(mkst regs' ret (mem1 ret (getr regs 8) (getr regs 9)) rom)
/\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 K.
Proof.
intros regs ret Hret H1 H2 H10 H11.
pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
pose proof (KL _ _ _ _ _ HOK) as HKL.
destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
set (s0 := getr regs 8). set (s1 := getr regs 9).

eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f33c : word) (mem1 ret s0 s1) rom)
(fun r => getr r 1 = (0x5fe48 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
/\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
/\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
/\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
{ eexists. split.
- stepiv F_5e048 D_5e048 (Z_to_bv 64 (usp - 32))
ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).
msd F_5e04c D_5e04c (Z_to_bv 64 (usp - 8)).
msd F_5e050 D_5e050 (Z_to_bv 64 (usp - 16)).
msd F_5e054 D_5e054 (Z_to_bv 64 (usp - 24)).
stepn F_5e058 D_5e058.
stepn F_5e05c D_5e05c.
stepn F_5e060 D_5e060.
stepn F_5e064 D_5e064.
stepn F_5e068 D_5e068.
rwH. fold s0 s1. unfold mem1. apply mst_refl.
- cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
repeat (destruct Hx as [<-|Hx];
[first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
| gres; reflexivity ] |]).
destruct Hx. }
cbv beta. intros r1 (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK).

eapply (runs_trans RSEGS _ (fun r => mkst r (0x5fe48 : word) (mem1 ret s0 s1) rom)
(fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
{ destruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0x5fe48 : word) (HOK1 ret s0 s1)
ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
cbv beta. intros r2 (A10 & KC).
assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).

eexists. split.
- stepb_ft F_5e06c D_5e06c ltac:(rwH; apply c_eq_neq; unorm; lia).
stepiv F_5e070 D_5e070 (Z_to_bv 64 K)
ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).
stepn F_5e074 D_5e074.
mld8 F_5e078 D_5e078 ret (rd_ra ret s0 s1).
mld8 F_5e07c D_5e07c s0 (rd_s0 ret s0 s1).
mld8 F_5e080 D_5e080 s1 (rd_s1 ret s0 s1).
stepiv F_5e084 D_5e084 sp
ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).

stepret F_5e088 D_5e088 ret ltac:(reflexivity).
apply mst_refl.
- split.
+ intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
repeat (destruct Hx as [<-|Hx];
[ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
| rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
destruct Hx.
+ gres. reflexivity.
Qed.
End SNL.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
mchrH mem s buf K n ->
(0 < bv_unsigned s + K)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
(0x13428 <= bv_unsigned sp - 32)%Z ->
(bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
exists regs' mem',
msteps RSEGS (mkst regs (0x5fe24 : word) mem rom) (mkst regs' ret mem' rom)
/\ keeps_cs regs regs'
/\ getr regs' 10 = Z_to_bv 64 K
/\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
destruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
as (r & RUN & KC & A10).
exists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.
End FPGEN1.

End Mq4.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq6.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
match s with
| [] => acc
| b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Section Defs.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av ev : list (list byte).

Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).

Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
Definition auxv_w : word :=
Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
Definition argc_w : word := argcN av.

Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
Definition progname_w : word :=
Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).

Definition rnd_w : word := at_random_ptr sp0 av ev.

Definition D_libc : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
(Z_to_bv 64 0x77b30) (word_to_le_bytes 8 envp_w))
(Z_to_bv 64 0x97e98) (word_to_le_bytes 8 auxv_w))
(Z_to_bv 64 0x97ef8) (word_to_le_bytes 8 a_hwcap))
(Z_to_bv 64 0x97ec0) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
(Z_to_bv 64 0x97e88) (word_to_le_bytes 8 pn_w))
(Z_to_bv 64 0x97e80) (word_to_le_bytes 8 progname_w).

Definition J_lsm (J : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes
(wbytes (wbytes (wbytes (wbytes J
(Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x5083c)))
(Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x20b84)).

Definition J_aux (Jf : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
(wbytes Jf aux_base (zeros 304))
(Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))
(Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))
(Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 11)))
(Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 a_hwcap))
(Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
(Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 a_uid))
(Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 a_uid))
(Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).

Definition D_tlsA (D : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
(wbytes (wbytes (wbytes (wbytes (wbytes D
(Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680)))
(Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8)))
(Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10)))
(Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1)))
(Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8)))
(Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232)))
(Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8)))
(Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400)))
(Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1)))
(Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10)))
(Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38)))
(Z_to_bv 64 0x97e90) [Z_to_bv 8 1])
(Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2)).

Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
(Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid))
(Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8)))
(Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0)))
(Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38)))
(Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38)))
(Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
D_tlsB tid (D_tlsA D).

Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
(Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
(Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
(Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
(Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
(Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

Definition D_ssp (D : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes D
(Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3])
(Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7])
(Z_to_bv 64 0x97e71) [Z_to_bv 8 0])
(Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary).

Definition D_fd (D : word -> option byte) : word -> option byte :=
wbytes D (Z_to_bv 64 0x66f30) [Z_to_bv 8 1].

Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
End FPGEN1.
