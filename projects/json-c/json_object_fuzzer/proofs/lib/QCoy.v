(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL QvfX QWTC.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QvfX.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition imemcpy_words : list (bv 32) :=
[W_74f0c; W_74f10; W_74f14; W_74f18; W_74f1c; W_74f20; W_74f24; W_74f28; W_74f2c].

Definition imemcpy_clob : list reg := [11; 12; 13; 14].

Section IMEMCPY.
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
+ mlbu C12 D_74f18 k.
msb C16 D_74f1c k.
an C20 D_74f20.
an C24 D_74f24.
ab_ft C28 D_74f28 ltac:(condz).
aret C32 D_74f2c ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemcpy_clob. solve_regs_agree.
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C12 D_74f18 k.
msb C16 D_74f1c k.
an C20 D_74f20.
an C24 D_74f24.
ab_tk C28 D_74f28 ltac:(condz).
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
+ ab_tk C0 D_74f0c ltac:(condz).
aret C32 D_74f2c ret.
rewrite Hz. apply mst_refl.
+ apply regs_agree_refl.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C0 D_74f0c ltac:(condz).
av C4 D_74f10 (at_ dst n) ltac:(apply v_add_at; lia).
an C8 D_74f14.
apply mst_refl.
* post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End IMEMCPY.

Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Definition asan_imemcpy_entry : word := 0x74ef4.

Lemma asan_imemcpy_code :
code_at Asan.M.loaded_segments asan_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem asan_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
cpyH Asan.M.loaded_segments mem0 dst src n bs ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps Asan.M.loaded_segments
(mkst regs asan_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
intros mem0 dst src n bs rom regs ret HOK.
rewrite <- (at_0 asan_imemcpy_entry).
apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QvfX.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition imemset_words : list (bv 32) :=
[W_74f88; W_74f8c; W_74f90; W_74f94; W_74f98; W_74f9c; W_74fa0; W_74fa4;
W_74fa8; W_74fac; W_74fb0; W_74fb4; W_74fb8; W_74fbc; W_74fc0; W_74fc4;
W_74fc8; W_74fcc; W_74fd0; W_74fd4; W_74fd8; W_74fdc; W_74fe0; W_74fe4].

Definition imemset_clob : list reg := [11; 12; 13].

Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.

Lemma land15_range : forall x, (0 <= x)%Z -> (0 <= Z.land x 15 < 16)%Z.
Proof.
intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : forall n s, (0 <= n)%Z -> (0 <= align15 n s < 16)%Z.
Proof.
intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : forall n (s : word), (0 <= n < 2 ^ 64)%Z ->
bv_unsigned (v_andi (v_or (Z_to_bv 64 n) s) 15) = align15 n s.
Proof.
intros n s Hn. pose proof (u64_range s) as Hs.
pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
change (bv_wrap 64 15) with 15%Z.
pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : forall n s, (0 <= n)%Z -> align15 n s = 0%Z -> (n mod 16 = 0)%Z.
Proof.
intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).

Lemma cpat_bytes : forall c : word, (bv_unsigned c < 256)%Z ->
word_to_le_bytes 8 (cpat_ c) = repeat (cbyte_ c) 8.
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.

Section IMEMSET.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables s c : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 imemset_words.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.

Hypothesis HC256 : align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z.

#[local] Abbreviation cbyte := (cbyte_ c).
#[local] Abbreviation cpat := (cpat_ c).
#[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
#[local] Abbreviation CL := (fun r => In r imemset_clob).

Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).

Ltac msb F D kk :=
chain_step; [reflexivity
| eapply QHup.Mq1.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity | reflexivity
| apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
| step_simpl];
rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

Ltac msd F D kk :=
chain_step; [reflexivity
| eapply step_sd_at with (a := at_ s kk) (v := cpat);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity
| apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
| step_simpl];
rewrite (cpat_bytes c) by lia;
rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.

Lemma bl_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = c -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
(0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 24) (MS k) rom) (mkst regs' ret (MS n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
- eexists. split.
+ msb C24 D_74fa0 k.
an C28 D_74fa4.
ab_ft C32 D_74fa8 ltac:(condz).
an C36 D_74fac.
aret C92 D_74fe4 ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemset_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
+ eexists. split.
* msb C24 D_74fa0 k.
an C28 D_74fa4.
ab_tk C32 D_74fa8 ltac:(condz).
apply mst_refl.
* post. unfold imemset_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.

Lemma al_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = cpat -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
(0 <= k)%Z -> (k + 16 <= n)%Z -> (Z.of_nat i * 16 = n - k - 16)%Z ->
(bv_unsigned c < 256)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 76) (MS k) rom) (mkst regs' ret (MS n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
- eexists. split.
+ msd C76 D_74fd4 k.
msd C80 D_74fd8 (k + 8)%Z.
an C84 D_74fdc.
ab_ft C88 D_74fe0 ltac:(condz).
aret C92 D_74fe4 ret.
replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
+ unfold imemset_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
+ eexists. split.
* msd C76 D_74fd4 k.
msd C80 D_74fd8 (k + 8)%Z.
an C84 D_74fdc.
ab_tk C88 D_74fe0 ltac:(condz).
replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
* post. unfold imemset_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.

Theorem imemset_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom)
(mkst regs' ret (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
pose proof (align15_range n s Hn) as HA.
change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).

eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
/\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
{ eexists. split.
- an C0 D_74f88.
av C4 D_74f8c (Z_to_bv 64 (align15 n s))
ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).
apply mst_refl.
- post. unfold imemset_clob. solve_regs_agree. }
cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
-
destruct (Z.eq_dec n 0) as [Hz|Hnz].
+ eexists. split.
* ab_tk C8 D_74f90 ltac:(condz).
ab_tk C40 D_74fb0 ltac:(condz).
aret C92 D_74fe4 ret.
rewrite Hz. apply mst_refl.
* exact AG0.
+ pose proof (HC256 HA0 Hnz) as Hc256.
pose proof (align15_n16 n s Hn HA0) as Hn16.
eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
* eexists. split.
-- ab_tk C8 D_74f90 ltac:(condz).
ab_ft C40 D_74fb0 ltac:(condz).
av C44 D_74fb4 (at_ s n) ltac:(apply v_add_at; lia).
av C48 D_74fb8 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).
av_or C52 D_74fbc (Z_to_bv 64 (bv_unsigned c * 257))
ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).
av C56 D_74fc0 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).
av_or C60 D_74fc4 (Z_to_bv 64 (bv_unsigned c * 16843009))
ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).
av C64 D_74fc8 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).
av_or C68 D_74fcc (cpat_ c)
ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia).
an C72 D_74fd0.
apply mst_refl.
-- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
* cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
destruct Hi as (i & Hi).
destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hz|Hnz].
+ eexists. split.
* ab_ft C8 D_74f90 ltac:(condz).
ab_tk C12 D_74f94 ltac:(condz).
aret C92 D_74fe4 ret.
rewrite Hz. apply mst_refl.
* exact AG0.
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C8 D_74f90 ltac:(condz).
ab_ft C12 D_74f94 ltac:(condz).
av C16 D_74f98 (at_ s n) ltac:(apply v_add_at; lia).
an C20 D_74f9c.
apply mst_refl.
-- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
* cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End IMEMSET.

Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Definition asan_imemset_entry : word := 0x74f70.

Lemma asan_imemset_code :
code_at Asan.M.loaded_segments asan_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem asan_imemset : forall mem0 (s c : word) n rom regs (ret : word),
(0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
store_ok Asan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
(align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps Asan.M.loaded_segments
(mkst regs asan_imemset_entry mem0 rom)
(mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
/\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
rewrite <- (at_0 asan_imemset_entry).
apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QvfX.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memisz_words : list (bv 32) :=
[W_754b8; W_754bc; W_754c0; W_754c4; W_754c8; W_754cc; W_754d0; W_754d4;
W_754d8; W_754dc; W_754e0; W_754e4; W_754e8; W_754ec; W_754f0; W_754f4;
W_754f8; W_754fc; W_75500; W_75504; W_75508; W_7550c; W_75510; W_75514;
W_75518; W_7551c; W_75520; W_75524; W_75528; W_7552c; W_75530; W_75534;
W_75538; W_7553c; W_75540; W_75544; W_75548; W_7554c; W_75550].

Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].

Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 8)%Z.
Proof.
intros a Ha.
replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). change (2 ^ 3)%Z with 8%Z in *. lia.
Qed.

Lemma v_andi_m8 : forall (a : word) d,
(0 <= bv_unsigned a + d < 2 ^ 64)%Z ->
v_andi (at_ a d) (-8) = at_ a (d - (bv_unsigned a + d) mod 8).
Proof.
intros a d Hd. unfold v_andi, at_. f_equal.
change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

Lemma rdn_all1 : forall segs m n (a : word) b,
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z ->
rdn segs m x 1 = Some [b]) ->
rdn segs m a n = Some (repeat b n).
Proof.
intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
pose proof (Hall a ltac:(lia)) as R. cbn [rdn repeat] in R |- *.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
injection R as ->.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
reflexivity.
Qed.

Lemma regs_agree_upd_same : forall (C : regset) regs regs' (r : reg) v,
regs_agree C regs regs' -> getr regs r = v -> r <> 0 -> regs_agree C regs (regupd regs' r v).
Proof.
intros C regs regs' r v AG Hv Hnz x Hx.
destruct (decide (x = r)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

Lemma regs_agree_strengthen : forall (l l' : list reg) regs regs',
regs_agree (fun r => In r l') regs regs' ->
(forall r, In r l' -> ~ In r l -> getr regs' r = getr regs r) ->
regs_agree (fun r => In r l) regs regs'.
Proof.
intros l l' regs regs' AG E r Hr.
destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
- apply E; assumption.
- apply AG, Hnin.
Qed.

Section MEMISZERO.
Variable segs : list Segment.
Variable base : word.
Variable mem : word -> option byte.
Variables beg sp : word.
Variable N : Z.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 memisz_words.
Hypothesis HN : (0 <= N <= 2 ^ 40)%Z.
Hypothesis Hnw : (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z.
Hypothesis Hsp : (16 <= bv_unsigned sp)%Z.
Hypothesis Hstk : store_ok segs mem (at_ sp (-8)) 8 = true.
Hypothesis Hdisj : (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z.
Hypothesis Hz : forall a : word,
(bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].

#[local] Abbreviation B := (bv_unsigned beg).
#[local] Abbreviation Z0 := (Z_to_bv 64 0).
#[local] Abbreviation CL := (fun r => In r memisz_clob').

Definition dAB : Z := 7 - (B + 7) mod 8.
Definition dAE : Z := N - (B + N) mod 8.

Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).

Lemma dAB_range : (0 <= dAB <= 7)%Z.
Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
Proof.
unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
Qed.

Lemma rd1 : forall ra j, (0 <= j < N)%Z -> rdn segs (mem1 ra) (at_ beg j) 1 = Some [Z_to_bv 8 0].
Proof.
intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
apply Hz. rewrite at_u; lia.
Qed.

Lemma rd8 : forall ra j, (0 <= j)%Z -> (j + 8 <= N)%Z -> rdn segs (mem1 ra) (at_ beg j) 8 = Some (zeros 8).
Proof.
intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
replace x with (at_ beg (bv_unsigned x - B)).
- apply rd1. lia.
- unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
Qed.

Lemma rd_ra : forall ra, rdn segs (mem1 ra) (at_ sp (-8)) 8 = Some (word_to_le_bytes 8 ra).
Proof. intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.

Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
& C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
& C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).

Ltac mlbu F D :=
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
| step_simpl]; vn.

Ltac mld F D :=
chain_step; [reflexivity
| eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; apply rd8; lia
| reflexivity]
| step_simpl]; vn.

Lemma fin_run : forall regs (ret : word),
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
exists regs',
msteps segs (mkst regs (at_ base 140) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
eexists. split; [|split; [|split; [|split]]].
- an C140 D_75544.
chain_step; [reflexivity
| eapply step_ld with (v := ret);
[exact C144 | reflexivity | exact D_75548
| gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
| apply bytes_le_to_Z_8]
| step_simpl]; vn.
an C148 D_7554c.
aret C152 D_75550 ret.
apply mst_refl.
- unfold memisz_clob'. solve_regs_agree.
- gres. reflexivity.
- gres. rewrite ?at_0. reflexivity.
- gres. reflexivity.
Qed.

Lemma ep_loop : forall (i : nat) regs (ret : word) q cnt,
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg q -> getr regs 14 = Z_to_bv 64 cnt ->
(0 <= q)%Z -> (1 <= cnt)%Z -> (q + cnt <= N)%Z -> Z.of_nat i = (cnt - 1)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 120) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. pose proof (u64_range beg) as Hb.
induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C120 D_75530.
av C124 D_75534 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
an C128 D_75538.
an C132 D_7553c.
ab_ft C136 D_75540 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
/\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C120 D_75530.
av C124 D_75534 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
an C128 D_75538.
an C132 D_7553c.
ab_tk C136 D_75540 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma tail_run : forall regs (ret : word),
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N ->
exists regs',
msteps segs (mkst regs (at_ base 108) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H2 H10 H11 H12 H14.
pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C108 D_75524 ltac:(rewrite <- (at_0 beg) at 2; condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C108 D_75524 ltac:(rewrite <- (at_0 beg) at 2; condz).
ab_ft C112 D_75528 ltac:(condz).
av C116 D_7552c (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C108 D_75524 ltac:(rewrite <- (at_0 beg) at 2; condz).
ab_tk C112 D_75528 ltac:(condz).
apply mst_refl.
-- post; apply regs_agree_refl.
* cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma w_loop : forall (i : nat) regs (ret : word) p,
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg p ->
(0 <= p)%Z -> (p + 8 <= dAE)%Z -> (Z.of_nat i * 8 = dAE - p - 8)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 92) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
+ eexists. split.
* mld C92 D_75514.
an C96 D_75518.
an C100 D_7551c.
ab_ft C104 D_75520 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
+ eexists. split.
* mld C92 D_75514.
an C96 D_75518.
an C100 D_7551c.
ab_tk C104 D_75520 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma mid_run : forall regs (ret : word),
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg dAB ->
exists regs',
msteps segs (mkst regs (at_ base 88) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H2 H10 H11 H12 H14 H15.
pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
destruct (Z.lt_ge_cases dAB dAE) as [Hlt|Hge].
-
assert (Hi : exists i : nat, (Z.of_nat i * 8 = dAE - dAB - 8)%Z).
{ unfold dAB, dAE in *.
pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.div_mod (B + N) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
exists (Z.to_nat ((B + N) / 8 - (B + 7) / 8 - 1)). nia. }
destruct Hi as (i & Hi).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C88 D_75510 ltac:(condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C88 D_75510 ltac:(condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma pro_loop : forall (i : nat) regs (ret : word) j,
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 13 = at_ beg (j + 1) -> getr regs 14 = at_ beg N ->
getr regs 15 = at_ beg dAB ->
(0 <= j)%Z -> (j < dAB)%Z -> (j < N)%Z -> Z.of_nat i = (Z.min dAB N - 1 - j)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 64) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
-
destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- an C64 D_754f8.
mlbu C68 D_754fc.
an C72 D_75500.
ab_tk C76 D_75504 ltac:(condz).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- an C64 D_754f8.
mlbu C68 D_754fc.
an C72 D_75500.
ab_ft C76 D_75504 ltac:(condz).
an C80 D_75508.
ab_ft C84 D_7550c ltac:(condz).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = at_ beg (j + 1 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
+ eexists. split.
* an C64 D_754f8.
mlbu C68 D_754fc.
an C72 D_75500.
ab_ft C76 D_75504 ltac:(condz).
an C80 D_75508.
ab_tk C84 D_7550c ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Theorem mem_is_zero_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H1 H2 H10 H11.
pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.

eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
{ eexists. split.
- an C0 D_754b8.
chain_step; [reflexivity
| eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
[exact C4 | reflexivity | exact D_754bc
| gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
| gres; rwH; reflexivity
| exact Hstk]
| step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.

an C8 D_754c0.
an C12 D_754c4.
an C16 D_754c8.
an C20 D_754cc.
ab_ft C24 D_754d0 ltac:(condz).
an C28 D_754d4.
av C32 D_754d8 (at_ beg N) ltac:(apply v_add_at; lia).
an C36 D_754dc.
av C40 D_754e0 (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).
av C44 D_754e4 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).
apply mst_refl.
- post. unfold memisz_clob'. solve_regs_agree. }
cbv beta. intros r0 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0).

enough (G : exists regs',
msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
{ destruct G as (r' & RUN & AG & P10 & P2 & P1). exists r'. split; [exact RUN|]. split; [|repeat split; assumption].
apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
exfalso. apply Hnr. cbn [In]. tauto. }
destruct (Z.eq_dec dAB 0) as [HA0|HA0].
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C48 D_754e8 ltac:(rewrite <- (at_0 beg) at 1; condz).
apply mst_refl.
* post; exact AG0.
+ cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- destruct (Z.eq_dec N 0) as [HN0|HN0].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C48 D_754e8 ltac:(rewrite <- (at_0 beg) at 1; condz).
ab_tk C52 D_754ec ltac:(condz).
apply mst_refl.
-- post; exact AG0.
* cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C48 D_754e8 ltac:(rewrite <- (at_0 beg) at 1; condz).
ab_ft C52 D_754ec ltac:(condz).
an C56 D_754f0.
an C60 D_754f4.
apply mst_refl.
-- post. unfold memisz_clob'. ra_chain.
* cbv beta. intros r1 (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG).
destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
End MEMISZERO.

Lemma slot_at : forall sp : word, (16 <= bv_unsigned sp)%Z ->
at_ sp (-8) = Z_to_bv 64 (bv_unsigned sp - 8).
Proof. intros sp Hsp. unfold at_. f_equal; lia. Qed.

Theorem mem_is_zero_summary : forall segs (base : word) mem (beg sp : word) N rom regs (ret : word),
code_at segs base 0 memisz_words ->
(0 <= N <= 2 ^ 40)%Z ->
(bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
(16 <= bv_unsigned sp)%Z ->
store_ok segs mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
(forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
exists regs',
msteps segs (mkst regs base mem rom)
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.

Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Definition asan_mem_is_zero_entry : word := 0x754a0.

Lemma asan_mem_is_zero_code :
code_at Asan.M.loaded_segments asan_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem asan_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
(0 <= N <= 2 ^ 40)%Z ->
(bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
(16 <= bv_unsigned sp)%Z ->
store_ok Asan.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
(forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
rdn Asan.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
exists regs',
msteps Asan.M.loaded_segments
(mkst regs asan_mem_is_zero_entry mem rom)
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
intros mem beg sp N rom regs ret.
apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret asan_mem_is_zero_code).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE Q3bI QU0c QJ4Q Qo8J Q85Z QHup QG64 QWZn Qrlk QJJu QiyH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn Qrlk QJJu QiyH.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C1.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

Lemma c1_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3c0 : word) (MK k) rom) (mkst regs' (0xdb58c : word) (MK (k + 3)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_db3e4 D_db3e4 k.
stepn F_db3e8 D_db3e8.
stepb_ft F_db3ec D_db3ec ltac:(cond).
stepn F_db3f0 D_db3f0.
stepb_tk F_db3f4 D_db3f4 ltac:(cond).
stepn F_db58c D_db58c.
stepn F_db590 D_db590.
stepn F_db594 D_db594.
msb F_db598 D_db598 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_db59c D_db59c (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
msb F_db5a0 D_db5a0 (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia).
stepn F_db5a4 D_db5a4.
stepn F_db5a8 D_db5a8.
stepn F_db5ac D_db5ac.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
(ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb58c : word) (MK kk) rom)
(mkst regs' (0xdb5ec : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_db5b0 D_db5b0.
mlw F_db5b4 D_db5b4 (kk + 1)%Z.
mlw F_db5b8 D_db5b8 (kk + 5)%Z.
mlw F_db5bc D_db5bc (kk + 9)%Z.
mlw F_db5c0 D_db5c0 (kk + 13)%Z.
stepn F_db5c4 D_db5c4. stepn F_db5c8 D_db5c8. stepn F_db5cc D_db5cc.
stepn F_db5d0 D_db5d0. stepn F_db5d4 D_db5d4. stepn F_db5d8 D_db5d8.
stepn F_db5dc D_db5dc. stepn F_db5e0 D_db5e0. stepn F_db5e4 D_db5e4.
stepn F_db5e8 D_db5e8. stepn F_db5ec D_db5ec.
stepn F_db5f0 D_db5f0.
msw F_db5f4 D_db5f4 kk ltac:(m24).
msw F_db5f8 D_db5f8 (kk + 4)%Z ltac:(m24).
msw F_db5fc D_db5fc (kk + 8)%Z ltac:(m24).
msw F_db600 D_db600 (kk + 12)%Z ltac:(m24).
stepn F_db604 D_db604.
stepn F_db608 D_db608.
stepb_ft F_db60c D_db60c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb58c : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
/\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
+ eexists. split.
* stepn F_db5b0 D_db5b0.
mlw F_db5b4 D_db5b4 (kk + 1)%Z.
mlw F_db5b8 D_db5b8 (kk + 5)%Z.
mlw F_db5bc D_db5bc (kk + 9)%Z.
mlw F_db5c0 D_db5c0 (kk + 13)%Z.
stepn F_db5c4 D_db5c4. stepn F_db5c8 D_db5c8. stepn F_db5cc D_db5cc.
stepn F_db5d0 D_db5d0. stepn F_db5d4 D_db5d4. stepn F_db5d8 D_db5d8.
stepn F_db5dc D_db5dc. stepn F_db5e0 D_db5e0. stepn F_db5e4 D_db5e4.
stepn F_db5e8 D_db5e8. stepn F_db5ec D_db5ec.
stepn F_db5f0 D_db5f0.
msw F_db5f4 D_db5f4 kk ltac:(m24).
msw F_db5f8 D_db5f8 (kk + 4)%Z ltac:(m24).
msw F_db5fc D_db5fc (kk + 8)%Z ltac:(m24).
msw F_db600 D_db600 (kk + 12)%Z ltac:(m24).
stepn F_db604 D_db604.
stepn F_db608 D_db608.
stepb_tk F_db60c D_db60c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma c1_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps JO6SEGS (mkst regs (0xdb5ec : word) (MK kk) rom)
(mkst regs' (0xdb70c : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3ac : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_db610 D_db610.
stepn F_db614 D_db614.
stepb_tk F_db618 D_db618 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb5f8 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_db610 D_db610.
stepn F_db614 D_db614.
stepb_ft F_db618 D_db618 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb684 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma c1_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps JO6SEGS (mkst regs (0xdb3c0 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn Qrlk QJJu QiyH.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C2.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

Lemma c2_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3c0 : word) (MK k) rom) (mkst regs' (0xdb3f0 : word) (MK (k + 2)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_db3e4 D_db3e4 k.
stepn F_db3e8 D_db3e8.
stepb_ft F_db3ec D_db3ec ltac:(cond).
stepn F_db3f0 D_db3f0.
stepb_ft F_db3f4 D_db3f4 ltac:(cond).
stepn F_db3f8 D_db3f8.
stepn F_db3fc D_db3fc.
msb F_db400 D_db400 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_db404 D_db404 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
stepn F_db408 D_db408.
stepn F_db40c D_db40c.
stepn F_db410 D_db410.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
(ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3f0 : word) (MK kk) rom)
(mkst regs' (0xdb450 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_db414 D_db414.
mlw F_db418 D_db418 (kk + 2)%Z.
mlw F_db41c D_db41c (kk + 6)%Z.
mlw F_db420 D_db420 (kk + 10)%Z.
mlw F_db424 D_db424 (kk + 14)%Z.
stepn F_db428 D_db428. stepn F_db42c D_db42c. stepn F_db430 D_db430.
stepn F_db434 D_db434. stepn F_db438 D_db438. stepn F_db43c D_db43c.
stepn F_db440 D_db440. stepn F_db444 D_db444. stepn F_db448 D_db448.
stepn F_db44c D_db44c. stepn F_db450 D_db450.
stepn F_db454 D_db454.
msw F_db458 D_db458 kk ltac:(m16).
msw F_db45c D_db45c (kk + 4)%Z ltac:(m16).
msw F_db460 D_db460 (kk + 8)%Z ltac:(m16).
msw F_db464 D_db464 (kk + 12)%Z ltac:(m16).
stepn F_db468 D_db468.
stepn F_db46c D_db46c.
stepb_ft F_db470 D_db470 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3f0 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
/\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
+ eexists. split.
* stepn F_db414 D_db414.
mlw F_db418 D_db418 (kk + 2)%Z.
mlw F_db41c D_db41c (kk + 6)%Z.
mlw F_db420 D_db420 (kk + 10)%Z.
mlw F_db424 D_db424 (kk + 14)%Z.
stepn F_db428 D_db428. stepn F_db42c D_db42c. stepn F_db430 D_db430.
stepn F_db434 D_db434. stepn F_db438 D_db438. stepn F_db43c D_db43c.
stepn F_db440 D_db440. stepn F_db444 D_db444. stepn F_db448 D_db448.
stepn F_db44c D_db44c. stepn F_db450 D_db450.
stepn F_db454 D_db454.
msw F_db458 D_db458 kk ltac:(m16).
msw F_db45c D_db45c (kk + 4)%Z ltac:(m16).
msw F_db460 D_db460 (kk + 8)%Z ltac:(m16).
msw F_db464 D_db464 (kk + 12)%Z ltac:(m16).
stepn F_db468 D_db468.
stepn F_db46c D_db46c.
stepb_tk F_db470 D_db470 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma c2_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps JO6SEGS (mkst regs (0xdb450 : word) (MK kk) rom)
(mkst regs' (0xdb70c : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3ac : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_db474 D_db474.
stepn F_db478 D_db478.
stepb_tk F_db47c D_db47c ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb5f8 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_db474 D_db474.
stepn F_db478 D_db478.
stepb_ft F_db47c D_db47c ltac:(cond).
stepn F_db480 D_db480.
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb684 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma c2_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps JO6SEGS (mkst regs (0xdb3c0 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn Qrlk QJJu QiyH.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C3.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

Lemma c3_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb3c0 : word) (MK k) rom) (mkst regs' (0xdb4f8 : word) (MK (k + 1)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_db3e4 D_db3e4 k.
stepn F_db3e8 D_db3e8.
stepb_tk F_db3ec D_db3ec ltac:(cond).
msb F_db508 D_db508 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
stepn F_db50c D_db50c.
stepn F_db510 D_db510.
stepn F_db514 D_db514.
stepn F_db518 D_db518.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
(ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb4f8 : word) (MK kk) rom)
(mkst regs' (0xdb558 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_db51c D_db51c.
mlw F_db520 D_db520 (kk + 3)%Z.
mlw F_db524 D_db524 (kk + 7)%Z.
mlw F_db528 D_db528 (kk + 11)%Z.
mlw F_db52c D_db52c (kk + 15)%Z.
stepn F_db530 D_db530. stepn F_db534 D_db534. stepn F_db538 D_db538.
stepn F_db53c D_db53c. stepn F_db540 D_db540. stepn F_db544 D_db544.
stepn F_db548 D_db548. stepn F_db54c D_db54c. stepn F_db550 D_db550.
stepn F_db554 D_db554. stepn F_db558 D_db558.
stepn F_db55c D_db55c.
msw F_db560 D_db560 kk ltac:(m8).
msw F_db564 D_db564 (kk + 4)%Z ltac:(m8).
msw F_db568 D_db568 (kk + 8)%Z ltac:(m8).
msw F_db56c D_db56c (kk + 12)%Z ltac:(m8).
stepn F_db570 D_db570.
stepn F_db574 D_db574.
stepb_ft F_db578 D_db578 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb4f8 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
/\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
+ eexists. split.
* stepn F_db51c D_db51c.
mlw F_db520 D_db520 (kk + 3)%Z.
mlw F_db524 D_db524 (kk + 7)%Z.
mlw F_db528 D_db528 (kk + 11)%Z.
mlw F_db52c D_db52c (kk + 15)%Z.
stepn F_db530 D_db530. stepn F_db534 D_db534. stepn F_db538 D_db538.
stepn F_db53c D_db53c. stepn F_db540 D_db540. stepn F_db544 D_db544.
stepn F_db548 D_db548. stepn F_db54c D_db54c. stepn F_db550 D_db550.
stepn F_db554 D_db554. stepn F_db558 D_db558.
stepn F_db55c D_db55c.
msw F_db560 D_db560 kk ltac:(m8).
msw F_db564 D_db564 (kk + 4)%Z ltac:(m8).
msw F_db568 D_db568 (kk + 8)%Z ltac:(m8).
msw F_db56c D_db56c (kk + 12)%Z ltac:(m8).
stepn F_db570 D_db570.
stepn F_db574 D_db574.
stepb_tk F_db578 D_db578 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma c3_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps JO6SEGS (mkst regs (0xdb558 : word) (MK kk) rom)
(mkst regs' (0xdb70c : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3ac : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_db57c D_db57c.
stepn F_db580 D_db580.
stepb_tk F_db584 D_db584 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb5f8 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_db57c D_db57c.
stepn F_db580 D_db580.
stepb_ft F_db584 D_db584 ltac:(cond).
stepn F_db588 D_db588.
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb684 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma c3_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps JO6SEGS (mkst regs (0xdb3c0 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq5.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 QqZL.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

#[local] Notation JO6SEGS := Asan.M.loaded_segments (only parsing).

Definition asan_popfree_head : Z := 0x445b4.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Lemma PF0 : fetch_word JO6SEGS (Z_to_bv 64 asan_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word JO6SEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec Asan.M.loaded_segments asan_popfree_head.
Proof.
apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

End Mq6.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QvfX.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition imemcpy_words : list (bv 32) :=
[W_7530c; W_75310; W_75314; W_75318; W_7531c; W_75320; W_75324; W_75328; W_7532c].

Definition imemcpy_clob : list reg := [11; 12; 13; 14].

Section IMEMCPY.
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
+ mlbu C12 D_75318 k.
msb C16 D_7531c k.
an C20 D_75320.
an C24 D_75324.
ab_ft C28 D_75328 ltac:(condz).
aret C32 D_7532c ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemcpy_clob. solve_regs_agree.
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C12 D_75318 k.
msb C16 D_7531c k.
an C20 D_75320.
an C24 D_75324.
ab_tk C28 D_75328 ltac:(condz).
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
+ ab_tk C0 D_7530c ltac:(condz).
aret C32 D_7532c ret.
rewrite Hz. apply mst_refl.
+ apply regs_agree_refl.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C0 D_7530c ltac:(condz).
av C4 D_75310 (at_ dst n) ltac:(apply v_add_at; lia).
an C8 D_75314.
apply mst_refl.
* post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End IMEMCPY.

Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Definition asan_imemcpy_entry : word := 0x752cc.

Lemma asan_imemcpy_code :
code_at AsanUbsan.M.loaded_segments asan_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem asan_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
cpyH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps AsanUbsan.M.loaded_segments
(mkst regs asan_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
intros mem0 dst src n bs rom regs ret HOK.
rewrite <- (at_0 asan_imemcpy_entry).
apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QvfX.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition imemset_words : list (bv 32) :=
[W_75388; W_7538c; W_75390; W_75394; W_75398; W_7539c; W_753a0; W_753a4;
W_753a8; W_753ac; W_753b0; W_753b4; W_753b8; W_753bc; W_753c0; W_753c4;
W_753c8; W_753cc; W_753d0; W_753d4; W_753d8; W_753dc; W_753e0; W_753e4].

Definition imemset_clob : list reg := [11; 12; 13].

Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.

Lemma land15_range : forall x, (0 <= x)%Z -> (0 <= Z.land x 15 < 16)%Z.
Proof.
intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : forall n s, (0 <= n)%Z -> (0 <= align15 n s < 16)%Z.
Proof.
intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : forall n (s : word), (0 <= n < 2 ^ 64)%Z ->
bv_unsigned (v_andi (v_or (Z_to_bv 64 n) s) 15) = align15 n s.
Proof.
intros n s Hn. pose proof (u64_range s) as Hs.
pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
change (bv_wrap 64 15) with 15%Z.
pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : forall n s, (0 <= n)%Z -> align15 n s = 0%Z -> (n mod 16 = 0)%Z.
Proof.
intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).

Lemma cpat_bytes : forall c : word, (bv_unsigned c < 256)%Z ->
word_to_le_bytes 8 (cpat_ c) = repeat (cbyte_ c) 8.
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.

Section IMEMSET.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables s c : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 imemset_words.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.

Hypothesis HC256 : align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z.

#[local] Abbreviation cbyte := (cbyte_ c).
#[local] Abbreviation cpat := (cpat_ c).
#[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
#[local] Abbreviation CL := (fun r => In r imemset_clob).

Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).

Ltac msb F D kk :=
chain_step; [reflexivity
| eapply QHup.Mq1.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity | reflexivity
| apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
| step_simpl];
rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

Ltac msd F D kk :=
chain_step; [reflexivity
| eapply step_sd_at with (a := at_ s kk) (v := cpat);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity
| apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
| step_simpl];
rewrite (cpat_bytes c) by lia;
rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.

Lemma bl_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = c -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
(0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 24) (MS k) rom) (mkst regs' ret (MS n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
- eexists. split.
+ msb C24 D_753a0 k.
an C28 D_753a4.
ab_ft C32 D_753a8 ltac:(condz).
an C36 D_753ac.
aret C92 D_753e4 ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemset_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
+ eexists. split.
* msb C24 D_753a0 k.
an C28 D_753a4.
ab_tk C32 D_753a8 ltac:(condz).
apply mst_refl.
* post. unfold imemset_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.

Lemma al_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = cpat -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
(0 <= k)%Z -> (k + 16 <= n)%Z -> (Z.of_nat i * 16 = n - k - 16)%Z ->
(bv_unsigned c < 256)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 76) (MS k) rom) (mkst regs' ret (MS n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
- eexists. split.
+ msd C76 D_753d4 k.
msd C80 D_753d8 (k + 8)%Z.
an C84 D_753dc.
ab_ft C88 D_753e0 ltac:(condz).
aret C92 D_753e4 ret.
replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
+ unfold imemset_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
+ eexists. split.
* msd C76 D_753d4 k.
msd C80 D_753d8 (k + 8)%Z.
an C84 D_753dc.
ab_tk C88 D_753e0 ltac:(condz).
replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
* post. unfold imemset_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.

Theorem imemset_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom)
(mkst regs' ret (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
pose proof (align15_range n s Hn) as HA.
change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).

eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
/\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
{ eexists. split.
- an C0 D_75388.
av C4 D_7538c (Z_to_bv 64 (align15 n s))
ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).
apply mst_refl.
- post. unfold imemset_clob. solve_regs_agree. }
cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
-
destruct (Z.eq_dec n 0) as [Hz|Hnz].
+ eexists. split.
* ab_tk C8 D_75390 ltac:(condz).
ab_tk C40 D_753b0 ltac:(condz).
aret C92 D_753e4 ret.
rewrite Hz. apply mst_refl.
* exact AG0.
+ pose proof (HC256 HA0 Hnz) as Hc256.
pose proof (align15_n16 n s Hn HA0) as Hn16.
eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
* eexists. split.
-- ab_tk C8 D_75390 ltac:(condz).
ab_ft C40 D_753b0 ltac:(condz).
av C44 D_753b4 (at_ s n) ltac:(apply v_add_at; lia).
av C48 D_753b8 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).
av_or C52 D_753bc (Z_to_bv 64 (bv_unsigned c * 257))
ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).
av C56 D_753c0 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).
av_or C60 D_753c4 (Z_to_bv 64 (bv_unsigned c * 16843009))
ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).
av C64 D_753c8 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).
av_or C68 D_753cc (cpat_ c)
ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia).
an C72 D_753d0.
apply mst_refl.
-- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
* cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
destruct Hi as (i & Hi).
destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hz|Hnz].
+ eexists. split.
* ab_ft C8 D_75390 ltac:(condz).
ab_tk C12 D_75394 ltac:(condz).
aret C92 D_753e4 ret.
rewrite Hz. apply mst_refl.
* exact AG0.
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
/\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C8 D_75390 ltac:(condz).
ab_ft C12 D_75394 ltac:(condz).
av C16 D_75398 (at_ s n) ltac:(apply v_add_at; lia).
an C20 D_7539c.
apply mst_refl.
-- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
* cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End IMEMSET.

Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Definition asan_imemset_entry : word := 0x75348.

Lemma asan_imemset_code :
code_at AsanUbsan.M.loaded_segments asan_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem asan_imemset : forall mem0 (s c : word) n rom regs (ret : word),
(0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
store_ok AsanUbsan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
(align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps AsanUbsan.M.loaded_segments
(mkst regs asan_imemset_entry mem0 rom)
(mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
/\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
rewrite <- (at_0 asan_imemset_entry).
apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QvfX.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memisz_words : list (bv 32) :=
[W_758b8; W_758bc; W_758c0; W_758c4; W_758c8; W_758cc; W_758d0; W_758d4;
W_758d8; W_758dc; W_758e0; W_758e4; W_758e8; W_758ec; W_758f0; W_758f4;
W_758f8; W_758fc; W_75900; W_75904; W_75908; W_7590c; W_75910; W_75914;
W_75918; W_7591c; W_75920; W_75924; W_75928; W_7592c; W_75930; W_75934;
W_75938; W_7593c; W_75940; W_75944; W_75948; W_7594c; W_75950].

Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].

Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 8)%Z.
Proof.
intros a Ha.
replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). change (2 ^ 3)%Z with 8%Z in *. lia.
Qed.

Lemma v_andi_m8 : forall (a : word) d,
(0 <= bv_unsigned a + d < 2 ^ 64)%Z ->
v_andi (at_ a d) (-8) = at_ a (d - (bv_unsigned a + d) mod 8).
Proof.
intros a d Hd. unfold v_andi, at_. f_equal.
change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

Lemma rdn_all1 : forall segs m n (a : word) b,
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z ->
rdn segs m x 1 = Some [b]) ->
rdn segs m a n = Some (repeat b n).
Proof.
intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
pose proof (Hall a ltac:(lia)) as R. cbn [rdn repeat] in R |- *.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
injection R as ->.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
reflexivity.
Qed.

Lemma regs_agree_upd_same : forall (C : regset) regs regs' (r : reg) v,
regs_agree C regs regs' -> getr regs r = v -> r <> 0 -> regs_agree C regs (regupd regs' r v).
Proof.
intros C regs regs' r v AG Hv Hnz x Hx.
destruct (decide (x = r)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

Lemma regs_agree_strengthen : forall (l l' : list reg) regs regs',
regs_agree (fun r => In r l') regs regs' ->
(forall r, In r l' -> ~ In r l -> getr regs' r = getr regs r) ->
regs_agree (fun r => In r l) regs regs'.
Proof.
intros l l' regs regs' AG E r Hr.
destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
- apply E; assumption.
- apply AG, Hnin.
Qed.

Section MEMISZERO.
Variable segs : list Segment.
Variable base : word.
Variable mem : word -> option byte.
Variables beg sp : word.
Variable N : Z.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 memisz_words.
Hypothesis HN : (0 <= N <= 2 ^ 40)%Z.
Hypothesis Hnw : (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z.
Hypothesis Hsp : (16 <= bv_unsigned sp)%Z.
Hypothesis Hstk : store_ok segs mem (at_ sp (-8)) 8 = true.
Hypothesis Hdisj : (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z.
Hypothesis Hz : forall a : word,
(bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].

#[local] Abbreviation B := (bv_unsigned beg).
#[local] Abbreviation Z0 := (Z_to_bv 64 0).
#[local] Abbreviation CL := (fun r => In r memisz_clob').

Definition dAB : Z := 7 - (B + 7) mod 8.
Definition dAE : Z := N - (B + N) mod 8.

Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).

Lemma dAB_range : (0 <= dAB <= 7)%Z.
Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
Proof.
unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
Qed.

Lemma rd1 : forall ra j, (0 <= j < N)%Z -> rdn segs (mem1 ra) (at_ beg j) 1 = Some [Z_to_bv 8 0].
Proof.
intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
apply Hz. rewrite at_u; lia.
Qed.

Lemma rd8 : forall ra j, (0 <= j)%Z -> (j + 8 <= N)%Z -> rdn segs (mem1 ra) (at_ beg j) 8 = Some (zeros 8).
Proof.
intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
replace x with (at_ beg (bv_unsigned x - B)).
- apply rd1. lia.
- unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
Qed.

Lemma rd_ra : forall ra, rdn segs (mem1 ra) (at_ sp (-8)) 8 = Some (word_to_le_bytes 8 ra).
Proof. intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.

Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
& C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
& C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).

Ltac mlbu F D :=
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
| step_simpl]; vn.

Ltac mld F D :=
chain_step; [reflexivity
| eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi; apply rd8; lia
| reflexivity]
| step_simpl]; vn.

Lemma fin_run : forall regs (ret : word),
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
exists regs',
msteps segs (mkst regs (at_ base 140) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
eexists. split; [|split; [|split; [|split]]].
- an C140 D_75944.
chain_step; [reflexivity
| eapply step_ld with (v := ret);
[exact C144 | reflexivity | exact D_75948
| gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
| apply bytes_le_to_Z_8]
| step_simpl]; vn.
an C148 D_7594c.
aret C152 D_75950 ret.
apply mst_refl.
- unfold memisz_clob'. solve_regs_agree.
- gres. reflexivity.
- gres. rewrite ?at_0. reflexivity.
- gres. reflexivity.
Qed.

Lemma ep_loop : forall (i : nat) regs (ret : word) q cnt,
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg q -> getr regs 14 = Z_to_bv 64 cnt ->
(0 <= q)%Z -> (1 <= cnt)%Z -> (q + cnt <= N)%Z -> Z.of_nat i = (cnt - 1)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 120) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. pose proof (u64_range beg) as Hb.
induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C120 D_75930.
av C124 D_75934 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
an C128 D_75938.
an C132 D_7593c.
ab_ft C136 D_75940 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
/\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C120 D_75930.
av C124 D_75934 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
an C128 D_75938.
an C132 D_7593c.
ab_tk C136 D_75940 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma tail_run : forall regs (ret : word),
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N ->
exists regs',
msteps segs (mkst regs (at_ base 108) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H2 H10 H11 H12 H14.
pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C108 D_75924 ltac:(rewrite <- (at_0 beg) at 2; condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C108 D_75924 ltac:(rewrite <- (at_0 beg) at 2; condz).
ab_ft C112 D_75928 ltac:(condz).
av C116 D_7592c (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C108 D_75924 ltac:(rewrite <- (at_0 beg) at 2; condz).
ab_tk C112 D_75928 ltac:(condz).
apply mst_refl.
-- post; apply regs_agree_refl.
* cbv beta. intros r1 (R2 & R11 & AG).
destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma w_loop : forall (i : nat) regs (ret : word) p,
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg p ->
(0 <= p)%Z -> (p + 8 <= dAE)%Z -> (Z.of_nat i * 8 = dAE - p - 8)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 92) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
+ eexists. split.
* mld C92 D_75914.
an C96 D_75918.
an C100 D_7591c.
ab_ft C104 D_75920 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
+ eexists. split.
* mld C92 D_75914.
an C96 D_75918.
an C100 D_7591c.
ab_tk C104 D_75920 ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma mid_run : forall regs (ret : word),
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg dAB ->
exists regs',
msteps segs (mkst regs (at_ base 88) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H2 H10 H11 H12 H14 H15.
pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
destruct (Z.lt_ge_cases dAB dAE) as [Hlt|Hge].
-
assert (Hi : exists i : nat, (Z.of_nat i * 8 = dAE - dAB - 8)%Z).
{ unfold dAB, dAE in *.
pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.div_mod (B + N) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
exists (Z.to_nat ((B + N) / 8 - (B + 7) / 8 - 1)). nia. }
destruct Hi as (i & Hi).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C88 D_75910 ltac:(condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C88 D_75910 ltac:(condz).
apply mst_refl.
* post; apply regs_agree_refl.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Lemma pro_loop : forall (i : nat) regs (ret : word) j,
ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
getr regs 12 = at_ beg dAE -> getr regs 13 = at_ beg (j + 1) -> getr regs 14 = at_ beg N ->
getr regs 15 = at_ beg dAB ->
(0 <= j)%Z -> (j < dAB)%Z -> (j < N)%Z -> Z.of_nat i = (Z.min dAB N - 1 - j)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 64) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
-
destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- an C64 D_758f8.
mlbu C68 D_758fc.
an C72 D_75900.
ab_tk C76 D_75904 ltac:(condz).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+ eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- an C64 D_758f8.
mlbu C68 D_758fc.
an C72 D_75900.
ab_ft C76 D_75904 ltac:(condz).
an C80 D_75908.
ab_ft C84 D_7590c ltac:(condz).
apply mst_refl.
-- post. unfold memisz_clob'. solve_regs_agree.
* cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = at_ beg (j + 1 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
+ eexists. split.
* an C64 D_758f8.
mlbu C68 D_758fc.
an C72 D_75900.
ab_ft C76 D_75904 ltac:(condz).
an C80 D_75908.
ab_tk C84 D_7590c ltac:(condz).
apply mst_refl.
* post. unfold memisz_clob'. solve_regs_agree.
+ cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.

Theorem mem_is_zero_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
get_code. intros regs ret Hret H1 H2 H10 H11.
pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.

eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
{ eexists. split.
- an C0 D_758b8.
chain_step; [reflexivity
| eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
[exact C4 | reflexivity | exact D_758bc
| gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
| gres; rwH; reflexivity
| exact Hstk]
| step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.

an C8 D_758c0.
an C12 D_758c4.
an C16 D_758c8.
an C20 D_758cc.
ab_ft C24 D_758d0 ltac:(condz).
an C28 D_758d4.
av C32 D_758d8 (at_ beg N) ltac:(apply v_add_at; lia).
an C36 D_758dc.
av C40 D_758e0 (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).
av C44 D_758e4 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).
apply mst_refl.
- post. unfold memisz_clob'. solve_regs_agree. }
cbv beta. intros r0 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0).

enough (G : exists regs',
msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
/\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
{ destruct G as (r' & RUN & AG & P10 & P2 & P1). exists r'. split; [exact RUN|]. split; [|repeat split; assumption].
apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
exfalso. apply Hnr. cbn [In]. tauto. }
destruct (Z.eq_dec dAB 0) as [HA0|HA0].
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C48 D_758e8 ltac:(rewrite <- (at_0 beg) at 1; condz).
apply mst_refl.
* post; exact AG0.
+ cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
- destruct (Z.eq_dec N 0) as [HN0|HN0].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C48 D_758e8 ltac:(rewrite <- (at_0 beg) at 1; condz).
ab_tk C52 D_758ec ltac:(condz).
apply mst_refl.
-- post; exact AG0.
* cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
+
eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
(fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
/\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
/\ regs_agree CL regs r)).
* eexists. split.
-- ab_ft C48 D_758e8 ltac:(rewrite <- (at_0 beg) at 1; condz).
ab_ft C52 D_758ec ltac:(condz).
an C56 D_758f0.
an C60 D_758f4.
apply mst_refl.
-- post. unfold memisz_clob'. ra_chain.
* cbv beta. intros r1 (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG).
destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
Qed.
End MEMISZERO.

Lemma slot_at : forall sp : word, (16 <= bv_unsigned sp)%Z ->
at_ sp (-8) = Z_to_bv 64 (bv_unsigned sp - 8).
Proof. intros sp Hsp. unfold at_. f_equal; lia. Qed.

Theorem mem_is_zero_summary : forall segs (base : word) mem (beg sp : word) N rom regs (ret : word),
code_at segs base 0 memisz_words ->
(0 <= N <= 2 ^ 40)%Z ->
(bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
(16 <= bv_unsigned sp)%Z ->
store_ok segs mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
(forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
exists regs',
msteps segs (mkst regs base mem rom)
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.

Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Definition asan_mem_is_zero_entry : word := 0x75878.

Lemma asan_mem_is_zero_code :
code_at AsanUbsan.M.loaded_segments asan_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem asan_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
(0 <= N <= 2 ^ 40)%Z ->
(bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
(16 <= bv_unsigned sp)%Z ->
store_ok AsanUbsan.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
(forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
rdn AsanUbsan.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
exists regs',
msteps AsanUbsan.M.loaded_segments
(mkst regs asan_mem_is_zero_entry mem rom)
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
/\ regs_agree (fun r => In r memisz_clob) regs regs'
/\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
intros mem beg sp N rom regs ret.
apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret asan_mem_is_zero_code).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn.Mq0 Qrlk.Mq1 QJJu.Mq1 QiyH.Mq4.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C1.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

Lemma c1_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda84 : word) (MK k) rom) (mkst regs' (0xddc50 : word) (MK (k + 3)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_ddad0 D_ddad0 k.
stepn F_ddad4 D_ddad4.
stepb_ft F_ddad8 D_ddad8 ltac:(cond).
stepn F_ddadc D_ddadc.
stepb_tk F_ddae0 D_ddae0 ltac:(cond).
stepn F_ddc78 D_ddc78.
stepn F_ddc7c D_ddc7c.
stepn F_ddc80 D_ddc80.
msb F_ddc84 D_ddc84 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_ddc88 D_ddc88 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
msb F_ddc8c D_ddc8c (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia).
stepn F_ddc90 D_ddc90.
stepn F_ddc94 D_ddc94.
stepn F_ddc98 D_ddc98.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
(ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddc50 : word) (MK kk) rom)
(mkst regs' (0xddcb0 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_ddc9c D_ddc9c.
mlw F_ddca0 D_ddca0 (kk + 1)%Z.
mlw F_ddca4 D_ddca4 (kk + 5)%Z.
mlw F_ddca8 D_ddca8 (kk + 9)%Z.
mlw F_ddcac D_ddcac (kk + 13)%Z.
stepn F_ddcb0 D_ddcb0. stepn F_ddcb4 D_ddcb4. stepn F_ddcb8 D_ddcb8.
stepn F_ddcbc D_ddcbc. stepn F_ddcc0 D_ddcc0. stepn F_ddcc4 D_ddcc4.
stepn F_ddcc8 D_ddcc8. stepn F_ddccc D_ddccc. stepn F_ddcd0 D_ddcd0.
stepn F_ddcd4 D_ddcd4. stepn F_ddcd8 D_ddcd8.
stepn F_ddcdc D_ddcdc.
msw F_ddce0 D_ddce0 kk ltac:(m24).
msw F_ddce4 D_ddce4 (kk + 4)%Z ltac:(m24).
msw F_ddce8 D_ddce8 (kk + 8)%Z ltac:(m24).
msw F_ddcec D_ddcec (kk + 12)%Z ltac:(m24).
stepn F_ddcf0 D_ddcf0.
stepn F_ddcf4 D_ddcf4.
stepb_ft F_ddcf8 D_ddcf8 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddc50 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
/\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
+ eexists. split.
* stepn F_ddc9c D_ddc9c.
mlw F_ddca0 D_ddca0 (kk + 1)%Z.
mlw F_ddca4 D_ddca4 (kk + 5)%Z.
mlw F_ddca8 D_ddca8 (kk + 9)%Z.
mlw F_ddcac D_ddcac (kk + 13)%Z.
stepn F_ddcb0 D_ddcb0. stepn F_ddcb4 D_ddcb4. stepn F_ddcb8 D_ddcb8.
stepn F_ddcbc D_ddcbc. stepn F_ddcc0 D_ddcc0. stepn F_ddcc4 D_ddcc4.
stepn F_ddcc8 D_ddcc8. stepn F_ddccc D_ddccc. stepn F_ddcd0 D_ddcd0.
stepn F_ddcd4 D_ddcd4. stepn F_ddcd8 D_ddcd8.
stepn F_ddcdc D_ddcdc.
msw F_ddce0 D_ddce0 kk ltac:(m24).
msw F_ddce4 D_ddce4 (kk + 4)%Z ltac:(m24).
msw F_ddce8 D_ddce8 (kk + 8)%Z ltac:(m24).
msw F_ddcec D_ddcec (kk + 12)%Z ltac:(m24).
stepn F_ddcf0 D_ddcf0.
stepn F_ddcf4 D_ddcf4.
stepb_tk F_ddcf8 D_ddcf8 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma c1_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps JOB6SEGS (mkst regs (0xddcb0 : word) (MK kk) rom)
(mkst regs' (0xdddd0 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda70 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddcfc D_ddcfc.
stepn F_ddd00 D_ddd00.
stepb_tk F_ddd04 D_ddd04 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddcbc : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddcfc D_ddcfc.
stepn F_ddd00 D_ddd00.
stepb_ft F_ddd04 D_ddd04 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd48 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma c1_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps JOB6SEGS (mkst regs (0xdda84 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn.Mq0 Qrlk.Mq1 QJJu.Mq1 QiyH.Mq4.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C2.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

Lemma c2_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda84 : word) (MK k) rom) (mkst regs' (0xddab4 : word) (MK (k + 2)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_ddad0 D_ddad0 k.
stepn F_ddad4 D_ddad4.
stepb_ft F_ddad8 D_ddad8 ltac:(cond).
stepn F_ddadc D_ddadc.
stepb_ft F_ddae0 D_ddae0 ltac:(cond).
stepn F_ddae4 D_ddae4.
stepn F_ddae8 D_ddae8.
msb F_ddaec D_ddaec k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_ddaf0 D_ddaf0 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
stepn F_ddaf4 D_ddaf4.
stepn F_ddaf8 D_ddaf8.
stepn F_ddafc D_ddafc.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
(ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddab4 : word) (MK kk) rom)
(mkst regs' (0xddb14 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_ddb00 D_ddb00.
mlw F_ddb04 D_ddb04 (kk + 2)%Z.
mlw F_ddb08 D_ddb08 (kk + 6)%Z.
mlw F_ddb0c D_ddb0c (kk + 10)%Z.
mlw F_ddb10 D_ddb10 (kk + 14)%Z.
stepn F_ddb14 D_ddb14. stepn F_ddb18 D_ddb18. stepn F_ddb1c D_ddb1c.
stepn F_ddb20 D_ddb20. stepn F_ddb24 D_ddb24. stepn F_ddb28 D_ddb28.
stepn F_ddb2c D_ddb2c. stepn F_ddb30 D_ddb30. stepn F_ddb34 D_ddb34.
stepn F_ddb38 D_ddb38. stepn F_ddb3c D_ddb3c.
stepn F_ddb40 D_ddb40.
msw F_ddb44 D_ddb44 kk ltac:(m16).
msw F_ddb48 D_ddb48 (kk + 4)%Z ltac:(m16).
msw F_ddb4c D_ddb4c (kk + 8)%Z ltac:(m16).
msw F_ddb50 D_ddb50 (kk + 12)%Z ltac:(m16).
stepn F_ddb54 D_ddb54.
stepn F_ddb58 D_ddb58.
stepb_ft F_ddb5c D_ddb5c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddab4 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
/\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
+ eexists. split.
* stepn F_ddb00 D_ddb00.
mlw F_ddb04 D_ddb04 (kk + 2)%Z.
mlw F_ddb08 D_ddb08 (kk + 6)%Z.
mlw F_ddb0c D_ddb0c (kk + 10)%Z.
mlw F_ddb10 D_ddb10 (kk + 14)%Z.
stepn F_ddb14 D_ddb14. stepn F_ddb18 D_ddb18. stepn F_ddb1c D_ddb1c.
stepn F_ddb20 D_ddb20. stepn F_ddb24 D_ddb24. stepn F_ddb28 D_ddb28.
stepn F_ddb2c D_ddb2c. stepn F_ddb30 D_ddb30. stepn F_ddb34 D_ddb34.
stepn F_ddb38 D_ddb38. stepn F_ddb3c D_ddb3c.
stepn F_ddb40 D_ddb40.
msw F_ddb44 D_ddb44 kk ltac:(m16).
msw F_ddb48 D_ddb48 (kk + 4)%Z ltac:(m16).
msw F_ddb4c D_ddb4c (kk + 8)%Z ltac:(m16).
msw F_ddb50 D_ddb50 (kk + 12)%Z ltac:(m16).
stepn F_ddb54 D_ddb54.
stepn F_ddb58 D_ddb58.
stepb_tk F_ddb5c D_ddb5c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma c2_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps JOB6SEGS (mkst regs (0xddb14 : word) (MK kk) rom)
(mkst regs' (0xdddd0 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda70 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddb60 D_ddb60.
stepn F_ddb64 D_ddb64.
stepb_tk F_ddb68 D_ddb68 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddcbc : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddb60 D_ddb60.
stepn F_ddb64 D_ddb64.
stepb_ft F_ddb68 D_ddb68 ltac:(cond).
stepn F_ddb6c D_ddb6c.
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd48 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma c2_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps JOB6SEGS (mkst regs (0xdda84 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn.Mq0 Qrlk.Mq1 QJJu.Mq1 QiyH.Mq4.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C3.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

Lemma c3_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda84 : word) (MK k) rom) (mkst regs' (0xddbbc : word) (MK (k + 1)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_ddad0 D_ddad0 k.
stepn F_ddad4 D_ddad4.
stepb_tk F_ddad8 D_ddad8 ltac:(cond).
msb F_ddbf4 D_ddbf4 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
stepn F_ddbf8 D_ddbf8.
stepn F_ddbfc D_ddbfc.
stepn F_ddc00 D_ddc00.
stepn F_ddc04 D_ddc04.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
(ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddbbc : word) (MK kk) rom)
(mkst regs' (0xddc1c : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_ddc08 D_ddc08.
mlw F_ddc0c D_ddc0c (kk + 3)%Z.
mlw F_ddc10 D_ddc10 (kk + 7)%Z.
mlw F_ddc14 D_ddc14 (kk + 11)%Z.
mlw F_ddc18 D_ddc18 (kk + 15)%Z.
stepn F_ddc1c D_ddc1c. stepn F_ddc20 D_ddc20. stepn F_ddc24 D_ddc24.
stepn F_ddc28 D_ddc28. stepn F_ddc2c D_ddc2c. stepn F_ddc30 D_ddc30.
stepn F_ddc34 D_ddc34. stepn F_ddc38 D_ddc38. stepn F_ddc3c D_ddc3c.
stepn F_ddc40 D_ddc40. stepn F_ddc44 D_ddc44.
stepn F_ddc48 D_ddc48.
msw F_ddc4c D_ddc4c kk ltac:(m8).
msw F_ddc50 D_ddc50 (kk + 4)%Z ltac:(m8).
msw F_ddc54 D_ddc54 (kk + 8)%Z ltac:(m8).
msw F_ddc58 D_ddc58 (kk + 12)%Z ltac:(m8).
stepn F_ddc5c D_ddc5c.
stepn F_ddc60 D_ddc60.
stepb_ft F_ddc64 D_ddc64 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddbbc : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
/\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
+ eexists. split.
* stepn F_ddc08 D_ddc08.
mlw F_ddc0c D_ddc0c (kk + 3)%Z.
mlw F_ddc10 D_ddc10 (kk + 7)%Z.
mlw F_ddc14 D_ddc14 (kk + 11)%Z.
mlw F_ddc18 D_ddc18 (kk + 15)%Z.
stepn F_ddc1c D_ddc1c. stepn F_ddc20 D_ddc20. stepn F_ddc24 D_ddc24.
stepn F_ddc28 D_ddc28. stepn F_ddc2c D_ddc2c. stepn F_ddc30 D_ddc30.
stepn F_ddc34 D_ddc34. stepn F_ddc38 D_ddc38. stepn F_ddc3c D_ddc3c.
stepn F_ddc40 D_ddc40. stepn F_ddc44 D_ddc44.
stepn F_ddc48 D_ddc48.
msw F_ddc4c D_ddc4c kk ltac:(m8).
msw F_ddc50 D_ddc50 (kk + 4)%Z ltac:(m8).
msw F_ddc54 D_ddc54 (kk + 8)%Z ltac:(m8).
msw F_ddc58 D_ddc58 (kk + 12)%Z ltac:(m8).
stepn F_ddc5c D_ddc5c.
stepn F_ddc60 D_ddc60.
stepb_tk F_ddc64 D_ddc64 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Lemma c3_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps JOB6SEGS (mkst regs (0xddc1c : word) (MK kk) rom)
(mkst regs' (0xdddd0 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda70 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddc68 D_ddc68.
stepn F_ddc6c D_ddc6c.
stepb_tk F_ddc70 D_ddc70 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddcbc : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddc68 D_ddc68.
stepn F_ddc6c D_ddc6c.
stepb_ft F_ddc70 D_ddc70 ltac:(cond).
stepn F_ddc74 D_ddc74.
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddd48 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma c3_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps JOB6SEGS (mkst regs (0xdda84 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 QqZL.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

#[local] Notation JOB6SEGS := AsanUbsan.M.loaded_segments (only parsing).

Definition asan_popfree_head : Z := 0x447e0.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Lemma PF0 : fetch_word JOB6SEGS (Z_to_bv 64 asan_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word JOB6SEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments asan_popfree_head.
Proof.
apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

End Mqd.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

Definition AJO6 : atable :=
{| img_lo := 0x10000; img_hi := 0x645000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3de24; rw_lo := 0xe2000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x74f70; x_imemcpy := 0x74ef4; x_memset := 0xdb750; x_memcpy := 0xdb34c; x_memiszero := 0x754a0;
x_istrncpy := 0x7539c; x_sealed := 0x11adc; x_popfree := 0x445b4;
x_sniff := 1; sniff_tab := 1; sniff_cell := 1;
x_envscan := 0xcbccc; x_envscan_k := 0xcbcd8; x_pnscan := 0xcbd90; x_pnscan_k := 0xcbd9c;
stops_more := [0x42228; 0x4384c; 0x64cc8; 0x6b520; 0x6b534; 0x6b548; 0x70fec; 0x710bc; 0x7e5e8; 0x7f4f4; 0x7f684; 0x893dc] |}.

Definition AJO6_TEXT_LO : Z := 0x3de24.
Definition AJO6_TEXT_N : nat := 167200.
Definition ajo_init : acs := init_acs_of AJO6.
