(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02 YP09 YH00 YH03 YH02 YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2e YN05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma step_val_at : forall segs st regs (rd : reg) (V v : word) pc' mem rom,
RiscvSemantics.step segs st =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd V) pc' mem rom) ->
bv_eqb rd 0 = false -> V = v ->
RiscvSemantics.step segs st = MachineOk (mkst (regupd regs rd v) pc' mem rom).
Proof. intros * H Hrd HV. rewrite H, Hrd, HV. reflexivity. Qed.
Lemma msteps_pc : forall segs regs (pc pc' : word) mem rom st,
bv_unsigned pc = bv_unsigned pc' ->
msteps segs (mkst regs pc' mem rom) st -> msteps segs (mkst regs pc mem rom) st.
Proof. intros * E H. replace pc with pc' by (apply bv_eq; symmetry; exact E). exact H. Qed.
Lemma mst_refl_pc : forall segs regs (pc pc' : word) mem rom,
bv_unsigned pc = bv_unsigned pc' ->
msteps segs (mkst regs pc mem rom) (mkst regs pc' mem rom).
Proof. intros * E. replace pc' with pc by (apply bv_eq; exact E). apply mst_refl. Qed.
End d.
Ltac sva F0 D L vv tac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_val_at with (v := vv);
[ eapply L; [exact F | reflexivity | exact D] | reflexivity | tac ]
| step_simpl ].
Ltac svl F0 D L vv rtac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_val_at with (v := vv);
[ eapply L; [exact F | reflexivity | exact D | rtac .. ] | reflexivity | reflexivity ]
| step_simpl ].
Ltac seg_done := apply mst_refl_pc; vm_compute; reflexivity.
Ltac vz := gr; rwH; imm_norm;
rewrite ?vz_addi, ?vz_add, ?vz_sub, ?vz_mul;
first [ reflexivity | idtac ].
Ltac svsb F0 D aa vv bb atac vtac btac oktac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply YK0v.step_sb_at with (a := aa) (v := vv) (b := bb);
[ exact F | reflexivity | exact D | atac | vtac | btac | oktac ]
| step_simpl ].
Ltac svsh F0 D aa vv atac vtac oktac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sh_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | atac | vtac | oktac ]
| step_simpl ].
Ltac svsw F0 D aa vv atac vtac oktac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sw_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | atac | vtac | oktac ]
| step_simpl ].
Ltac svsd F0 D aa vv atac vtac oktac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | atac | vtac | oktac ]
| step_simpl ].
Ltac atac := gr; rwH; imm_norm; rewrite ?v_addi_lit; first [ reflexivity | f_equal; lia ].
Ltac brz :=
gr; rwH;
rewrite ?brz_eq, ?brz_ne, ?brz_ltu, ?brz_geu, ?brz_lt, ?brz_ge by lia;
rewrite ?s64_small by lia;
first [ reflexivity
| apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
| apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
| apply negb_true_iff; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia]
| apply negb_false_iff; first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia] ].
Ltac stepbtz F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | brz ]
| step_simpl ].
Ltac stepbfz F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | brz ]
| step_simpl ].
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma length_word_to_le_bytes n v : length (word_to_le_bytes n v) = n.
Proof. apply length_N_to_le_bytes. Qed.
Lemma bytes2_value : forall (lo hi : byte) c, bv_unsigned lo + 256 * bv_unsigned hi = c ->
bytes_le_to_Z [lo; hi] = bv_unsigned (Z64 c).
Proof.
intros lo hi c Hc. pose proof (u8_range lo). pose proof (u8_range hi).
cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_comm.
rewrite lor_add_high by lia. rewrite u64_of_Z by lia. lia.
Qed.
Section h.
Variables (mem rom : word -> option byte).
Variables (g M idx n ctr : Z).
Variables (last sc maplen : Z).
Variable cls : Z.
Variables clo chi : byte.
Variables (b3 b2lo b2hi : byte).
Definition bits : Z := bits_enc last sc maplen.
Definition mapped1 : bool := negb (maplen =? 0) && (last =? 0).
Definition stride : Z := if mapped1 then maplen * 4096 - 16 else cls * 16.
Hypothesis Hlast : 0 <= last < 32.
Hypothesis Hsc : 0 <= sc < 64.
Hypothesis Hmaplen : 0 <= maplen < 2 ^ 52.
Hypothesis Hg : 0 <= g /\ g + 40 <= 2 ^ 64.
Hypothesis Hbits : word_mem src0segs mem (g + 32) bits.
Hypothesis HM : word_mem src0segs mem (g + 16) M.
Hypothesis Hcls : mapped1 = false ->
sc < 48 /\
mbyte src0segs mem (src0_D_size_classes + 2 * sc) = Some clo /\
mbyte src0segs mem (src0_D_size_classes + 2 * sc + 1) = Some chi /\
bv_unsigned clo + 256 * bv_unsigned chi = cls.
Hypothesis Hctr : 0 <= ctr < 2 ^ 64.
Hypothesis Hidx : 0 <= idx < 32.
Hypothesis Hn : 0 <= n /\ n + 4 <= stride.
Hypothesis Hgeom : 16 <= M /\ M + 16 + stride * idx + stride <= 2 ^ 63.
Hypothesis Hsmall : stride * idx + (stride - 4 - n) < 2 ^ 20.
Definition h3 : Z := bv_unsigned b3.
Definition h16 : Z := bv_unsigned b2lo + 256 * bv_unsigned b2hi.
Definition start : Z := M + 16 + stride * idx.
Definition slack : Z := (stride - 4 - n) / 16.
Definition off0src : Z := if h3 =? 0 then ctr else h16 + 1.
Definition off0 : Z := Z.land off0src 255.
Definition off : Z := fold_off slack off0.
Definition q : Z := start + 16 * off.
Definition end_ : Z := start + stride - 4.
Definition reserved : Z := stride - 4 - 16 * off - n.
Definition code : Z := if 5 <=? reserved then 5 else reserved.
Definition hdr16v : Z := (stride * idx) / 16 + off.
Hypothesis Hc4 : mbyte src0segs mem (start - 4) = Some (Z_to_bv 8 0).
Hypothesis Hb3 : mbyte src0segs mem (start - 3) = Some b3.
Hypothesis Hb2lo : mbyte src0segs mem (start - 2) = Some b2lo.
Hypothesis Hb2hi : mbyte src0segs mem (start - 1) = Some b2hi.
Hypothesis HW : forall x, start - 4 <= x < end_ -> writable_at src0segs mem x.
Hypothesis Hdisj : g + 24 <= start - 4 \/ start + stride <= g + 16.
Definition memA : word -> option byte :=
if off =? 0 then mem
else wbytes (wbytes (wbytes mem (Z64 (start - 3)) [Z_to_bv 8 224])
(Z64 (start - 2)) (word_to_le_bytes 2 (Z64 off)))
(Z64 (q - 4)) [Z_to_bv 8 0].
Definition memB : word -> option byte :=
wbytes (wbytes memA (Z64 (q - 3)) [Z_to_bv 8 idx]) (Z64 (q - 2)) (word_to_le_bytes 2 (Z64 hdr16v)).
Definition memC : word -> option byte :=
if reserved =? 0 then memB
else let m6 := wbytes memB (Z64 (q + n)) [Z_to_bv 8 0] in
if reserved <? 5 then m6
else wbytes (wbytes m6 (Z64 (end_ - 5)) [Z_to_bv 8 0]) (Z64 (end_ - 4)) (word_to_le_bytes 4 (Z64 reserved)).
Definition memF : word -> option byte :=
wbytes memC (Z64 (q - 3)) [Z_to_bv 8 (idx + 32 * code)].
Definition eT0 : Z := add64 (sub64 stride n) (2 ^ 64 - 4).
Definition eT1 : Z := Z.shiftr eT0 4.
Definition eA3a : Z := Z.shiftr eT0 5.
Definition eA3b : Z := Z.lor eT1 eA3a.
Definition eT0c : Z := Z.shiftr eA3b 2.
Definition eA3d : Z := Z.lor eT0c eA3b.
Definition eT0e : Z := Z.shiftr eA3d 4.
Definition eA3f : Z := Z.lor eT0e eA3d.
Definition eA3g : Z := Z.land off0 eA3f.
Definition eA7h : Z := sltu eT1 eA3g.
Definition eT0i : Z := not64 eT1.
Definition eA7j : Z := negw eA7h.
Definition eA7k : Z := Z.land eA7j eT0i.
Definition eA7l : Z := addw eA7k eA3g.
Lemma off_machine_eq : enframe_off_machine stride n off0src = if off0 <=? eT1 then off0 else eA7l.
Proof.
unfold enframe_off_machine, eA7l, eA7k, eA7j, eT0i, eA7h, eA3g, eA3f, eT0e, eA3d, eT0c, eA3b, eA3a, eT1, eT0, off0.
cbv zeta. reflexivity.
Qed.
Lemma basic_facts :
0 <= stride * idx /\ 4 <= stride /\ 0 <= h3 < 256 /\ 0 <= h16 < 2 ^ 16 /\
32 <= start /\ start + stride <= 2 ^ 63 /\ 0 <= off0 < 256 /\ 0 <= off0src < 2 ^ 64.
Proof.
pose proof (u8_range b3) as B3. pose proof (u8_range b2lo) as B2. pose proof (u8_range b2hi) as B1.
assert (Hsi : 0 <= stride * idx) by nia.
assert (Hsrc : 0 <= off0src < 2 ^ 64).
{ unfold off0src, h3, h16. destruct (bv_unsigned b3 =? 0); lia. }
assert (Ho0 : 0 <= off0 < 256).
{ unfold off0. change 256 with (2 ^ 8). apply land_range_r; lia. }
unfold h3, h16, start. lia.
Qed.
Lemma stride_idx_nonneg : 0 <= stride * idx.
Proof. nia. Qed.
Lemma eT0_eq : eT0 = stride - 4 - n.
Proof. pose proof stride_idx_nonneg. unfold eT0. rewrite sub64_small, add64_neg_imm by lia. lia. Qed.
Lemma eT1_eq : eT1 = slack.
Proof. unfold eT1, slack. rewrite eT0_eq, Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma slack_range : 0 <= slack < 2 ^ 31.
Proof. pose proof stride_idx_nonneg. unfold slack. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma off_facts : enframe_off_machine stride n off0src = off /\ 0 <= off <= slack /\ off <= off0.
Proof.
pose proof basic_facts as (? & ? & ? & ? & ? & ? & ? & ?).
destruct (enframe_off_ok' stride n off0src) as [E R]; unfold IB, UNIT in *; try lia.
unfold off, slack, off0. rewrite <- E. split; [reflexivity|]. split; [exact R|].
rewrite E. apply fold_off_le; [| apply Z.div_pos; lia].
change 256 with (2 ^ 8) in *. apply Z.land_nonneg. right. lia.
Qed.
Lemma geom_facts : 0 <= off <= 255 /\ 16 * off + n + 4 <= stride /\ q = start + 16 * off /\
end_ = start + stride - 4 /\ 0 <= reserved /\ q + n + reserved = end_ /\ 0 <= slack.
Proof.
pose proof basic_facts as (Hsi & Hs4 & Hh3 & Hh16 & Hst & Hst' & Ho0 & Hsrc).
pose proof off_facts as (_ & Roff & Ro0). pose proof slack_range.
assert (16 * slack <= stride - 4 - n) by (unfold slack; apply Z.mul_div_le; lia).
unfold q, end_, reserved. lia.
Qed.
Lemma e_ranges :
0 <= eT0 < 2 ^ 64 /\ 0 <= eT1 < 2 ^ 64 /\ 0 <= eA3a < 2 ^ 64 /\ 0 <= eA3b < 2 ^ 64 /\
0 <= eT0c < 2 ^ 64 /\ 0 <= eA3d < 2 ^ 64 /\ 0 <= eT0e < 2 ^ 64 /\ 0 <= eA3f < 2 ^ 64 /\
0 <= eA3g < 2 ^ 64 /\ 0 <= eA7h < 2 ^ 64 /\ 0 <= eT0i < 2 ^ 64 /\ 0 <= eA7j < 2 ^ 64 /\
0 <= eA7k < 2 ^ 64 /\ 0 <= eA7l < 2 ^ 64.
Proof.
pose proof basic_facts as (? & ? & ? & ? & ? & ? & ? & ?).
assert (R0 : 0 <= eT0 < 2 ^ 64) by apply add64_range.
assert (R1 : 0 <= eT1 < 2 ^ 64) by (unfold eT1; apply shiftr_range64; lia).
assert (R2 : 0 <= eA3a < 2 ^ 64) by (unfold eA3a; apply shiftr_range64; lia).
assert (R3 : 0 <= eA3b < 2 ^ 64) by (unfold eA3b; apply lor_range64; lia).
assert (R4 : 0 <= eT0c < 2 ^ 64) by (unfold eT0c; apply shiftr_range64; lia).
assert (R5 : 0 <= eA3d < 2 ^ 64) by (unfold eA3d; apply lor_range64; lia).
assert (R6 : 0 <= eT0e < 2 ^ 64) by (unfold eT0e; apply shiftr_range64; lia).
assert (R7 : 0 <= eA3f < 2 ^ 64) by (unfold eA3f; apply lor_range64; lia).
assert (R8 : 0 <= eA3g < 2 ^ 64) by (unfold eA3g; apply land_range64; lia).
assert (R9 : 0 <= eA7h < 2 ^ 64) by (unfold eA7h; apply sltu_range).
assert (R10 : 0 <= eT0i < 2 ^ 64) by (unfold eT0i; apply not64_range).
assert (R11 : 0 <= eA7j < 2 ^ 64) by (unfold eA7j, negw; apply sx32_range).
assert (R12 : 0 <= eA7k < 2 ^ 64) by (unfold eA7k; apply land_range64; lia).
assert (R13 : 0 <= eA7l < 2 ^ 64) by (unfold eA7l, addw; apply sx32_range).
repeat split; lia.
Qed.
Lemma bits_range : 0 <= bits < 2 ^ 64.
Proof. unfold bits. split; [apply bits_nonneg; lia | apply bits_lt64; lia]. Qed.
Lemma seg1 : forall regs,
getr regs 10 = Z64 g ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0x0)) mem rom)
(mkst regs' (Z64 (src0_A_enframe + 0x40)) mem rom) /\
getr regs' 14 = Z64 stride /\
(forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10. pose proof bits_range as Hb.
destruct mapped1 eqn:Em.
-
assert (Es : stride = maplen * 4096 - 16) by (unfold stride; rewrite Em; reflexivity).
unfold mapped1 in Em. apply andb_prop in Em as [E1 E2].
apply negb_true_iff in E1. apply Z.eqb_neq in E1. apply Z.eqb_eq in E2.
eexists. split; [|split].
+ norm_pc.
svl FN_000 DN_000 step_ld (Z64 bits)
ltac:(first [ gr; rwH; imm_norm; rewrite vz_addi; rewrite add64_small by lia; apply word_mem_rdn; exact Hbits
| apply word_mem_value_mod ]).
sva FN_004 DN_004 step_srli (Z64 maplen)
ltac:(gr; imm_norm; rewrite vz_srli by lia; f_equal; apply bits_shiftr12; lia).
stepbf FN_008 DN_008.
sva FN_00c DN_00c step_andi (Z64 last)
ltac:(gr; imm_norm; rewrite vz_andi by lia; f_equal; apply bits_land31; lia).
stepbf FN_010 DN_010.
sva FN_014 DN_014 step_lui (Z64 (2 ^ 64 - 4096))
ltac:(imm_norm; unfold v_lui; apply Z64_eq_mod; vm_compute; reflexivity).
sva FN_018 DN_018 step_and (Z64 (maplen * 4096))
ltac:(gr; rewrite vz_and by lia; f_equal; apply bits_maplen_bytes; lia).
sva FN_01c DN_01c step_addi (Z64 (maplen * 4096 - 16))
ltac:(gr; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepj' FN_020 DN_020.
seg_done.
+ gr. rewrite Es. reflexivity.
+ intros r H14 H15. rewrite !getr_other by assumption. reflexivity.
-
assert (Es : stride = cls * 16) by (unfold stride; rewrite Em; reflexivity).
destruct (Hcls eq_refl) as (Hsc48 & Hlo & Hhi & Hcl).
pose proof (u8_range clo). pose proof (u8_range chi).
assert (TAIL : forall regs1,
getr regs1 14 = Z64 bits ->
(forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs1 r = getr regs r) ->
exists regs',
msteps src0segs (mkst regs1 (Z64 (src0_A_enframe + 0x24)) mem rom)
(mkst regs' (Z64 (src0_A_enframe + 0x40)) mem rom) /\
getr regs' 14 = Z64 stride /\
(forall r : reg, r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r)).
{ intros regs1 H14 Hfr. eexists. split; [|split].
- norm_pc.
sva FN_024 DN_024 step_srli (Z64 (Z.shiftr bits 5))
ltac:(gr; rwH; imm_norm; rewrite vz_srli by lia; reflexivity).
let F := litF FN_028 in stepi F DN_028.
sva FN_02c DN_02c step_andi (Z64 (2 * sc))
ltac:(gr; imm_norm; rewrite vz_andi by (apply shiftr_range64; lia); f_equal; apply bits_2sc; lia).
sva FN_030 DN_030 step_addi (Z64 src0_D_size_classes)
ltac:(gr; unfold v_auipc; rewrite v_addi_lit; apply bv_eq; vm_compute; reflexivity).
sva FN_034 DN_034 step_add (Z64 (src0_D_size_classes + 2 * sc))
ltac:(gr; rewrite v_add_lit; reflexivity).
svl FN_038 DN_038 step_lhu (Z64 cls)
ltac:(first [ gr; imm_norm; rewrite v_addi_lit, Z.add_0_r; apply rdn2_mbyte; [exact Hlo | exact Hhi]
| apply bytes2_value; exact Hcl ]).
sva FN_03c DN_03c step_slli (Z64 (cls * 16))
ltac:(gr; imm_norm; rewrite vz_slli by lia; f_equal; apply sll64_small; lia).
seg_done.
- gr. rewrite Es. reflexivity.
- intros r Hra Hrb. rewrite !getr_other by assumption. apply Hfr; assumption. }
unfold mapped1 in Em.
destruct (Z.eqb_spec maplen 0) as [E1|E1].
+
edestruct TAIL as (regs' & Hms & H14 & Hfr); cycle 2.
{ exists regs'. split; [|split; [exact H14 | exact Hfr]].
norm_pc.
svl FN_000 DN_000 step_ld (Z64 bits)
ltac:(first [ gr; rwH; imm_norm; rewrite vz_addi; rewrite add64_small by lia; apply word_mem_rdn; exact Hbits
| apply word_mem_value_mod ]).
sva FN_004 DN_004 step_srli (Z64 maplen)
ltac:(gr; imm_norm; rewrite vz_srli by lia; f_equal; apply bits_shiftr12; lia).
stepbt FN_008 DN_008.
eapply msteps_pc; [|exact Hms]. vm_compute; reflexivity. }
* gr. reflexivity.
* intros r Hra Hrb. rewrite !getr_other by assumption. reflexivity.
+
cbn [negb andb] in Em. apply Z.eqb_neq in Em.
edestruct TAIL as (regs' & Hms & H14 & Hfr); cycle 2.
{ exists regs'. split; [|split; [exact H14 | exact Hfr]].
norm_pc.
svl FN_000 DN_000 step_ld (Z64 bits)
ltac:(first [ gr; rwH; imm_norm; rewrite vz_addi; rewrite add64_small by lia; apply word_mem_rdn; exact Hbits
| apply word_mem_value_mod ]).
sva FN_004 DN_004 step_srli (Z64 maplen)
ltac:(gr; imm_norm; rewrite vz_srli by lia; f_equal; apply bits_shiftr12; lia).
stepbf FN_008 DN_008.
sva FN_00c DN_00c step_andi (Z64 last)
ltac:(gr; imm_norm; rewrite vz_andi by lia; f_equal; apply bits_land31; lia).
stepbt FN_010 DN_010.
eapply msteps_pc; [|exact Hms]. vm_compute; reflexivity. }
* gr. reflexivity.
* intros r Hra Hrb. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma seg2 : forall regs,
getr regs 10 = Z64 g -> getr regs 11 = Z64 idx -> getr regs 12 = Z64 n ->
getr regs 13 = Z64 ctr -> getr regs 14 = Z64 stride ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0x40)) mem rom)
(mkst regs' (Z64 (src0_A_enframe + 0x68)) mem rom) /\
getr regs' 16 = Z64 M /\ getr regs' 15 = Z64 start /\ getr regs' 17 = Z64 h3 /\
getr regs' 5 = Z64 eT0 /\ getr regs' 13 = Z64 off0src /\
(forall r : reg, r <> 5%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H11 H12 H13 H14.
pose proof basic_facts as (Hsi & Hs4 & Hh3 & Hh16 & Hst & Hst' & Ho0 & _).
pose proof (u8_range b3) as Hb3r.
assert (HEAD : exists regs1,
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0x40)) mem rom)
(mkst regs1 (Z64 (src0_A_enframe + 0x5c)) mem rom) /\
regs1 = regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
16 (Z64 M)) 15 (Z64 (stride * idx))) 15 (Z64 (start - 16))) 17 (Z64 h3))
5 (Z64 (sub64 stride n))) 5 (Z64 eT0)) 15 (Z64 start)).
{ eexists. split; [|reflexivity]. norm_pc.
svl FN_040 DN_040 step_ld (Z64 M)
ltac:(first [ gr; rwH; imm_norm; rewrite vz_addi; rewrite add64_small by lia; apply word_mem_rdn; exact HM
| apply word_mem_value_mod ]).
sva FN_044 DN_044 step_mul (Z64 (stride * idx))
ltac:(gr; rwH; rewrite vz_mul; f_equal; apply mul64_small; lia).
sva FN_048 DN_048 step_add (Z64 (start - 16))
ltac:(gr; rewrite v_add_lit; f_equal; unfold start; lia).
svl FN_04c DN_04c step_lbu (Z64 h3)
ltac:(gr; imm_norm; rewrite v_addi_lit; replace (start - 16 + 13) with (start - 3) by lia; apply rdn1_mbyte; exact Hb3).
sva FN_050 DN_050 step_sub (Z64 (sub64 stride n))
ltac:(gr; rwH; rewrite vz_sub; reflexivity).
sva FN_054 DN_054 step_addi (Z64 eT0)
ltac:(gr; imm_norm; rewrite v_addi_lit, Z64_add64_wrap; unfold eT0; do 2 f_equal; lia).
sva FN_058 DN_058 step_addi (Z64 start)
ltac:(gr; imm_norm; rewrite v_addi_lit; f_equal; lia).
seg_done. }
destruct HEAD as (regs1 & Hms1 & E1).
destruct (Z.eqb_spec h3 0) as [Eh3 | Eh3].
-
exists regs1. subst regs1. split; [| unfold off0src; rewrite (proj2 (Z.eqb_eq _ _) Eh3); repeat split; try (gr; rwH; reflexivity)].
2:{ intros r ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity. }
eapply msteps_trans; [exact Hms1|]. norm_pc.
stepbt FN_05c DN_05c.
seg_done.
-
eexists. split.
{ eapply msteps_trans; [exact Hms1|]. subst regs1. norm_pc.
stepbf FN_05c DN_05c.
svl FN_060 DN_060 step_lhu (Z64 h16)
ltac:(first [ gr; imm_norm; rewrite v_addi_lit; replace (start + -2) with (start - 2) by lia;
apply rdn2_mbyte; [exact Hb2lo | replace (start - 2 + 1) with (start - 1) by lia; exact Hb2hi]
| apply bytes2_value; reflexivity ]).
sva FN_064 DN_064 step_addi (Z64 (h16 + 1))
ltac:(gr; imm_norm; rewrite v_addi_lit; reflexivity).
seg_done. }
subst regs1. unfold off0src. rewrite (proj2 (Z.eqb_neq _ _) Eh3).
repeat split; try (gr; rwH; reflexivity).
intros r ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma seg3 : forall regs,
getr regs 13 = Z64 off0src -> getr regs 5 = Z64 eT0 -> getr regs 15 = Z64 start ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0x68)) mem rom)
(mkst regs' (Z64 (src0_A_enframe + 0xb8)) mem rom) /\
getr regs' 17 = Z64 off /\ getr regs' 6 = Z64 slack /\ getr regs' 7 = Z64 0 /\
(forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 13%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs H13 H5 H15.
pose proof basic_facts as (Hsi & Hs4 & Hh3 & Hh16 & Hst & Hst' & Ho0 & Hsrc).
pose proof e_ranges as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
pose proof off_facts as (Eoff & Roff & _). rewrite off_machine_eq in Eoff.
pose proof eT1_eq as E1.
assert (HEAD : exists regs1,
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0x68)) mem rom)
(mkst regs1 (Z64 (src0_A_enframe + 0x7c)) mem rom) /\
regs1 = regupd (regupd (regupd regs 7 (Z64 0)) 6 (Z64 eT1)) 17 (Z64 off0)).
{ eexists. split; [|reflexivity]. norm_pc.
svl FN_068 DN_068 step_lbu (Z64 0)
ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; replace (start + -4) with (start - 4) by lia; apply rdn1_mbyte; exact Hc4).
sva FN_06c DN_06c step_srli (Z64 eT1)
ltac:(gr; rwH; imm_norm; rewrite vz_srli by lia; reflexivity).
sva FN_070 DN_070 step_andi (Z64 off0)
ltac:(gr; rwH; imm_norm; rewrite vz_andi by lia; reflexivity).
stepbt FN_074 DN_074.
seg_done. }
destruct HEAD as (regs1 & Hms1 & E1r).
destruct (off0 <=? eT1) eqn:Ec.
-
apply Z.leb_le in Ec.
exists regs1. split.
{ eapply msteps_trans; [exact Hms1|]. subst regs1. norm_pc.
stepbt FN_07c DN_07c.
seg_done. }
subst regs1. repeat split; try (gr; rwH; congruence).
intros r ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
-
apply Z.leb_gt in Ec.
eexists. split.
{ eapply msteps_trans; [exact Hms1|]. subst regs1. norm_pc.
stepbf FN_07c DN_07c.
sva FN_080 DN_080 step_srli (Z64 eA3a) ltac:(gr; rwH; imm_norm; rewrite vz_srli by lia; reflexivity).
sva FN_084 DN_084 step_or (Z64 eA3b) ltac:(gr; rewrite vz_or by lia; reflexivity).
sva FN_088 DN_088 step_srli (Z64 eT0c) ltac:(gr; imm_norm; rewrite vz_srli by lia; reflexivity).
sva FN_08c DN_08c step_or (Z64 eA3d) ltac:(gr; rewrite vz_or by lia; reflexivity).
sva FN_090 DN_090 step_srli (Z64 eT0e) ltac:(gr; imm_norm; rewrite vz_srli by lia; reflexivity).
sva FN_094 DN_094 step_or (Z64 eA3f) ltac:(gr; rewrite vz_or by lia; reflexivity).
sva FN_098 DN_098 step_and (Z64 eA3g) ltac:(gr; rewrite vz_and by lia; reflexivity).
sva FN_09c DN_09c step_sltu (Z64 eA7h) ltac:(gr; rewrite vz_sltu by lia; reflexivity).
sva FN_0a0 DN_0a0 step_xori (Z64 eT0i) ltac:(gr; imm_norm; rewrite vz_not by lia; reflexivity).
sva FN_0a4 DN_0a4 step_subw (Z64 eA7j) ltac:(gr; rewrite vz_negw by lia; reflexivity).
sva FN_0a8 DN_0a8 step_and (Z64 eA7k) ltac:(gr; rewrite vz_and by lia; reflexivity).
sva FN_0ac DN_0ac step_addw (Z64 eA7l) ltac:(gr; rewrite vz_addw by lia; reflexivity).
stepbt FN_0b0 DN_0b0.
seg_done. }
subst regs1. repeat split; try (gr; rwH; congruence).
intros r ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Ltac wtac := apply store_ok_writable; [lia | cbn [length]; lia |
intros x Hx; repeat apply wbytes_writable; apply HW; cbn [length] in Hx; lia].
Lemma seg4 : forall regs,
getr regs 10 = Z64 g -> getr regs 15 = Z64 start -> getr regs 16 = Z64 M -> getr regs 17 = Z64 off ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0xb8)) mem rom)
(mkst regs' (Z64 (src0_A_enframe + 0xdc)) memA rom) /\
getr regs' 13 = Z64 q /\ getr regs' 16 = Z64 M /\
(forall r : reg, r <> 13%bv -> r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H15 H16 H17.
pose proof basic_facts as (Hsi & Hs4 & Hh3 & Hh16 & Hst & Hst' & Ho0 & Hsrc).
pose proof geom_facts as (Go & Gs & Gq & Ge & Gr & Gqe & Gsl).
unfold memA.
destruct (Z.eqb_spec off 0) as [Eo | Eo].
-
eexists. split.
{ norm_pc.
sva FN_0b8 DN_0b8 step_addi (Z64 q) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepbt FN_0bc DN_0bc.
seg_done. }
repeat split; try (gr; rwH; reflexivity).
intros r ? ?. rewrite !getr_other by assumption. reflexivity.
- eexists. split.
{ norm_pc.
sva FN_0b8 DN_0b8 step_addi (Z64 start) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepbf FN_0bc DN_0bc.
sva FN_0c0 DN_0c0 step_addi (Z64 (2 ^ 64 - 32)) ltac:(gr; imm_norm; rewrite v_addi_lit; apply Z64_eq_mod; reflexivity).
sva FN_0c4 DN_0c4 step_slliw (Z64 (16 * off))
ltac:(gr; rwH; imm_norm; rewrite vz_slliw by lia; f_equal; apply enframe_off_bytes; lia).
sva FN_0c8 DN_0c8 step_add (Z64 q) ltac:(gr; rwH; rewrite v_add_lit; f_equal; lia).
svsb FN_0cc DN_0cc (Z64 (start - 3)) (Z64 (2 ^ 64 - 32)) (Z_to_bv 8 224)
atac ltac:(gr; reflexivity) ltac:(apply bv_eq; vm_compute; reflexivity) wtac.
svsh FN_0d0 DN_0d0 (Z64 (start - 2)) (Z64 off) atac ltac:(gr; rwH; reflexivity) wtac.
svsb FN_0d4 DN_0d4 (Z64 (q - 4)) (Z64 0) (Z_to_bv 8 0)
atac ltac:(gr; reflexivity) ltac:(reflexivity) wtac.
svl FN_0d8 DN_0d8 step_ld (Z64 M)
ltac:(first
[ gr; rwH; imm_norm; rewrite v_addi_lit;
rewrite !rdn_wbytes_out by (cbn [length]; rewrite ?length_word_to_le_bytes; rewrite !u64_of_Z by lia; lia);
apply word_mem_rdn; exact HM
| apply word_mem_value_mod ]).
seg_done. }
repeat split; try (gr; rwH; reflexivity).
intros r ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma code_range : 0 <= code <= 5 /\ code <= reserved.
Proof. pose proof geom_facts as (_ & _ & _ & _ & Gr & _). unfold code. destruct (5 <=? reserved) eqn:E; [apply Z.leb_le in E|apply Z.leb_gt in E]; lia. Qed.
Lemma hdr16_facts : 16 <= q - M < 2 ^ 31 /\ Z.shiftr (q - M - 16) 4 = hdr16v /\ 0 <= hdr16v < 2 ^ 16.
Proof.
pose proof basic_facts as (Hsi & Hs4 & _). pose proof geom_facts as (Go & Gs & Gq & Ge & Gr & Gqe & Gsl).
pose proof off_facts as (_ & Roff & _).
assert (E : q - M - 16 = stride * idx + 16 * off) by (rewrite Gq; unfold start; lia).
assert (Hle : 16 * slack <= stride - 4 - n) by (unfold slack; apply Z.mul_div_le; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. rewrite E. unfold hdr16v.
replace (16 * off) with (off * 16) by lia. rewrite Z.div_add by lia.
assert (0 <= stride * idx / 16) by (apply Z.div_pos; lia).
assert (stride * idx / 16 + off < 2 ^ 16).
{ apply (Z.le_lt_trans _ ((stride * idx + (stride - 4 - n)) / 16)).
- rewrite <- Z.div_add by lia. apply Z.div_le_mono; lia.
- apply Z.div_lt_upper_bound; lia. }
lia.
Qed.
Lemma seg5 : forall regs,
getr regs 11 = Z64 idx -> getr regs 12 = Z64 n -> getr regs 13 = Z64 q ->
getr regs 14 = Z64 stride -> getr regs 15 = Z64 start -> getr regs 16 = Z64 M ->
exists regs',
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0xdc)) memA rom)
(mkst regs' (v_jalr (getr regs 1) 0) memF rom) /\
getr regs' 10 = Z64 q /\
(forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
getr regs' r = getr regs r).
Proof.
intros regs H11 H12 H13 H14 H15 H16.
pose proof basic_facts as (Hsi & Hs4 & Hh3 & Hh16 & Hst & Hst' & Ho0 & Hsrc).
pose proof geom_facts as (Go & Gs & Gq & Ge & Gr & Gqe & Gsl).
pose proof code_range as [Hc Hcr]. pose proof hdr16_facts as (HqM & Eh16 & Rh16).
assert (Rres : reserved < 2 ^ 31) by (unfold reserved; lia).
assert (HWA : forall x, start - 4 <= x < end_ -> writable_at src0segs memA x).
{ intros x Hx. unfold memA. destruct (off =? 0); repeat apply wbytes_writable; apply HW; exact Hx. }
assert (HEAD : exists regs1,
msteps src0segs (mkst regs (Z64 (src0_A_enframe + 0xdc)) memA rom)
(mkst regs1 (Z64 (src0_A_enframe + 0x100)) memB rom) /\
regs1 = regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
14 (Z64 (start + stride))) 15 (Z64 (q - M))) 12 (Z64 (q + n))) 10 (Z64 end_))
15 (Z64 (q - M - 16))) 15 (Z64 hdr16v)) 16 (Z64 reserved)).
{ eexists. split; [|reflexivity]. unfold memB. norm_pc.
sva FN_0dc DN_0dc step_add (Z64 (start + stride)) ltac:(gr; rwH; rewrite v_add_lit; reflexivity).
sva FN_0e0 DN_0e0 step_subw (Z64 (q - M)) ltac:(gr; rwH; rewrite vz_subw by lia; f_equal; apply subw_small; lia).
sva FN_0e4 DN_0e4 step_add (Z64 (q + n)) ltac:(gr; rwH; rewrite v_add_lit; f_equal; lia).
sva FN_0e8 DN_0e8 step_addi (Z64 end_) ltac:(gr; imm_norm; rewrite v_addi_lit; f_equal; lia).
sva FN_0ec DN_0ec step_addi (Z64 (q - M - 16)) ltac:(gr; imm_norm; rewrite v_addi_lit; f_equal; lia).
sva FN_0f0 DN_0f0 step_srli (Z64 hdr16v) ltac:(gr; imm_norm; rewrite vz_srli by lia; f_equal; exact Eh16).
sva FN_0f4 DN_0f4 step_subw (Z64 reserved) ltac:(gr; rewrite vz_subw by lia; f_equal; rewrite subw_small by lia; lia).
svsb FN_0f8 DN_0f8 (Z64 (q - 3)) (Z64 idx) (Z_to_bv 8 idx)
atac ltac:(gr; rwH; reflexivity) ltac:(rewrite u64_of_Z by lia; reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; apply HWA; cbn [length] in Hx; lia]).
svsh FN_0fc DN_0fc (Z64 (q - 2)) (Z64 hdr16v) atac ltac:(gr; reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; repeat apply wbytes_writable; apply HWA; cbn [length] in Hx; lia]).
seg_done. }
destruct HEAD as (regs1 & Hms1 & E1r).
assert (TAIL : forall regs2,
getr regs2 10 = Z64 code -> getr regs2 13 = Z64 q ->
exists regs3,
msteps src0segs (mkst regs2 (Z64 (src0_A_enframe + 0x134)) memC rom)
(mkst regs3 (v_jalr (getr regs2 1) 0) memF rom) /\
regs3 = regupd (regupd (regupd (regupd (regupd regs2
11 (Z64 (bv_unsigned (Z_to_bv 8 idx)))) 11 (Z64 (Z.land idx 31))) 10 (Z64 (sll64 code 5)))
10 (Z64 (idx + 32 * code))) 10 (Z64 q)).
{ intros regs2 H10' H13'.
assert (Hrd : mbyte src0segs memC (q - 3) = Some (Z_to_bv 8 idx)).
{ unfold memC, memB.
destruct (reserved =? 0) eqn:Er'; [| destruct (reserved <? 5) eqn:Er5'];
[ | apply Z.eqb_neq in Er'; apply Z.ltb_lt in Er5' | apply Z.eqb_neq in Er'; apply Z.ltb_ge in Er5' ];
cbv zeta;
rewrite ?wbytes_mbyte_out by (rewrite ?length_word_to_le_bytes; cbn [length]; lia);
rewrite wbytes_mbyte_in by (cbn [length]; lia);
replace (q - 3 - (q - 3)) with 0 by lia; reflexivity. }
assert (Eidx : bv_unsigned (Z_to_bv 8 idx) = idx).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. }
eexists. split; [|reflexivity]. unfold memF. norm_pc.
svl FN_134 DN_134 step_lbu (Z64 (bv_unsigned (Z_to_bv 8 idx)))
ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; replace (q + -3) with (q - 3) by lia; apply rdn1_mbyte; exact Hrd).
sva FN_138 DN_138 step_andi (Z64 (Z.land idx 31)) ltac:(gr; imm_norm; rewrite Eidx, vz_andi by lia; reflexivity).
sva FN_13c DN_13c step_slli (Z64 (sll64 code 5)) ltac:(gr; rwH; imm_norm; rewrite vz_slli by lia; reflexivity).
sva FN_140 DN_140 step_or (Z64 (idx + 32 * code))
ltac:(gr; rewrite vz_or by (first [apply sll64_range | change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound idx (2 ^ 5)); lia]);
f_equal; apply (proj1 (enframe_hdr3 idx code ltac:(lia) ltac:(lia)))).
svsb FN_144 DN_144 (Z64 (q - 3)) (Z64 (idx + 32 * code)) (Z_to_bv 8 (idx + 32 * code))
atac ltac:(gr; reflexivity) ltac:(rewrite u64_of_Z by lia; reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; unfold memC, memB;
destruct (reserved =? 0); [| destruct (reserved <? 5)]; repeat apply wbytes_writable; apply HWA; cbn [length] in Hx; lia]).
sva FN_148 DN_148 step_addi (Z64 q) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; lia).
stepret FN_14c DN_14c.
gr. apply mst_refl. }
destruct (Z.eqb_spec reserved 0) as [Er | Er].
-
assert (Ec : code = 0) by (unfold code; rewrite Er; reflexivity).
edestruct (TAIL (regupd regs1 10 (Z64 0))) as (regs3 & Hms3 & E3).
{ gr. rewrite Ec. reflexivity. } { subst regs1. gr. rwH. reflexivity. }
exists regs3. split; [|split].
+ eapply msteps_trans; [exact Hms1|]. subst regs1. norm_pc.
stepbtz FN_100 DN_100.
sva FN_128 DN_128 step_addi (Z64 0) ltac:(gr; imm_norm; reflexivity).
stepj' FN_12c DN_12c.
eapply msteps_pc; [| unfold memC in Hms3; rewrite (proj2 (Z.eqb_eq _ _) Er) in Hms3; revert Hms3; gr; intros Hms3; exact Hms3].
vm_compute; reflexivity.
+ subst regs3 regs1. gr. reflexivity.
+ subst regs3 regs1. intros r ? ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
- assert (Eneg : add64 end_ (negw reserved) = q + n).
{ rewrite (proj1 (enframe_end_minus_reserved end_ reserved ltac:(lia) ltac:(lia))). lia. }
set (m6 := wbytes memB (Z64 (q + n)) [Z_to_bv 8 0]).
assert (MID : exists regs2,
msteps src0segs (mkst regs1 (Z64 (src0_A_enframe + 0x100)) memB rom)
(mkst regs2 (Z64 (src0_A_enframe + 0x118)) m6 rom) /\
regs2 = regupd (regupd (regupd (regupd regs1
11 (Z64 reserved)) 12 (Z64 (negw reserved))) 12 (Z64 (q + n))) 10 (Z64 5)).
{ eexists. split; [|reflexivity]. subst regs1 m6. norm_pc.
stepbfz FN_100 DN_100.
sva FN_104 DN_104 step_subw (Z64 reserved) ltac:(gr; rewrite vz_subw by lia; f_equal; rewrite subw_small by lia; lia).
sva FN_108 DN_108 step_subw (Z64 (negw reserved)) ltac:(gr; rewrite vz_negw by lia; reflexivity).
sva FN_10c DN_10c step_add (Z64 (q + n)) ltac:(gr; rewrite vz_add; f_equal; exact Eneg).
sva FN_110 DN_110 step_addi (Z64 5) ltac:(gr; imm_norm; reflexivity).
svsb FN_114 DN_114 (Z64 (q + n)) (Z64 0) (Z_to_bv 8 0)
atac ltac:(gr; reflexivity) ltac:(reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; unfold memB; repeat apply wbytes_writable; apply HWA; cbn [length] in Hx; lia]).
seg_done. }
destruct MID as (regs2 & Hms2 & E2r).
destruct (Z.ltb_spec reserved 5) as [Er5 | Er5].
+
assert (Ec : code = reserved) by (unfold code; rewrite (proj2 (Z.leb_gt _ _) Er5); reflexivity).
edestruct (TAIL (regupd regs2 10 (Z64 reserved))) as (regs3 & Hms3 & E3).
{ gr. rewrite Ec. reflexivity. } { subst regs2 regs1. gr. rwH. reflexivity. }
exists regs3. split; [|split].
* eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. subst regs2 regs1. norm_pc.
stepbtz FN_118 DN_118.
sva FN_130 DN_130 step_addi (Z64 reserved) ltac:(gr; imm_norm; rewrite v_addi_lit; f_equal; lia).
eapply msteps_pc; [| unfold memC in Hms3; rewrite (proj2 (Z.eqb_neq _ _) Er), (proj2 (Z.ltb_lt _ _) Er5) in Hms3;
revert Hms3; gr; intros Hms3; exact Hms3].
vm_compute; reflexivity.
* subst regs3 regs2 regs1. gr. reflexivity.
* subst regs3 regs2 regs1. intros r ? ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
+
assert (Ec : code = 5) by (unfold code; rewrite (proj2 (Z.leb_le _ _) Er5); reflexivity).
edestruct (TAIL regs2) as (regs3 & Hms3 & E3).
{ subst regs2. gr. rewrite Ec. reflexivity. } { subst regs2 regs1. gr. rwH. reflexivity. }
exists regs3. split; [|split].
* eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. subst regs2 regs1. norm_pc.
stepbfz FN_118 DN_118.
svsb FN_11c DN_11c (Z64 (end_ - 5)) (Z64 0) (Z_to_bv 8 0)
atac ltac:(gr; reflexivity) ltac:(reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; subst m6; unfold memB; repeat apply wbytes_writable; apply HWA; cbn [length] in Hx; lia]).
svsw FN_120 DN_120 (Z64 (end_ - 4)) (Z64 reserved) atac ltac:(gr; reflexivity)
ltac:(apply store_ok_writable; [lia | cbn [length]; lia | intros x Hx; subst m6; unfold memB; repeat apply wbytes_writable; apply HWA; cbn [length] in Hx; lia]).
stepj' FN_124 DN_124.
eapply msteps_pc; [| unfold memC in Hms3; rewrite (proj2 (Z.eqb_neq _ _) Er), (proj2 (Z.ltb_ge _ _) Er5) in Hms3;
revert Hms3; gr; intros Hms3; exact Hms3].
vm_compute; reflexivity.
* subst regs3 regs2 regs1. gr. reflexivity.
* subst regs3 regs2 regs1. intros r ? ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Definition written (x : Z) : Prop :=
(start - 4 <= x < start) \/ (q - 4 <= x < q) \/ (q + n <= x < end_).
Ltac cond_tf :=
match goal with
| |- context [if (?a <=? ?x) && (?y <? ?b) then _ else _] =>
first [ replace ((a <=? x) && (y <? b)) with false
by (symmetry; apply andb_false_iff; first [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia])
| replace ((a <=? x) && (y <? b)) with true
by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia])
| destruct ((a <=? x) && (y <? b)) ];
cbv beta iota
end.
Ltac mem_cases :=
pose proof basic_facts as (Hsi & Hs4 & Hh3 & Hh16 & Hst & Hst' & Ho0 & Hsrc);
pose proof geom_facts as (Go & Gs & Gq & Ge & Gr & Gqe & Gsl);
pose proof code_range as [Hc Hcr]; pose proof hdr16_facts as (HqM & Eh16 & Rh16);
unfold memF, memC, memB, memA;
destruct (Z.eqb_spec off 0) as [Eo|Eo];
destruct (Z.eqb_spec reserved 0) as [Er|Er];
[ | destruct (Z.ltb_spec reserved 5) as [Er5|Er5] | | destruct (Z.ltb_spec reserved 5) as [Er5|Er5] ];
cbv zeta.
Ltac peel := rewrite !wbytes_mbyte by (rewrite ?length_word_to_le_bytes; cbn [length]; lia);
rewrite ?length_word_to_le_bytes; cbn [length]; repeat cond_tf.
Ltac fin0 := first [ reflexivity
| match goal with |- nth_error _ (Z.to_nat ?e) = _ => replace (Z.to_nat e) with 0%nat by lia; reflexivity end ].
Ltac fink k := match goal with |- nth_error _ (Z.to_nat ?e) = _ =>
replace (Z.to_nat e) with k by lia; apply word_to_le_bytes_nth; lia end.
Lemma memF_frame : forall x, 0 <= x < 2 ^ 64 -> ~ written x -> memF (Z64 x) = mem (Z64 x).
Proof using Hlast Hsc Hmaplen Hctr Hidx Hn Hgeom Hsmall.
intros x Hx Hw. unfold written in Hw. mem_cases;
rewrite !wbytes_other by (rewrite ?length_word_to_le_bytes; cbn [length]; lia); reflexivity.
Qed.
Lemma memF_present : forall a, mem a <> None -> memF a <> None.
Proof using Hlast Hsc Hmaplen Hctr Hidx Hn Hgeom Hsmall. intros a Ha. mem_cases; repeat apply wbytes_present; exact Ha. Qed.
Lemma memF_writable : forall x, writable_at src0segs mem x -> writable_at src0segs memF x.
Proof using Hlast Hsc Hmaplen Hctr Hidx Hn Hgeom Hsmall. intros x Hx. mem_cases; repeat apply wbytes_writable; exact Hx. Qed.
Lemma memF_hdr :
mbyte src0segs memF (start - 4) = Some (Z_to_bv 8 0) /\
mbyte src0segs memF (start - 3) = Some (Z_to_bv 8 (if off =? 0 then idx + 32 * code else 224)) /\
(forall k, (k < 2)%nat ->
mbyte src0segs memF (start - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (if off =? 0 then hdr16v else off) 2 k))) /\
mbyte src0segs memF (q - 4) = Some (Z_to_bv 8 0) /\
mbyte src0segs memF (q - 3) = Some (Z_to_bv 8 (idx + 32 * code)) /\
(forall k, (k < 2)%nat -> mbyte src0segs memF (q - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte hdr16v 2 k))).
Proof using Hlast Hsc Hmaplen Hctr Hidx Hn Hgeom Hsmall Hc4.
repeat split.
- mem_cases; peel; first [exact Hc4 | rewrite <- Hc4; f_equal; lia].
- mem_cases; peel; rewrite ?(proj2 (Z.eqb_eq off 0) Eo), ?(proj2 (Z.eqb_neq off 0) Eo); fin0.
- intros k Hk. mem_cases; peel; rewrite ?(proj2 (Z.eqb_eq off 0) Eo), ?(proj2 (Z.eqb_neq off 0) Eo); fink k.
- mem_cases; peel; first [ fin0 | rewrite <- Hc4; f_equal; lia ].
- mem_cases; peel; fin0.
- intros k Hk. mem_cases; peel; fink k.
Qed.
Lemma memF_tail :
(0 < reserved -> mbyte src0segs memF (q + n) = Some (Z_to_bv 8 0)) /\
(5 <= reserved -> mbyte src0segs memF (end_ - 5) = Some (Z_to_bv 8 0)) /\
(5 <= reserved -> forall k, (k < 4)%nat ->
mbyte src0segs memF (end_ - 4 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte reserved 4 k))).
Proof using Hlast Hsc Hmaplen Hctr Hidx Hn Hgeom Hsmall.
repeat split.
- intros Hr. mem_cases; try lia; peel; fin0.
- intros Hr. mem_cases; try lia; peel; fin0.
- intros Hr k Hk. mem_cases; try lia; peel; fink k.
Qed.
Definition eclob (r : reg) : Prop :=
r = 5%bv \/ r = 6%bv \/ r = 7%bv \/ r = 10%bv \/ r = 11%bv \/ r = 12%bv \/ r = 13%bv \/
r = 14%bv \/ r = 15%bv \/ r = 16%bv \/ r = 17%bv.
Theorem enframe_steps : forall regs,
getr regs 10 = Z64 g -> getr regs 11 = Z64 idx -> getr regs 12 = Z64 n -> getr regs 13 = Z64 ctr ->
exists regs',
msteps src0segs (mkst regs (Z64 src0_A_enframe) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) memF rom) /\
getr regs' 10 = Z64 q /\
(forall r : reg, ~ eclob r -> getr regs' r = getr regs r).
Proof.
intros regs H10 H11 H12 H13.
destruct (seg1 regs H10) as (r1 & M1 & A14 & F1).
destruct (seg2 r1) as (r2 & M2 & B16 & B15 & B17 & B5 & B13 & F2);
[rewrite F1 by (intros E; discriminate E); assumption .. | exact A14 |].
destruct (seg3 r2 B13 B5 B15) as (r3 & M3 & C17 & C6 & C7 & F3).
destruct (seg4 r3) as (r4 & M4 & D13 & D16 & F4);
[rewrite F3 by (intros E; discriminate E); first [exact B15 | exact B16 | rewrite F2 by (intros E; discriminate E); rewrite F1 by (intros E; discriminate E); assumption] .. | exact C17 |].
destruct (seg5 r4) as (r5 & M5 & E10 & F5).
1-6: rewrite ?D13, ?D16; try reflexivity; rewrite F4 by (intros E; discriminate E);
rewrite ?F3 by (intros E; discriminate E); rewrite ?B15; try reflexivity;
rewrite F2 by (intros E; discriminate E); rewrite ?A14; try reflexivity;
rewrite F1 by (intros E; discriminate E); assumption.
exists r5. split; [|split; [exact E10|]].
- eapply msteps_pc with (pc' := Z64 (src0_A_enframe + 0x0)); [vm_compute; reflexivity|].
eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
eapply msteps_trans; [exact M4|].
replace (getr regs 1) with (getr r4 1); [exact M5|].
rewrite F4, F3, F2, F1 by (intros E; discriminate E). reflexivity.
- intros r Hr. unfold eclob in Hr.
rewrite F5 by (intros E; apply Hr; rewrite E; tauto).
rewrite F4 by (intros E; apply Hr; rewrite E; tauto).
rewrite F3 by (intros E; apply Hr; rewrite E; tauto).
rewrite F2 by (intros E; apply Hr; rewrite E; tauto).
rewrite F1 by (intros E; apply Hr; rewrite E; tauto). reflexivity.
Qed.
End h.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
