(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE08 YB1o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB15.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition istrncpy_words : list (bv 32) :=
[W_e29c0; W_e29c4; W_e29c8; W_e29cc; W_e29d0; W_e29d4; W_e29d8; W_e29dc;
W_e29e0; W_e29e4; W_e29e8; W_e29ec; W_e29f0; W_e29f4; W_e29f8; W_e29fc;
W_e2a00; W_e2a04; W_e2a08; W_e2a0c; W_e2a10; W_e2a14; W_e2a18; W_e2a1c;
W_e2a20; W_e2a24; W_e2a28; W_e2a2c].
Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].
Definition sealed8 : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e].
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.
Lemma length_strncpy_sealed_bytes : length strncpy_sealed_bytes = 4095%nat.
Proof. unfold strncpy_sealed_bytes. rewrite length_app, length_zeros. reflexivity. Qed.
Lemma sealed8_nz : forall j, (0 <= j < 8)%Z -> bv_unsigned (b_ sealed8 j) <> 0%Z.
Proof.
intros j Hj.
assert (E : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%Z) by lia.
destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; cbv; discriminate.
Qed.
Lemma align15_4087 : forall d : word, align15 4087 d <> 0%Z.
Proof.
intros d H. unfold align15 in H. rewrite Z.land_lor_distr_l in H.
apply Z.lor_eq_0_iff in H as [H _]. cbv in H. discriminate.
Qed.
Section e.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 istrncpy_words.
Hypothesis Hsrc : rdn segs mem0 src 8%nat = Some sealed8.
Hypothesis Hnul : rdn segs mem0 (at_ src 8) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hsnw : (bv_unsigned src + 9 < 2 ^ 64)%Z.
Hypothesis Hok : store_ok segs mem0 dst 4095%nat = true.
Hypothesis Hnw : (bv_unsigned dst + 4095 < 2 ^ 64)%Z.
Hypothesis Hdisj : (bv_unsigned dst + 4095 <= bv_unsigned src \/ bv_unsigned src + 9 <= bv_unsigned dst)%Z.
#[local] Abbreviation CL := (fun r => In r istrncpy_clob).
Ltac condv :=
rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.
Lemma HMC : cpyH segs mem0 dst src 8 sealed8.
Proof.
pose proof (u64_range dst). pose proof (u64_range src).
apply CPYH.
- lia.
- reflexivity.
- exact Hsrc.
- cbn [length]. eapply (store_ok_sub segs mem0 dst dst 4095%nat 8%nat); [lia | exact Hok | lia | cbn; lia].
- lia.
- lia.
- lia.
Qed.
#[local] Abbreviation MK := (memk mem0 dst sealed8).
Definition MZ (k : Z) : word -> option byte := msetk (MK 8) (at_ dst 8) (Z_to_bv 8 0) k.
Lemma MZ_0 : MZ 0 = MK 8.
Proof. reflexivity. Qed.
Lemma MZ_final : MZ 4087 = wbytes mem0 dst strncpy_sealed_bytes.
Proof.
unfold MZ, msetk, strncpy_sealed_bytes, zeros. rewrite (memk_n _ _ _ _ _ _ HMC).
rewrite wbytes_app. reflexivity.
Qed.
Lemma MK8_ok : store_ok segs (MK 8) (at_ dst 8) (Z.to_nat 4087) = true.
Proof.
unfold memk. pose proof (u64_range dst).
apply (store_ok_at segs mem0 dst 4095%nat); [lia | exact Hok | lia | cbn; lia].
Qed.
Lemma at8_nw : (bv_unsigned (at_ dst 8) + 4087 < 2 ^ 64)%Z.
Proof. pose proof (u64_range dst). rewrite at_u by lia. lia. Qed.
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at istrncpy_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60
& C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & _).
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ _ HMC) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia]
| step_simpl]; vn.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (memk _ _ _ ?a) _) _ =>
first [constr_eq a kk | replace (memk mem0 dst sealed8 a) with (memk mem0 dst sealed8 kk) by (f_equal; lia)] end.
Ltac msb F D kk :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ _ HMC) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
| gres; rwH; reflexivity | apply sb_val_b | lia | lia]
| step_simpl]; vn.
Ltac mz_at kk := match goal with |- msteps _ (mkst _ _ (MZ ?a) _) _ =>
first [constr_eq a kk | replace (MZ a) with (MZ kk) by (f_equal; lia)] end.
Ltac mzsb F D kk :=
mz_at kk; unfold MZ;
chain_step; [reflexivity
| eapply YK0v.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
[exact F | reflexivity | exact D
| gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; first [reflexivity | f_equal; lia]
| gres; rwH; reflexivity | reflexivity
| apply (wr_s segs (MK 8) (at_ dst 8) 4087 (Z_to_bv 8 0) ltac:(lia) at8_nw MK8_ok); cbn; lia ]
| step_simpl];
rewrite (msetk_extend1 (MK 8) (at_ dst 8) (Z_to_bv 8 0) kk) by lia; fold (MZ (kk + 1)); vn.
Lemma fill_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ dst (8 + k) -> getr regs 12 = at_ dst 4095 ->
(0 <= k)%Z -> (8 + k < 4095)%Z -> (Z.of_nat i = 4095 - 8 - k - 1)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 68) (MZ k) rom) (mkst regs' ret (MZ 4087) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range dst) as Hd.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H12 Hk Hkn Hi.
- eexists. split.
+ mzsb C68 D_e2a04 k.
an C72 D_e2a08.
ab_ft C76 D_e2a0c ltac:(condz).
an C80 D_e2a10.
aret C108 D_e2a2c ret.
mz_at 4087%Z. apply mst_refl.
+ unfold istrncpy_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
+ eexists. split.
* mzsb C68 D_e2a04 k.
an C72 D_e2a08.
ab_tk C76 D_e2a0c ltac:(condz).
mz_at (k + 1)%Z. apply mst_refl.
* post. unfold istrncpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Lemma copy_iter : forall regs (j : Z),
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 4095 ->
getr regs 13 = Z_to_bv 64 j -> (0 <= j < 8)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 8) (MK j) rom) (mkst regs' (at_ base 8) (MK (j + 1)) rom)
/\ getr regs' 10 = dst /\ getr regs' 11 = src /\ getr regs' 12 = Z_to_bv 64 4095
/\ getr regs' 13 = Z_to_bv 64 (j + 1) /\ regs_agree CL regs regs'.
Proof.
get_code. intros regs j H10 H11 H12 H13 Hj. pose proof (u64_range dst). pose proof (u64_range src).
eexists. split.
- av C8 D_e29c8 (at_ src j) ltac:(apply v_add_at; lia).
mlbu C12 D_e29cc j.
ab_ft C16 D_e29d0
ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
apply sealed8_nz; lia).
av C20 D_e29d4 (at_ dst j) ltac:(apply v_add_at; lia).
an C24 D_e29d8.
msb C28 D_e29dc j.
ab_tk C32 D_e29e0 ltac:(condv).
mk_at (j + 1)%Z. apply mst_refl.
- post; try (unfold istrncpy_clob; solve_regs_agree). unfold v_addi. unorm. reflexivity.
Qed.
Lemma copy8 : forall regs0 rr,
regs_agree CL regs0 rr ->
getr rr 10 = dst -> getr rr 11 = src -> getr rr 12 = Z_to_bv 64 4095 ->
getr rr 13 = Z_to_bv 64 0 ->
exists regs',
msteps segs (mkst rr (at_ base 8) (MK 0) rom) (mkst regs' (at_ base 8) (MK 8) rom)
/\ getr regs' 10 = dst /\ getr regs' 11 = src /\ getr regs' 12 = Z_to_bv 64 4095
/\ getr regs' 13 = Z_to_bv 64 8 /\ regs_agree CL regs0 regs'.
Proof.
intros regs0 rr K A B C D.
Ltac cp_iter :=
match goal with
| K : regs_agree _ ?regs0 ?rr, A : getr ?rr 10 = _, B : getr ?rr 11 = _, C : getr ?rr 12 = _, D : getr ?rr 13 = Z_to_bv 64 ?v |- _ =>
let jj := eval vm_compute in v in
let jj1 := eval vm_compute in (v + 1)%Z in
change (Z_to_bv 64 v) with (Z_to_bv 64 jj) in D;
try change (memk mem0 dst sealed8 v) with (memk mem0 dst sealed8 jj);
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK jj1) rom)
(fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
/\ getr r 13 = Z_to_bv 64 jj1 /\ regs_agree CL regs0 r));
[ destruct (copy_iter rr jj A B C D ltac:(lia)) as (r' & RUN & B10 & B11 & B12 & B13 & K');
exists r'; split; [exact RUN | repeat split; try assumption; eapply regs_agree_trans; [exact K | exact K']]
| cbv beta; clear rr K A B C D; intros rr (A & B & C & D & K) ]
end.
do 8 cp_iter.
exists rr. split; [apply mst_refl | repeat split; assumption].
Qed.
Theorem istrncpy_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 4095 ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom)
(mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.
rewrite <- MZ_final.
change (mkst regs (at_ base 0) mem0 rom) with (mkst regs (at_ base 0) (MK 0) rom).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 0) rom)
(fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
/\ getr r 13 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
{ eexists. split.
- ab_ft C0 D_e29c0 ltac:(condz).
an C4 D_e29c4.
apply mst_refl.
- post. unfold istrncpy_clob. solve_regs_agree. }
cbv beta. intros r0 (A10 & A11 & A12 & A13 & K0).
destruct (copy8 regs r0 K0 A10 A11 A12 A13) as (r8 & RUN8 & L10 & L11 & L12 & L13 & K8).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 8) rom)
(fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
/\ getr r 13 = Z_to_bv 64 8 /\ regs_agree CL regs r)).
{ exists r8. split; [exact RUN8 | repeat split; assumption]. }
cbv beta. clear r8 RUN8 L10 L11 L12 L13 K8. intros r8 (L10 & L11 & L12 & L13 & K8).
eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + 0) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
{ eexists. split.
- av C8 D_e29c8 (at_ src 8) ltac:(apply v_add_at; lia).
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact C12 | reflexivity | exact D_e29cc
| gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
rewrite rdn_wbytes_out;
[ exact Hnul
| change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
| step_simpl]; vn.
ab_tk C16 D_e29d0 ltac:(condz).
change (memk mem0 dst sealed8 8) with (MZ 0).
av C40 D_e29e8 (at_ dst 8) ltac:(apply v_add_at; lia).
an C44 D_e29ec.
an C48 D_e29f0.
av C52 D_e29f4 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
ab_ft C56 D_e29f8 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
ab_ft C60 D_e29fc ltac:(condz).
av C64 D_e2a00 (at_ dst 4095) ltac:(apply v_add_at; lia).
apply mst_refl.
- post.
+ rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
+ unfold istrncpy_clob in *. ra_chain. }
cbv beta. intros r9 (M1 & M11 & M12 & K9).
destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End e.
End c.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_istrncpy_entry : word := 0x63d94.
Definition tfib_sealed_src : Z := 0x11806.
Lemma tfib_istrncpy_code :
code_at Asan.M.loaded_segments tfib_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.
Lemma tfib_sealed_src_img : forall mem,
(forall i, (tfib_sealed_src <= i < tfib_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
rdn Asan.M.loaded_segments mem (Z_to_bv 64 tfib_sealed_src) 8 = Some sealed8
/\ rdn Asan.M.loaded_segments mem (at_ (Z_to_bv 64 tfib_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
intros mem Hnone. unfold tfib_sealed_src in *. split.
- rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Theorem tfib_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
(forall i, (tfib_sealed_src <= i < tfib_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
store_ok Asan.M.loaded_segments mem0 dst 4095%nat = true ->
(bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
(bv_unsigned dst + 4095 <= tfib_sealed_src \/ tfib_sealed_src + 9 <= bv_unsigned dst)%Z ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 tfib_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
exists regs',
msteps Asan.M.loaded_segments
(mkst regs tfib_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
/\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
destruct (tfib_sealed_src_img mem0 Hnone) as [Hs Hn].
rewrite <- (at_0 tfib_istrncpy_entry).
apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 tfib_sealed_src) rom tfib_istrncpy_code Hs Hn); try assumption;
unfold tfib_sealed_src in *; u_norm; lia.
Qed.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
