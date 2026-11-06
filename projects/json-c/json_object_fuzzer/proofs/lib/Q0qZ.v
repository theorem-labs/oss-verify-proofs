(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL QiyH QCoy QWTC.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QiyH QCoy.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition istrncpy_words : list (bv 32) :=
[W_753b4; W_753b8; W_753bc; W_753c0; W_753c4; W_753c8; W_753cc; W_753d0;
W_753d4; W_753d8; W_753dc; W_753e0; W_753e4; W_753e8; W_753ec; W_753f0;
W_753f4; W_753f8; W_753fc; W_75400; W_75404; W_75408; W_7540c; W_75410;
W_75414; W_75418; W_7541c; W_75420].

Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].

Definition sealed8 : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e].
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.

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

Section ISTRNCPY.
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
| eapply QHup.Mq1.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
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
+ mzsb C68 D_753f8 k.
an C72 D_753fc.
ab_ft C76 D_75400 ltac:(condz).
an C80 D_75404.
aret C108 D_75420 ret.
mz_at 4087%Z. apply mst_refl.
+ unfold istrncpy_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
+ eexists. split.
* mzsb C68 D_753f8 k.
an C72 D_753fc.
ab_tk C76 D_75400 ltac:(condz).
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
- av C8 D_753bc (at_ src j) ltac:(apply v_add_at; lia).
mlbu C12 D_753c0 j.
ab_ft C16 D_753c4
ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
apply sealed8_nz; lia).
av C20 D_753c8 (at_ dst j) ltac:(apply v_add_at; lia).
an C24 D_753cc.
msb C28 D_753d0 j.
ab_tk C32 D_753d4 ltac:(condv).
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
- ab_ft C0 D_753b4 ltac:(condz).
an C4 D_753b8.
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
- av C8 D_753bc (at_ src 8) ltac:(apply v_add_at; lia).
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact C12 | reflexivity | exact D_753c0
| gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
rewrite rdn_wbytes_out;
[ exact Hnul
| change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
| step_simpl]; vn.
ab_tk C16 D_753c4 ltac:(condz).
change (memk mem0 dst sealed8 8) with (MZ 0).
av C40 D_753dc (at_ dst 8) ltac:(apply v_add_at; lia).
an C44 D_753e0.

an C48 D_753e4.
av C52 D_753e8 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
ab_ft C56 D_753ec ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
ab_ft C60 D_753f0 ltac:(condz).
av C64 D_753f4 (at_ dst 4095) ltac:(apply v_add_at; lia).
apply mst_refl.
- post.
+ rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
+ unfold istrncpy_clob in *. ra_chain. }
cbv beta. intros r9 (M1 & M11 & M12 & K9).
destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End ISTRNCPY.

Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Definition asan_istrncpy_entry : word := 0x7539c.
Definition asan_sealed_src : Z := 0x11adc.

Lemma asan_istrncpy_code :
code_at Asan.M.loaded_segments asan_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

Lemma asan_sealed_src_img : forall mem,
(forall i, (asan_sealed_src <= i < asan_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
rdn Asan.M.loaded_segments mem (Z_to_bv 64 asan_sealed_src) 8 = Some sealed8
/\ rdn Asan.M.loaded_segments mem (at_ (Z_to_bv 64 asan_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
intros mem Hnone. unfold asan_sealed_src in *. split.
- rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem asan_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
(forall i, (asan_sealed_src <= i < asan_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
store_ok Asan.M.loaded_segments mem0 dst 4095%nat = true ->
(bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
(bv_unsigned dst + 4095 <= asan_sealed_src \/ asan_sealed_src + 9 <= bv_unsigned dst)%Z ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 asan_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
exists regs',
msteps Asan.M.loaded_segments
(mkst regs asan_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
/\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
destruct (asan_sealed_src_img mem0 Hnone) as [Hs Hn].
rewrite <- (at_0 asan_istrncpy_entry).
apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 asan_sealed_src) rom asan_istrncpy_code Hs Hn); try assumption;
unfold asan_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE Q3bI QU0c QJ4Q Qo8J Q85Z QHup QG64 QWZn Qrlk QJJu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn Qrlk QJJu QCoy.Mq3 QCoy.Mq4 QCoy.Mq5 QiyH.Mq1.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ALL.
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

Ltac conda := rwH; unfold at_; cond.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma al_finish : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb46c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
set (m := ((n - k) mod 16)%Z).
pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb4a8 : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb4c8 : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb70c : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R | eapply keeps_trans; eassumption].
Qed.

Lemma mis_run : forall regs (ret : word) k q,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
(0 <= k <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb39c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
-
destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3a4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_db3c0 D_db3c0.
stepb_ft F_db3c4 D_db3c4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
set (m := (n - k)%Z) in *.
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb70c : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb3c0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_db3c0 D_db3c0.
stepb_tk F_db3c4 D_db3c4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
assert (CASE : exists regs' m,
msteps JO6SEGS (mkst r1 (0xdb3c0 : word) (MK k) rom)
(mkst regs' (0xdb70c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
{ destruct Hq as [-> | [-> | ->]].
- apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

Lemma j_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb394 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
pose proof (u64_range dst).
set (q := ((bv_unsigned dst + k) mod 4)%Z).
pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
destruct (Z.eq_dec q 0) as [Hq0|Hq0].
-
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb46c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_db3b8 D_db3b8.
stepb_tk F_db3bc D_db3bc ltac:(conda).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
- eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb39c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_db3b8 D_db3b8.
stepb_ft F_db3bc D_db3bc ltac:(conda).
apply mst_refl.
* cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
change (bv_wrap 64 3) with 3%Z. reflexivity.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

Lemma hl_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
(Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb364 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
-
pose proof (u64_range src).
destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
+ eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb394 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_db388 D_db388 k.
stepn F_db38c D_db38c.
stepn F_db390 D_db390.
stepn F_db394 D_db394.
msb F_db398 D_db398 k ltac:(apply sb_val_plain).
stepn F_db39c D_db39c.
stepn F_db3a0 D_db3a0.
stepb_tk F_db3a4 D_db3a4 ltac:(conda).
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb394 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_db388 D_db388 k.
stepn F_db38c D_db38c.
stepn F_db390 D_db390.
stepn F_db394 D_db394.
msb F_db398 D_db398 k ltac:(apply sb_val_plain).
stepn F_db39c D_db39c.
stepn F_db3a0 D_db3a0.
stepb_ft F_db3a4 D_db3a4 ltac:(conda).
stepn F_db3a8 D_db3a8.
stepb_ft F_db3ac D_db3ac ltac:(cond).
stepn F_db3b0 D_db3b0.
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
pose proof (u64_range src).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb364 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
/\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
+ eexists. split.
* mlbu F_db388 D_db388 k.
stepn F_db38c D_db38c.
stepn F_db390 D_db390.
stepn F_db394 D_db394.
msb F_db398 D_db398 k ltac:(apply sb_val_plain).
stepn F_db39c D_db39c.
stepn F_db3a0 D_db3a0.
stepb_ft F_db3a4 D_db3a4 ltac:(conda).
stepn F_db3a8 D_db3a8.
stepb_tk F_db3ac D_db3ac ltac:(cond).
apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

Theorem ref_memcpy : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps JO6SEGS (mkst regs (0xdb34c : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ keeps regs regs'.
Proof.
intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
-
destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
+ eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb46c : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_db370 D_db370.
stepb_tk F_db374 D_db374 ltac:(conda).
stepn F_db484 D_db484.
stepn F_db488 D_db488.
stepb_ft F_db48c D_db48c ltac:(cond).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb39c : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
* eexists. split.
-- stepn F_db370 D_db370.
stepb_tk F_db374 D_db374 ltac:(conda).
stepn F_db484 D_db484.
stepn F_db488 D_db488.
stepb_tk F_db48c D_db48c ltac:(cond).
apply mst_refl.
-- cbv beta. post; try (rewrite at_0; reflexivity).
unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
+ eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb394 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_db370 D_db370.
stepb_ft F_db374 D_db374 ltac:(conda).
stepb_tk F_db378 D_db378 ltac:(cond).
stepn F_db3b4 D_db3b4.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
eapply (runs_trans JO6SEGS _ (fun r => mkst r (0xdb364 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
* eexists. split.
-- stepn F_db370 D_db370.
stepb_ft F_db374 D_db374 ltac:(conda).
stepb_ft F_db378 D_db378 ltac:(cond).
stepn F_db37c D_db37c.
stepn F_db380 D_db380.
stepn F_db384 D_db384.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
{ subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

End ALL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n QOTP.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition jo6_stage2b_r0_1 : plan :=
PRun [0x4c5d4]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x915f8]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 3 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition jo6_stage2b_r1_2 : plan :=
PRun [0x4c5d4]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x915f8]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 4 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition jo6_stage2b : plan :=
PBump 478
(PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 4030
(jo6_stage2b_r0_1)
(jo6_stage2b_r1_2)).

Definition jo6_stage2b_ranges : list (Z * nat) := [(0x3d000, 1018%nat); (0x4bfe8, 4096%nat); (0x63fe8, 2048%nat); (0x68fe8, 1024%nat); (0x6afe8, 1024%nat); (0x6cfe8, 1024%nat); (0x6efe8, 3072%nat); (0x73fe8, 4096%nat); (0x7cfe8, 1024%nat); (0x80fe8, 4096%nat); (0x90fe8, 2048%nat); (0xcafe8, 1024%nat); (0xdafdc, 1024%nat); (0xdcfdc, 1024%nat)]%Z.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import Qt8n QOTP.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition jo6_startup1s_brkfail1 : plan :=
PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 9 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PRun []
(PMprotect
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 8 )))))))))))))
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 7 )))))))))))))
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (EVar 424) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 6 )))))))))))))))))))).

Definition jo6_startup1s_tail2 : plan :=
PRun [0x7d914]
(PRespell 10 (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10)))
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 374
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemcpy []
(PRun []
(PSys YBrk
(PRun []
(PSplit (EVar 5) 524276
(PBrk2
(jo6_startup1s_brkfail1)
(PRun []
(PMmapIn
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 3 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 2 )))))))))))))))))
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 1 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 0 )))))))))))))))))
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 5 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x92ab4]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 4 ))))))))))))))))))))
(PSys YBrk
(jo6_startup1s_brkfail1)))))))))))))))))).

Definition jo6_startup1s_s2A3 : plan :=
PBump 364
(jo6_startup1s_tail2).

Definition jo6_startup1s_tospin4 : plan :=
PRun []
(PX XIMemset []
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7870c]
(PFresh 21 0 None
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun [0x7889c]
(PDiamond 0x78874 [16]%nat
(PRun []
(PSpin ))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition jo6_startup1s : plan :=
PRun []
(PX XIMemset []
(PRun []
(PX XEnvScan []
(PRun []
(PX XPnScan []
(PRun []
(PX XIMemcpy []
(PRun []
(PSys YSetTid
(PRun []
(PRun [0xcc384]
(PExt 1 [ELit 6565536; ELit 8]
(PRun [0x765b8]
(PExt 2 []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x7539c]
(PX XIStrncpy []
(PRun [0x7539c]
(PX XIStrncpy []
(PRun [0x6a8c0]
(PDropRange (ELit 1570240) (ELit 0xfff) (PDropRange (ELit 1574336) (ELit 0xfff)
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun [0x6a8c4]
(PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
(PRun [0x765b8]
(PExt 2 []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x6a988]
(PDropRange (ELit 971768) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x7d3e0]
(PFresh 9 12 None
(PRun []
(PMmapIn
(jo6_startup1s_tospin4)
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 220
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 249
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemIsZero []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PSys YMunmap
(PSplit (EVar 10) 0
(jo6_startup1s_s2A3)
(PSplit (EVar 10) 7
(jo6_startup1s_s2A3)
(jo6_startup1s_s2A3)))))))))))))))))))))))))))))))))))))))
(jo6_startup1s_tospin4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition jo6_startup1s_ranges : list (Z * nat) := [(0x3d000, 2042%nat); (0x3ffe8, 2048%nat); (0x43fe8, 2048%nat); (0x48fe8, 3072%nat); (0x4dfe8, 2048%nat); (0x54fe8, 1024%nat); (0x56fe8, 8192%nat); (0x60fe8, 5120%nat); (0x68fe8, 23552%nat); (0x80fe8, 1024%nat); (0x8afe8, 1024%nat); (0x8dfe8, 1024%nat); (0x90fe8, 2048%nat); (0xcafe8, 5117%nat); (0xd0fdc, 1024%nat); (0xdafdc, 4096%nat)]%Z.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n.
Import QOTP.
Import QqZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HS1s_0 : acs := ltac:(acsb (AXB.acs_of "wv`/C###uu`/%#%#'##q}A$#'##C$)#X'#eyb$#ioZy%$V-$W-$X-#gzR6#UyR6#wpy6#qYs6#eoy6$Y-$Z-$[-$\-$]-#Sv[/%#%#'##q}A$#%#'##3$$'##C$)#C################$^-$_-$`-$a-#~2($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&($Z,%U^nyn\*###]S\7$#####Uy\7+#y{\7$##m}\7#-###]}\7+#####cR]7$#%###{|\7+#####k|\7+#####[|\7'#-###y{\7+#umh6###aiuw%$#####ciuw%$#%###qauw%+#gduw%$##[fuw%#o$###yeuw%+#####Qiuw%$#%###ieuw%+#####Yeuw%+#####wduw%'#o$###gduw%+#Quq6###eiuw%%#####_b~{%+%#'##Uy&$Z,#u%#'##Uy&$Z,w&+###'##Uy&$Z,g&+#ywj+#'##Uy&$Z,Y'+###'##Uy&$Z,W&+#qsj+#'##Uy&$Z,u%+#klj+#'##Uy&$Z,o%$#k(#'##Uy&$Z,i'$###'##Uy&$Z,q%%#####ug{{%+%#'##Uy&$(#Wz&#'##Uy&$(gz&+%#'##Uy&$(#Wz&#'##Uy&$(Wz&+%#'##Uy&$(#Wz&#'##Uy&$(Y{&'#eO#'##Uy&$(i{&+#a*#'##Uy&$Z,e%$#5#'##Uy&$Z,U%+%#'##Uy&$(#Wz&#'##Uy&$(wz&+%#'##Uy&$Z,#U%#'##Uy&$(a{&'#####gx{{%+#7#'##Uy&$Z,g:$###'##Uy&$Z,c8$###'##Uy&$Z,_6$###'##Uy&$Z,[4$###'##Uy&$Z,W2$###'##Uy&$Z,S0$###'##Uy&$Z,}-$###'##Uy&$Z,y+$###'##Uy&$Z,u)$###'##Uy&$Z,q'$###'##Uy&$Z,m%$###'##Uy&$Z,}$$#a+#'##Uy&$Z,Q%%#####_l{{%+%#'##Uy&$(#y{&#'##Uy&$([|&+%#'##Uy&$(#y{&#'##Uy&$(y{&+%#'##Uy&$(#y{&#'##Uy&$({|&'#'#'##Uy&$(]}&+#YN#'##Uy&$Z,s$$#%#'##Uy&$Z,c$+%#'##Uy&$(#y{&#'##Uy&$(k|&+%#'##Uy&$Z,#c$#'##Uy&$(U}&'#####Q}{{%+#'#'##Uy&$Z,SP$###'##Uy&$Z,{$$###'##Uy&$Z,]$$#a+#'##Uy&$Z,_$%#####qm{{%+%#'##Uy&$(#m}&#'##Uy&$(}}&+%#'##Uy&$(#m}&#'##Uy&$(m}&+%#'##Uy&$(#m}&#'##Uy&$(o~&'#'#'##Uy&$(QQ'+#_Y$#'##Uy&$Z,S$$#%#'##Uy&$Z,C+%#'##Uy&$(#m}&#'##Uy&$(_~&+%#'##Uy&$Z,#C#'##Uy&$(w~&'#####c~{{%+#'#'##Uy&$Z,y{$$###'##Uy&$Z,[$$###'##Uy&$Z,=$#a+#'##Uy&$Z,?%#####Uo{{%+%#'##Uy&$(#aQ'#'##Uy&$(qQ'+%#'##Uy&$(#aQ'#'##Uy&$(aQ'+%#'##Uy&$(#aQ'#'##Uy&$(cR''#'#'##Uy&$(sR'+#i^(#'##Uy&$Z,3$#%#'##Uy&$Z,#+%#'##Uy&$(#aQ'#'##Uy&$(SR'+'##Uy&$Z,#'##Uy&$(kR''#####uQ|{%+#'###Wd{{%'#%($[,%U^nyn\*)'##]9$Z,krg[x7#]9$'##]9$Z,krg[x7#]9)'##Uy&$Z,##Uy&$'##Uy&$Z,5#+$'##Uy&$Z,U$#)$'##Uy&$Z,u$#)$'##Uy&$Z,g%#)$'##Uy&$Z,k'#)$'##Uy&$Z,s'#S%$'##Uy&$Z,w)#S%$'##Uy&$Z,{+#S%$'##Uy&$Z,Q.#S%$'##Uy&$Z,U0#S%$'##Uy&$Z,Y2#S%$'##Uy&$Z,]4#S%$'##Uy&$Z,a6#S%$'##Uy&$Z,e8#S%$'##Uy&$Z,i:#i8$'##Uy&$Z,UP#uN$'##Uy&$Z,{{$#Y|$*'##Uy&$Z,##Uy&##c|`$#Ysrz%*'##Uy&$Z,##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z,##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z,krg[x7#]9##sfo[x7#i}q3*'##]9$Z,krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z,##Uy&##gxc[x7#WVltmors$*'##Uy&$(##Ys*'##Uy&$Z,##Uy&*'##Uy&$w+##oxsX('##Uy&$Z,##Uy&*'##Uy&$Y*##Uy&'##Uy&$Z,##Uy&*'##Uy&$t(##Uy&'##Uy&$Z,##Uy&*'##Uy&$Y(##c|`$'##Uy&$Z,##Uy&*'##Uy&$X(##Uy&'##Uy&$Z,##Uy&*'##Uy&$W(##Usas&'##Uy&$Z,##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Z,##Uy&*'##Uy&$h'##WRlo$'##Uy&$Z,##Uy&*'##Uy&$q$##c|`$'##Uy&$Z,##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Z,##Uy&*#]kSWf:##WXelkZU-'##Uy&$Z,##Uy&*#gxc[x7##uqnzl%'##Uy&$Z,##Uy&($Z,%U^nyn\*###]]|{%$#%###Qe{{%+#['###od{{%+%#'##Uy&$(#US'#'##Uy&$(uy&'#c'#'##Uy&$(Uy&+*#<3+###cf{{%+%#'##Uy&$(#Uy&###Sf{{%+%#'##Uy&$(#Uy&###sf{{%+%#'##Uy&$(#Ys*###ae{{%+#####m]|{%+%#'##Uy&$(#Ys*)'##]9$(krg[x7#iO$'##]9$(krg[x7#iO)'##Uy&$(Uy&#Uy&$'##Uy&$(ey&#3$'##Uy&$(}y&#+$'##Uy&$(US'#Uq&*'##Uy&$w+##oxsX('##Uy&$(##]m.*'##Uy&$Y*##Uy&'##Uy&$(##]m.*'##Uy&$t(##Uy&'##Uy&$(##]m.*'##Uy&$Y(##c|`$'##Uy&$(##]m.*'##Uy&$X(##Uy&'##Uy&$(##]m.*'##Uy&$W(##Usas&'##Uy&$(##]m.*'##Uy&$i'##YqWklQ@'##Uy&$(##]m.*'##Uy&$h'##WRlo$'##Uy&$(##]m.*'##Uy&$q$##c|`$'##Uy&$(##]m.*#crgrRrU-##[\h]ecni$'##Uy&$(##]m.*#]kSWf:##WXelkZU-'##Uy&$(##]m.*#gxc[x7##uqnzl%'##Uy&$(##]m.($(uh$mit-###}c{{%'#%###mc{{%+*#<3+###_X]7+###'##Uy&$Y([('###'##Uy&$Y(y''#'#'##Uy&$Y(c$+#####SZ]7+#%###ioZy%+'##Uy&$w+#'##Uy&$X(W&+'##Uy&$w+#'##Uy&$w+w&+#K)'##]9$w+krg[x7#}Ur@$'##]9$w+krg[x7#}Ur@)'##Uy&$w+##oxsX($'##Uy&$w+##w&$'##Uy&$w+Y'#gtsX(*'##Uy&$w+##oxsX(##c|`$#Ysrz%*'##Uy&$w+##oxsX(%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$w+##oxsX(%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$w+krg[x7#}Ur@##sfo[x7#i}q3*'##]9$w+krg[x7#}Ur@%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$w+##oxsX(##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$w+##oxsX(*'##Uy&$t(##Uy&'##Uy&$w+##oxsX(*'##Uy&$Y(##c|`$'##Uy&$w+##oxsX(*'##Uy&$X(##Uy&'##Uy&$w+##oxsX(*'##Uy&$W(##Usas&'##Uy&$w+##oxsX(*'##Uy&$i'##YqWklQ@'##Uy&$w+##oxsX(*'##Uy&$h'##WRlo$'##Uy&$w+##oxsX(*'##Uy&$q$##c|`$'##Uy&$w+##oxsX(*#crgrRrU-##[\h]ecni$'##Uy&$w+##oxsX(*#]kSWf:##WXelkZU-'##Uy&$w+##oxsX(*#gxc[x7##uqnzl%'##Uy&$w+##oxsX(($w+%_mkyn\*#'##Uy&$X(u%+#yoZy%#'##Uy&$X(C+%#%#'##q}A$#'##Uy&$-#Tsas&#'##Uy&$X(3+%#'##q}A$#'##Uy&$-#'##Uy&$X(e%+#}m\y%#'##Uy&$X(U%+#yc\y%*'##Uy&$Z*##Uy&##c|`$#Ysrz%*'##Uy&$Z*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z*krg[x7#]9##sfo[x7#i}q3*'##]9$Z*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z*##Uy&##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$Z*##Uy&*'##Uy&$t(##Uy&'##Uy&$Z*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Z*##Uy&*'##Uy&$X(##Uy&'##Uy&$Z*##Uy&*'##Uy&$W(##Usas&'##Uy&$Z*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Z*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Z*##Uy&*'##Uy&$q$##c|`$'##Uy&$Z*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Z*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Z*##Uy&*#gxc[x7##uqnzl%'##Uy&$Z*##Uy&($Z*%U^nyn\*###ekeC$#%#'##Uy&$Y*c$+###'##Uy&$Y*S$+#ioZy%###[dz6$#####]dz6&#####}geC+#%###yoZy%+'##Uy&$Y*)'##Uy&$Y*##Uy&$'##Uy&$Y*##S$$'##Uy&$Y*s$#aw&*'##Uy&$Y*##Uy&##c|`$#Ysrz%*'##Uy&$Y*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y*krg[x7#]9##sfo[x7#i}q3*'##]9$Y*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y*##Uy&##gxc[x7#WVltmors$*'##Uy&$t(##Uy&'##Uy&$Y*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Y*##Uy&*'##Uy&$X(##Uy&'##Uy&$Y*##Uy&*'##Uy&$W(##Usas&'##Uy&$Y*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Y*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Y*##Uy&*'##Uy&$q$##c|`$'##Uy&$Y*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Y*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Y*##Uy&*#gxc[x7##uqnzl%'##Uy&$Y*##Uy&($Y*%U^nyn\*#'##Uy&$X(s$$###'##Uy&$X(c$+###'##Uy&$X(S$+#####QiZy%$#%###_dQ|%+'##Uy&$Y(#'##Uy&$X(#+'##Uy&$Y(#'##Uy&$Y(m)+'##Uy&$X(#'##Uy&$Y(S($#%###QY]7+#%#'##Uy&$Y(s$+###'##Uy&$Y(C+#####qY]7+#%###aY]7+#%#'##Uy&$t(#+'##Uy&$Y(###U[]7+#%###sZ]7+#Uy&###cZ]7+'##Uy&$t()'##Uy&$t(##Uy&$'##Uy&$t(3#sx&*'##Uy&$t(##Uy&##c|`$#Ysrz%*'##Uy&$t(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$t(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$t(krg[x7#]9##sfo[x7#i}q3*'##]9$t(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$t(##Uy&##gxc[x7#WVltmors$*'##Uy&$Y(##c|`$'##Uy&$t(##Uy&*'##Uy&$X(##Uy&'##Uy&$t(##Uy&*'##Uy&$W(##Usas&'##Uy&$t(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$t(##Uy&*'##Uy&$h'##WRlo$'##Uy&$t(##Uy&*'##Uy&$q$##c|`$'##Uy&$t(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$t(##Uy&*#]kSWf:##WXelkZU-'##Uy&$t(##Uy&*#gxc[x7##uqnzl%'##Uy&$t(##Uy&($t(%U^nyn\*###uS]7+###'##Uy&$Y(#+#gTS6#'##Uy&$Y(e)%#iO#'##Uy&$Y(])'###'##Uy&$Y(S$'###'##Uy&$Y(3'###'##Uy&$Y(U%$###'##Uy&$Y({(+###'##Uy&$Y(k('###'##Uy&$Y(c('#####wT]7+%#'##Uy&$Y(#})###gT]7+%#'##Uy&$Y(#c|`$)'##Uy&$Y(##c|`$$'##Uy&$Y(;#+$'##Uy&$Y([$#+$'##Uy&$Y(W%#s%$'##Uy&$Y(U(#)$'##Uy&$Y(s(#+$'##Uy&$Y(i)#'$'##Uy&$Y(})#eu`$*'##Uy&$Y(##c|`$##c|`$#Ysrz%*'##Uy&$Y(##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y(##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y(krg[x7#Ys*##sfo[x7#i}q3*'##]9$Y(krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y(##c|`$##gxc[x7#WVltmors$*'##Uy&$X(##Uy&'##Uy&$Y(##c|`$*'##Uy&$W(##Usas&'##Uy&$Y(##c|`$*'##Uy&$i'##YqWklQ@'##Uy&$Y(##c|`$*'##Uy&$h'##WRlo$'##Uy&$Y(##c|`$*'##Uy&$q$##c|`$'##Uy&$Y(##c|`$*#crgrRrU-##[\h]ecni$'##Uy&$Y(##c|`$*#]kSWf:##WXelkZU-'##Uy&$Y(##c|`$*#gxc[x7##uqnzl%'##Uy&$Y(##c|`$($Y(%e]nyn\*###{V]7'#####kV]7'#####[V]7+#####yU]7+#####eS]7+#YU]7###sR]7$#%###qU]7'#####iU]7'#####YU]7+#####UW]7'#####sV]7'#####US]7+#]W]7###w\]7+#####g\]7+#####W\]7+#####u[]7+#####e[]7+#####[^]7'#####y]]7+#####i]]7+#####Y]]7+#####wX]7'#####oX]7'#####}W]7'#####mW]7+#[ijUWqnbbqz5###]W]7+#Ue`,)'##Uy&$X(##Uy&$'##Uy&$X(u$#1$'##Uy&$X(g&#mu&*'##Uy&$X(##Uy&##c|`$#Ysrz%*'##Uy&$X(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$X(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$X(krg[x7#]9##sfo[x7#i}q3*'##]9$X(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$X(##Uy&##gxc[x7#WVltmors$*'##Uy&$W(##Usas&'##Uy&$X(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$X(##Uy&*'##Uy&$h'##WRlo$'##Uy&$X(##Uy&*'##Uy&$q$##c|`$'##Uy&$X(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$X(##Uy&*#]kSWf:##WXelkZU-'##Uy&$X(##Uy&*#gxc[x7##uqnzl%'##Uy&$X(##Uy&($X(%U^nyn\*###qieC+#Shx-###Wnz{%'#%###_zz{%+#Shx-###Yoz{%+#i_Z4###gnz{%+#wnz{%###]weC$#####YS\7$#%###[S\7$#%###yY}6+#kTr^uUS(###_Z}6%#S|$###[Z}6%#C###cZ}6$#%###}lz6$#####{lz6$#####uiz6+#]Uj8###eiz6+#yrT{`%###Uiz6+#uqnzl%###uwy6+'##Uy&$W(###wxy6+#ufZ%###gxy6+#Usas&###Wxy6+'##Uy&$W(*'##Uy&$W(##Usas&##c|`$#Ysrz%*'##Uy&$W(##Usas&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$W(##Usas&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$W(krg[x7#]Uj8##sfo[x7#i}q3*'##]9$W(krg[x7#]Uj8%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$W(##Usas&##gxc[x7#WVltmors$*'##Uy&$i'##YqWklQ@'##Uy&$W(##Usas&*'##Uy&$h'##WRlo$'##Uy&$W(##Usas&*'##Uy&$q$##c|`$'##Uy&$W(##Usas&*#crgrRrU-##[\h]ecni$'##Uy&$W(##Usas&*#]kSWf:##WXelkZU-'##Uy&$W(##Usas&*#gxc[x7##uqnzl%'##Uy&$W(##Usas&($W(%Ualyn\*###ewy6+#Uy&###cvy6'#[ijUWqnbbqz5###WZ\7+#Uy&###uY\7+#%)%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&$%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&###svy6+%#%#'##Uy&$i''##Ty&$j'#UwSklQ@###Svy6+%#%#'##Uy&$i''##Ty&$j'#c|`$($j'#A(%#'##Ty&$j'%,'##Uy&$i'#a|`$#####auy6+#a_}$###Quy6+#YqWklQ@###oty6+'##Uy&$i'*'##Uy&$i'##YqWklQ@##c|`$#Ysrz%*'##Uy&$i'##YqWklQ@%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$i'##YqWklQ@%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$i'krg[x7#iwh|vm&##sfo[x7#i}q3*'##]9$i'krg[x7#iwh|vm&%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$i'##YqWklQ@##gxc[x7#WVltmors$*'##Uy&$h'##WRlo$'##Uy&$i'##YqWklQ@*'##Uy&$q$##c|`$'##Uy&$i'##YqWklQ@*#crgrRrU-##[\h]ecni$'##Uy&$i'##YqWklQ@*#]kSWf:##WXelkZU-'##Uy&$i'##YqWklQ@*#gxc[x7##uqnzl%'##Uy&$i'##YqWklQ@($i'_|UrqLS_Yz_\*###Uwy6$#####QvVB$#%###yaQ|%'#####Qc~{%+#mej+###iaQ|%'#####iUW7'#####qkZy%+#_dQ|%###aUW7$#%###y{X7+#krg[x7###qSW7$#%###mSW7$#%###uSW7'#Q0###_TW7+'##Uy&$h'###}SW7+#_TW7)'##Uy&$h'##WRlo$$'##Uy&$h'##WRlo$*'##Uy&$h'##WRlo$##c|`$#Ysrz%*'##Uy&$h'##WRlo$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$h'##WRlo$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$h'krg[x7#cbk,##sfo[x7#i}q3*'##]9$h'krg[x7#cbk,%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$h'##WRlo$##gxc[x7#WVltmors$*'##Uy&$q$##c|`$'##Uy&$h'##WRlo$*#crgrRrU-##[\h]ecni$'##Uy&$h'##WRlo$*#]kSWf:##WXelkZU-'##Uy&$h'##WRlo$*#gxc[x7##uqnzl%'##Uy&$h'##WRlo$($h'%kdmyn\*###oSW7$#%###muVB+#aYQ,###[ph6+#3###[|X7'#%###o~dC$#####]qh6'#'###q~dC&#####[feC+#S|j+###QieC+#]SQ,###aieC+#Yw~+###iS\7+#_{RYQ`xR1###sT\7'#_$###YUW7$#%###QUW7'#'###S`}6$#%###QQeC+#%###aQeC+#####qQeC+#####SReC+#Wnq$###cReC+#SRclYZ>###sReC+#####USeC+#####eSeC+#####uSeC+#####WTeC+#eZu]oQT(###gTeC+#ic`gqL###wTeC+#####YUeC+#####iUeC+#####yUeC+#e|`$###[VeC+#[ijUWqnbbqz5###kVeC+#seg$###{VeC+#W.###]WeC+#####mWeC+#####}WeC+#####_XeC+#####oXeC+#sV[mdumbbqz5###QYeC+#%###aYeC+#wer$###qYeC+#Wnq$###SZeC+#Wnq$###cZeC+#cZu]oQT(###sZeC+#####U[eC+#skm%###e[eC+#_lu`ojeryc&###u[eC+#m`lXmogwyc&###W\eC+#soTi*###g\eC+#WgSugQT(###w\eC+#WmX%###Y]eC+#wTUaQoqT?###Q]}6'#iO###w\}6'#W.###kV]C'#####]uVB+%#'##Uy&$q$#au5###cjuw%%#####Sjuw%+#Wnq$###qiuw%%#####}}tw%'#%###{|tw%'#Y.###k|tw%+#yohneogwyc&###c|tw%'#####[|tw%$#####m}tw%+#Wnq$###]}tw%'#%###Y}tw%$#####U}tw%%#####k`}6$#####i]}6$#####Ya}6+#Wnq$###Qa}6'#'###w`}6$#%###o`}6'#####g`}6%#%###W`}6+#UX\Wmogwyc&###u_}6)#ic`gqL###U`}6$#####k^}6'#Uy&###c^}6$#####S^}6+#WTqqVW5###q]}6+#c]YXssfwyc&###a]}6'#S|$###e_}6+#####]_}6$#%###U_}6'#q&###s^}6+#Whm\Y]s&###Y]}6'#C###o\}6'#gc`gqL###ia}6'#kYa$###{tVB+%#'##Uy&$q$#c|`$)'##Uy&$q$##c|`$$'##Uy&$q$c|`$##*'##Uy&$q$##c|`$##c|`$#Ysrz%*'##Uy&$q$##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$q$##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$q$krg[x7#Ys*##sfo[x7#i}q3*'##]9$q$krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$q$##c|`$##gxc[x7#WVltmors$*#crgrRrU-##[\h]ecni$'##Uy&$q$##c|`$*#]kSWf:##WXelkZU-'##Uy&$q$##c|`$*#gxc[x7##uqnzl%'##Uy&$q$##c|`$($q$%e]nyn\*###{V]C+#Uy&###kT\7$#%)%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$$%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$)##sfo[x7#i}q3$##sfo[x7#i}q3###[V]C+%#%#'##q}A$#'##C$)#|)###kph6+#[nx%###_S\7$###%#'##q}A$#'##C$)v&+#{hX4#%#'##q}A$#'##C$)V&+$$#%#'##q}A$#'##C$)t%+%#%#'##q}A$#'##C$)#3#%#'##q}A$#'##C$)d%+#kpX4#%#'##q}A$#'##C$)r$+###%#'##q}A$#'##C$)b$+###%#'##q}A$#'##C$)R$+###%#'##q}A$#'##C$)B+###%#'##q}A$#'##C$)2+#####wnZy%+$P###Umz{%+$P###ygZy%+#####igZy%+#wfZy%###YgZy%+#wfZy%###SlZy%+#SlZy%###emZy%+#][{{%###[hZy%'$O($O%QbYy$###khZy%'#'###wX{{%$#%###wfZy%+#wfZy%###YoZy%+#]qZy%###]qZy%+#%###mqZy%+#kl\y%###[Z{{%+#3###yY{{%+#W.###slz{%+#####Slz{%+#c$###kZ{{%+#%###iY{{%+#Qkz{%###clz{%+#3###qkz{%+#####akz{%+#QQ}5###gX{{%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+###{Z{{%+#Uy&###a]{{%+$,###YY{{%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#S$###gfZy%+%#%#'##q}A$#%#'##3$$'##C$)#C#%#'##q}A$#'##C$)T%+%#%#'##q}A$#'##C$)#3($#Wf~eqLgc`gqL($)#Q|$(%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#q+ecy{WywR1a{RYQ`xR1(%#'##Uy&$#%#$$%#$%%#$''##'$)_ixxQmrs$}Zhtmors$(%#'##q}A$#'##C$)U[y{WywR1QsRYQ`xR1(%#'##Uy&$#'##'$)]ixxQmrs$Q[htmors$($$%iO($%#W.($&#syp%($*#syp%($+#ec`gqL($'#{ns(($(uh${Sv-($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&(%#'##Ty&$-%,%#'##C$)#Ur&#YofUWqnbbqz5##)%#'##q}A$#'##C$)Tsas&#Usas&$%#'##q}A$#'##C$)X'#3$%#'##q}A$#'##C$)f&#3#%#'##q}A$#'##C$)#+$$#%#'##q}A$#'##C$)3+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+#%#'##q}A$#'##C$)C+'#%'#%$$%#%#'##q}A$#%#'##3$$%#'##3$%%#$&'##C$)#S+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)S$+#)#%#'##q}A$#%#'##3$$%#'##3$%'##C$)c$+#YQa$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)s$+#+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)U%+#e%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)e%+#-#%#'##q}A$#%#'##3$$%#'##3$%'##C$)u%+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)W&+#C#%#'##q}A$#%#'##3$$%#'##3$%'##C$)g&+$,#%#'##q}A$#%#'##3$$%#'##3$%'##C$)w&+#/#%#'##q}A$#%#'##3$$%#'##3$%'##C$)Y'+#Uy&#%#'##q}A$#%#'##3$$%#'##3$%'##C$)i'+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)y'+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)[(+#;#%#'##q}A$#%#'##3$$%#'##3$%'##C$)k(+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$){(+#Q$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)])+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)m)+#U$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)})+%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#Q+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)_*+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)o*+##%%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)Q+#C<&c|`$[ph6&{ph6]qh6&eqh6oty6&quy6Svy6&kvy6svy6&Wwy6ewy6&Yyy6[dz6&cdz6Uiz6&Wjz6{lz6&Qmz6yY}6&eZ}6o\}6&k]}6q]}6&e^}6k^}6&__}6e_}6&m`}6o`}6&y`}6Qa}6&qa}6ug}6&uQT7mSW7&sSW7uSW7&oTW7QUW7&[UW7aUW7&cUW7iUW7&qUW7y{X7&c|X7YS\7&aS\7iS\7&yS\7kT\7&mT\7sT\7&{T\7uY\7&gZ\7Uy\7&ey\7y{\7&c|\7k|\7&w}\7cR]7&eR]7sR]7&uR]7US]7&WT]7gT]7&WX]7_X]7&c^]7{tVB&}uVBQvVB&SvVB[V]C&sV]C{V]C&]W]C_X]C&aRaCcRaC&ezdCo~dC&w~dCQQeC&i]eC[feC&kfeC}geC&_heCQieC&SjeCekeC&gkeC]weC&_weC[|tw%&]|tw%c|tw%&[}tw%]}tw%&e}tw%m}tw%&W~tw%qauw%&Sbuw%gduw%&Qeuw%Yeuw%&yguw%Qiuw%&Siuw%aiuw%&iiuw%qiuw%&uiuw%Sjuw%&gjuw%gfZy%&chZy%khZy%&shZy%QiZy%&SiZy%qkZy%&clZy%emZy%&umZy%wnZy%&[pZy%]qZy%&}qZy%akz{%&emz{%Wnz{%&_nz{%gnz{%&wnz{%Yoz{%&ioz{%_zz{%&ozz{%WX{{%&yX{{%YY{{%&][{{%a]{{%&q]{{%mc{{%&_d{{%od{{%&qe{{%Sf{{%&Ug{{%ug{{%&Wh{{%_l{{%&ol{{%qm{{%&Sn{{%Uo{{%&eo{{%gx{{%&wx{{%Q}{{%&a}{{%c~{{%&s~{{%uQ|{%&WR|{%]]|{%&_]|{%m]|{%&}]|{%_b~{%&ob~{%Qc~{%&ac~{%iaQ|%&qaQ|%yaQ|%&SbQ|%_dQ|%&odQ|%kpT|%)##o|Q6#eoyh%)##emz{%#WT+b-#1'##Uy&$Z,#Uy&#'##Uy&$(#Ys*#'##Uy&$w+#oxsX(#'##Uy&$Y*#Uy&#'##Uy&$t(#Uy&#'##Uy&$Y(#c|`$#'##Uy&$X(#Uy&#'##Uy&$W(#Usas&&'##Uy&$i'#YqWklQ@#'##Uy&$h'#WRlo$#'##Uy&$q$#c|`$##crgrRrU-#[\h]ecni$$#]kSWf:#WXelkZU-&#gxc[x7#uqnzl%$sXfzhpat$ioV]ZS``%]sqz)/'##Uy&$Z,#Uy&'##Uy&$(#Ys*'##Uy&$w+#oxsX('##Uy&$Y*#Uy&'##Uy&$t(#Uy&'##Uy&$Y(#c|`$'##Uy&$X(#Uy&%#%#'##Uy&$i''##Ty&$j'#UwSklQ@#Uy&'##Uy&$h'#WRlo$'##Uy&$q$#c|`$#c|`$#Ysrz%%#%#'##q}A$#'##Uy&$-#Tsas&%#%#'##p}A$#'##Ty&$-#eoc{T`xR1''##Uy&$Z*#Uy&'##Uy&$Z,#Uy&%#'##Uy&$Z,#Uy&#Uy&'##Uy&$[,#Uy&sb]iu:%#'##Uy&$(#Ys*#$[Q%")).

Definition HS1s_6 : acs := ltac:(acsb (AXB.acs_of "wv`/C###uu`/%#%#'##q}A$#'##C$)#X'#eyb$#ioZy%$V-$W-$X-#gzR6#UyR6#wpy6#qYs6#eoy6$Y-$Z-$[-$\-$]-#Sv[/%#%#'##q}A$#%#'##3$$'##C$)#C################$^-$_-$`-$a-#V3($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&($[,%U^nyn\*($Z,%U^nyn\*###]S\7$#####Uy\7+#y{\7$##m}\7#-###]}\7+#####cR]7$#%###{|\7+#####k|\7+#####[|\7'#-###y{\7+#umh6###aiuw%$#####ciuw%$#%###qauw%+#gduw%$##[fuw%#o$###yeuw%+#####Qiuw%$#%###ieuw%+#####Yeuw%+#####wduw%'#o$###gduw%+#Quq6###eiuw%%#####_b~{%+%#'##Uy&$[,#u%#'##Uy&$[,w&+###'##Uy&$[,g&+#ywj+#'##Uy&$[,Y'+###'##Uy&$[,W&+#qsj+#'##Uy&$[,u%+#klj+#'##Uy&$[,o%$#k(#'##Uy&$[,i'$###'##Uy&$[,q%%#####ug{{%+%#'##Uy&$Z,#Wz&#'##Uy&$Z,gz&+%#'##Uy&$Z,#Wz&#'##Uy&$Z,Wz&+%#'##Uy&$Z,#Wz&#'##Uy&$Z,Y{&'#eO#'##Uy&$Z,i{&+#a*#'##Uy&$[,e%$#5#'##Uy&$[,U%+%#'##Uy&$Z,#Wz&#'##Uy&$Z,wz&+%#'##Uy&$[,#U%#'##Uy&$Z,a{&'#####gx{{%+#7#'##Uy&$[,g:$###'##Uy&$[,c8$###'##Uy&$[,_6$###'##Uy&$[,[4$###'##Uy&$[,W2$###'##Uy&$[,S0$###'##Uy&$[,}-$###'##Uy&$[,y+$###'##Uy&$[,u)$###'##Uy&$[,q'$###'##Uy&$[,m%$###'##Uy&$[,}$$#a+#'##Uy&$[,Q%%#####_l{{%+%#'##Uy&$Z,#y{&#'##Uy&$Z,[|&+%#'##Uy&$Z,#y{&#'##Uy&$Z,y{&+%#'##Uy&$Z,#y{&#'##Uy&$Z,{|&'#'#'##Uy&$Z,]}&+#YN#'##Uy&$[,s$$#%#'##Uy&$[,c$+%#'##Uy&$Z,#y{&#'##Uy&$Z,k|&+%#'##Uy&$[,#c$#'##Uy&$Z,U}&'#####Q}{{%+#'#'##Uy&$[,SP$###'##Uy&$[,{$$###'##Uy&$[,]$$#a+#'##Uy&$[,_$%#####qm{{%+%#'##Uy&$Z,#m}&#'##Uy&$Z,}}&+%#'##Uy&$Z,#m}&#'##Uy&$Z,m}&+%#'##Uy&$Z,#m}&#'##Uy&$Z,o~&'#'#'##Uy&$Z,QQ'+#_Y$#'##Uy&$[,S$$#%#'##Uy&$[,C+%#'##Uy&$Z,#m}&#'##Uy&$Z,_~&+%#'##Uy&$[,#C#'##Uy&$Z,w~&'#####c~{{%+#'#'##Uy&$[,y{$$###'##Uy&$[,[$$###'##Uy&$[,=$#a+#'##Uy&$[,?%#####Uo{{%+%#'##Uy&$Z,#aQ'#'##Uy&$Z,qQ'+%#'##Uy&$Z,#aQ'#'##Uy&$Z,aQ'+%#'##Uy&$Z,#aQ'#'##Uy&$Z,cR''#'#'##Uy&$Z,sR'+#i^(#'##Uy&$[,3$#%#'##Uy&$[,#+%#'##Uy&$Z,#aQ'#'##Uy&$Z,SR'+'##Uy&$[,#'##Uy&$Z,kR''#####uQ|{%+#'###Wd{{%'#%)'##]9$[,krg[x7#]9$'##]9$[,krg[x7#]9)'##Uy&$[,##Uy&$'##Uy&$[,5#+$'##Uy&$[,U$#)$'##Uy&$[,u$#)$'##Uy&$[,g%#)$'##Uy&$[,k'#)$'##Uy&$[,s'#S%$'##Uy&$[,w)#S%$'##Uy&$[,{+#S%$'##Uy&$[,Q.#S%$'##Uy&$[,U0#S%$'##Uy&$[,Y2#S%$'##Uy&$[,]4#S%$'##Uy&$[,a6#S%$'##Uy&$[,e8#S%$'##Uy&$[,i:#i8$'##Uy&$[,UP#uN$'##Uy&$[,{{$#Y|$*'##Uy&$[,##Uy&##c|`$#Ysrz%*'##Uy&$[,##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$[,##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$[,krg[x7#]9##sfo[x7#i}q3*'##]9$[,krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$[,##Uy&##gxc[x7#WVltmors$*'##Uy&$Z,##Ys*'##Uy&$[,##Uy&*'##Uy&$w+##oxsX('##Uy&$[,##Uy&*'##Uy&$Y*##Uy&'##Uy&$[,##Uy&*'##Uy&$t(##Uy&'##Uy&$[,##Uy&*'##Uy&$Y(##c|`$'##Uy&$[,##Uy&*'##Uy&$X(##Uy&'##Uy&$[,##Uy&*'##Uy&$W(##Usas&'##Uy&$[,##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$[,##Uy&*'##Uy&$h'##WRlo$'##Uy&$[,##Uy&*'##Uy&$q$##c|`$'##Uy&$[,##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$[,##Uy&*#]kSWf:##WXelkZU-'##Uy&$[,##Uy&*#gxc[x7##uqnzl%'##Uy&$[,##Uy&($[,%U^nyn\*###]]|{%$#%###Qe{{%+#['###od{{%+%#'##Uy&$Z,#US'#'##Uy&$Z,uy&'#c'#'##Uy&$Z,Uy&+*#<3+###cf{{%+%#'##Uy&$Z,#Uy&###Sf{{%+%#'##Uy&$Z,#Uy&###sf{{%+%#'##Uy&$Z,#Ys*###ae{{%+##)'##]9$Z,wZh[x7#]9$'##]9$Z,wZh[x7#]9)'##Uy&$Z,Uy&#Uy&$'##Uy&$Z,ey&#3$'##Uy&$Z,}y&#+$'##Uy&$Z,US'#Uq&###qe{{%+#%*'##Uy&$Z,##Ys*##c|`$#Ysrz%*'##Uy&$Z,##Ys*%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z,##Ys*%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z,krg[x7#iO##sfo[x7#i}q3*'##]9$Z,krg[x7#iO%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z,##Ys*##gxc[x7#WVltmors$*'##Uy&$w+##oxsX('##Uy&$Z,##Ys**'##Uy&$Y*##Uy&'##Uy&$Z,##Ys**'##Uy&$t(##Uy&'##Uy&$Z,##Ys**'##Uy&$Y(##c|`$'##Uy&$Z,##Ys**'##Uy&$X(##Uy&'##Uy&$Z,##Ys**'##Uy&$W(##Usas&'##Uy&$Z,##Ys**'##Uy&$i'##YqWklQ@'##Uy&$Z,##Ys**'##Uy&$h'##WRlo$'##Uy&$Z,##Ys**'##Uy&$q$##c|`$'##Uy&$Z,##Ys**#crgrRrU-##[\h]ecni$'##Uy&$Z,##Ys**#]kSWf:##WXelkZU-'##Uy&$Z,##Ys**#gxc[x7##uqnzl%'##Uy&$Z,##Ys*($Z,%S^nyn\*###m]|{%+#[ijUWqnbbqz5###}c{{%'#%###mc{{%+*#<3+###_X]7+###'##Uy&$Y([('###'##Uy&$Y(y''#'#'##Uy&$Y(c$+#####SZ]7+#%###ioZy%+'##Uy&$w+#'##Uy&$X(W&+'##Uy&$w+#'##Uy&$w+w&+#K)'##]9$w+krg[x7#}Ur@$'##]9$w+krg[x7#}Ur@)'##Uy&$w+##oxsX($'##Uy&$w+##w&$'##Uy&$w+Y'#gtsX(*'##Uy&$w+##oxsX(##c|`$#Ysrz%*'##Uy&$w+##oxsX(%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$w+##oxsX(%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$w+krg[x7#}Ur@##sfo[x7#i}q3*'##]9$w+krg[x7#}Ur@%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$w+##oxsX(##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$w+##oxsX(*'##Uy&$t(##Uy&'##Uy&$w+##oxsX(*'##Uy&$Y(##c|`$'##Uy&$w+##oxsX(*'##Uy&$X(##Uy&'##Uy&$w+##oxsX(*'##Uy&$W(##Usas&'##Uy&$w+##oxsX(*'##Uy&$i'##YqWklQ@'##Uy&$w+##oxsX(*'##Uy&$h'##WRlo$'##Uy&$w+##oxsX(*'##Uy&$q$##c|`$'##Uy&$w+##oxsX(*#crgrRrU-##[\h]ecni$'##Uy&$w+##oxsX(*#]kSWf:##WXelkZU-'##Uy&$w+##oxsX(*#gxc[x7##uqnzl%'##Uy&$w+##oxsX(($w+%_mkyn\*#'##Uy&$X(u%+#yoZy%#'##Uy&$X(C+%#%#'##q}A$#'##Uy&$-#Tsas&#'##Uy&$X(3+%#'##q}A$#'##Uy&$-#'##Uy&$X(e%+#}m\y%#'##Uy&$X(U%+#yc\y%*'##Uy&$Z*##Uy&##c|`$#Ysrz%*'##Uy&$Z*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z*krg[x7#]9##sfo[x7#i}q3*'##]9$Z*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z*##Uy&##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$Z*##Uy&*'##Uy&$t(##Uy&'##Uy&$Z*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Z*##Uy&*'##Uy&$X(##Uy&'##Uy&$Z*##Uy&*'##Uy&$W(##Usas&'##Uy&$Z*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Z*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Z*##Uy&*'##Uy&$q$##c|`$'##Uy&$Z*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Z*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Z*##Uy&*#gxc[x7##uqnzl%'##Uy&$Z*##Uy&($Z*%U^nyn\*###ekeC$#%#'##Uy&$Y*c$+###'##Uy&$Y*S$+#ioZy%###[dz6$#####]dz6&#####}geC+#%###yoZy%+'##Uy&$Y*)'##Uy&$Y*##Uy&$'##Uy&$Y*##S$$'##Uy&$Y*s$#aw&*'##Uy&$Y*##Uy&##c|`$#Ysrz%*'##Uy&$Y*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y*krg[x7#]9##sfo[x7#i}q3*'##]9$Y*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y*##Uy&##gxc[x7#WVltmors$*'##Uy&$t(##Uy&'##Uy&$Y*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Y*##Uy&*'##Uy&$X(##Uy&'##Uy&$Y*##Uy&*'##Uy&$W(##Usas&'##Uy&$Y*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Y*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Y*##Uy&*'##Uy&$q$##c|`$'##Uy&$Y*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Y*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Y*##Uy&*#gxc[x7##uqnzl%'##Uy&$Y*##Uy&($Y*%U^nyn\*#'##Uy&$X(s$$###'##Uy&$X(c$+###'##Uy&$X(S$+#####QiZy%$#%###_dQ|%+'##Uy&$Y(#'##Uy&$X(#+'##Uy&$Y(#'##Uy&$Y(m)+'##Uy&$X(#'##Uy&$Y(S($#%###QY]7+#%#'##Uy&$Y(s$+###'##Uy&$Y(C+#####qY]7+#%###aY]7+#%#'##Uy&$t(#+'##Uy&$Y(###U[]7+#%###sZ]7+#Uy&###cZ]7+'##Uy&$t()'##Uy&$t(##Uy&$'##Uy&$t(3#sx&*'##Uy&$t(##Uy&##c|`$#Ysrz%*'##Uy&$t(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$t(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$t(krg[x7#]9##sfo[x7#i}q3*'##]9$t(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$t(##Uy&##gxc[x7#WVltmors$*'##Uy&$Y(##c|`$'##Uy&$t(##Uy&*'##Uy&$X(##Uy&'##Uy&$t(##Uy&*'##Uy&$W(##Usas&'##Uy&$t(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$t(##Uy&*'##Uy&$h'##WRlo$'##Uy&$t(##Uy&*'##Uy&$q$##c|`$'##Uy&$t(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$t(##Uy&*#]kSWf:##WXelkZU-'##Uy&$t(##Uy&*#gxc[x7##uqnzl%'##Uy&$t(##Uy&($t(%U^nyn\*###uS]7+###'##Uy&$Y(#+#gTS6#'##Uy&$Y(e)%#iO#'##Uy&$Y(])'###'##Uy&$Y(S$'###'##Uy&$Y(3'###'##Uy&$Y(U%$###'##Uy&$Y({(+###'##Uy&$Y(k('###'##Uy&$Y(c('#####wT]7+%#'##Uy&$Y(#})###gT]7+%#'##Uy&$Y(#c|`$)'##Uy&$Y(##c|`$$'##Uy&$Y(;#+$'##Uy&$Y([$#+$'##Uy&$Y(W%#s%$'##Uy&$Y(U(#)$'##Uy&$Y(s(#+$'##Uy&$Y(i)#'$'##Uy&$Y(})#eu`$*'##Uy&$Y(##c|`$##c|`$#Ysrz%*'##Uy&$Y(##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y(##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y(krg[x7#Ys*##sfo[x7#i}q3*'##]9$Y(krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y(##c|`$##gxc[x7#WVltmors$*'##Uy&$X(##Uy&'##Uy&$Y(##c|`$*'##Uy&$W(##Usas&'##Uy&$Y(##c|`$*'##Uy&$i'##YqWklQ@'##Uy&$Y(##c|`$*'##Uy&$h'##WRlo$'##Uy&$Y(##c|`$*'##Uy&$q$##c|`$'##Uy&$Y(##c|`$*#crgrRrU-##[\h]ecni$'##Uy&$Y(##c|`$*#]kSWf:##WXelkZU-'##Uy&$Y(##c|`$*#gxc[x7##uqnzl%'##Uy&$Y(##c|`$($Y(%e]nyn\*###{V]7'#####kV]7'#####[V]7+#####yU]7+#####eS]7+#YU]7###sR]7$#%###qU]7'#####iU]7'#####YU]7+#####UW]7'#####sV]7'#####US]7+#]W]7###w\]7+#####g\]7+#####W\]7+#####u[]7+#####e[]7+#####[^]7'#####y]]7+#####i]]7+#####Y]]7+#####wX]7'#####oX]7'#####}W]7'#####mW]7+#[ijUWqnbbqz5###]W]7+#Ue`,)'##Uy&$X(##Uy&$'##Uy&$X(u$#1$'##Uy&$X(g&#mu&*'##Uy&$X(##Uy&##c|`$#Ysrz%*'##Uy&$X(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$X(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$X(krg[x7#]9##sfo[x7#i}q3*'##]9$X(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$X(##Uy&##gxc[x7#WVltmors$*'##Uy&$W(##Usas&'##Uy&$X(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$X(##Uy&*'##Uy&$h'##WRlo$'##Uy&$X(##Uy&*'##Uy&$q$##c|`$'##Uy&$X(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$X(##Uy&*#]kSWf:##WXelkZU-'##Uy&$X(##Uy&*#gxc[x7##uqnzl%'##Uy&$X(##Uy&($X(%U^nyn\*###qieC+#Shx-###Wnz{%'#%###_zz{%+#Shx-###Yoz{%+#i_Z4###gnz{%+#wnz{%###]weC$#####YS\7$#%###[S\7$#%###yY}6+#kTr^uUS(###_Z}6%#S|$###[Z}6%#C###cZ}6$#%###}lz6$#####{lz6$#####uiz6+#]Uj8###eiz6+#yrT{`%###Uiz6+#uqnzl%###uwy6+'##Uy&$W(###wxy6+#ufZ%###gxy6+#Usas&###Wxy6+'##Uy&$W(*'##Uy&$W(##Usas&##c|`$#Ysrz%*'##Uy&$W(##Usas&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$W(##Usas&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$W(krg[x7#]Uj8##sfo[x7#i}q3*'##]9$W(krg[x7#]Uj8%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$W(##Usas&##gxc[x7#WVltmors$*'##Uy&$i'##YqWklQ@'##Uy&$W(##Usas&*'##Uy&$h'##WRlo$'##Uy&$W(##Usas&*'##Uy&$q$##c|`$'##Uy&$W(##Usas&*#crgrRrU-##[\h]ecni$'##Uy&$W(##Usas&*#]kSWf:##WXelkZU-'##Uy&$W(##Usas&*#gxc[x7##uqnzl%'##Uy&$W(##Usas&($W(%Ualyn\*###ewy6+#Uy&###cvy6'#[ijUWqnbbqz5###WZ\7+#Uy&###uY\7+#%)%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&$%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&###svy6+%#%#'##Uy&$i''##Ty&$j'#UwSklQ@###Svy6+%#%#'##Uy&$i''##Ty&$j'#c|`$($j'#A(%#'##Ty&$j'%,'##Uy&$i'#a|`$#####auy6+#a_}$###Quy6+#YqWklQ@###oty6+'##Uy&$i'*'##Uy&$i'##YqWklQ@##c|`$#Ysrz%*'##Uy&$i'##YqWklQ@%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$i'##YqWklQ@%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$i'krg[x7#iwh|vm&##sfo[x7#i}q3*'##]9$i'krg[x7#iwh|vm&%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$i'##YqWklQ@##gxc[x7#WVltmors$*'##Uy&$h'##WRlo$'##Uy&$i'##YqWklQ@*'##Uy&$q$##c|`$'##Uy&$i'##YqWklQ@*#crgrRrU-##[\h]ecni$'##Uy&$i'##YqWklQ@*#]kSWf:##WXelkZU-'##Uy&$i'##YqWklQ@*#gxc[x7##uqnzl%'##Uy&$i'##YqWklQ@($i'_|UrqLS_Yz_\*###Uwy6$#####QvVB$#%###yaQ|%'#####Qc~{%+#mej+###iaQ|%'#####iUW7'#####qkZy%+#_dQ|%###aUW7$#%###y{X7+#krg[x7###qSW7$#%###mSW7$#%###uSW7'#Q0###_TW7+'##Uy&$h'###}SW7+#_TW7)'##Uy&$h'##WRlo$$'##Uy&$h'##WRlo$*'##Uy&$h'##WRlo$##c|`$#Ysrz%*'##Uy&$h'##WRlo$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$h'##WRlo$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$h'krg[x7#cbk,##sfo[x7#i}q3*'##]9$h'krg[x7#cbk,%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$h'##WRlo$##gxc[x7#WVltmors$*'##Uy&$q$##c|`$'##Uy&$h'##WRlo$*#crgrRrU-##[\h]ecni$'##Uy&$h'##WRlo$*#]kSWf:##WXelkZU-'##Uy&$h'##WRlo$*#gxc[x7##uqnzl%'##Uy&$h'##WRlo$($h'%kdmyn\*###oSW7$#%###muVB+#aYQ,###[ph6+#3###[|X7'#%###o~dC$#####]qh6'#'###q~dC&#####[feC+#S|j+###QieC+#]SQ,###aieC+#Yw~+###iS\7+#_{RYQ`xR1###sT\7'#_$###YUW7$#%###QUW7'#'###S`}6$#%###QQeC+#%###aQeC+#####qQeC+#####SReC+#Wnq$###cReC+#SRclYZ>###sReC+#####USeC+#####eSeC+#####uSeC+#####WTeC+#eZu]oQT(###gTeC+#ic`gqL###wTeC+#####YUeC+#####iUeC+#####yUeC+#e|`$###[VeC+#[ijUWqnbbqz5###kVeC+#seg$###{VeC+#W.###]WeC+#####mWeC+#####}WeC+#####_XeC+#####oXeC+#sV[mdumbbqz5###QYeC+#%###aYeC+#wer$###qYeC+#Wnq$###SZeC+#Wnq$###cZeC+#cZu]oQT(###sZeC+#####U[eC+#skm%###e[eC+#_lu`ojeryc&###u[eC+#m`lXmogwyc&###W\eC+#soTi*###g\eC+#WgSugQT(###w\eC+#WmX%###Y]eC+#wTUaQoqT?###Q]}6'#iO###w\}6'#W.###kV]C'#####]uVB+%#'##Uy&$q$#au5###cjuw%%#####Sjuw%+#Wnq$###qiuw%%#####}}tw%'#%###{|tw%'#Y.###k|tw%+#yohneogwyc&###c|tw%'#####[|tw%$#####m}tw%+#Wnq$###]}tw%'#%###Y}tw%$#####U}tw%%#####k`}6$#####i]}6$#####Ya}6+#Wnq$###Qa}6'#'###w`}6$#%###o`}6'#####g`}6%#%###W`}6+#UX\Wmogwyc&###u_}6)#ic`gqL###U`}6$#####k^}6'#Uy&###c^}6$#####S^}6+#WTqqVW5###q]}6+#c]YXssfwyc&###a]}6'#S|$###e_}6+#####]_}6$#%###U_}6'#q&###s^}6+#Whm\Y]s&###Y]}6'#C###o\}6'#gc`gqL###ia}6'#kYa$###{tVB+%#'##Uy&$q$#c|`$)'##Uy&$q$##c|`$$'##Uy&$q$c|`$##*'##Uy&$q$##c|`$##c|`$#Ysrz%*'##Uy&$q$##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$q$##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$q$krg[x7#Ys*##sfo[x7#i}q3*'##]9$q$krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$q$##c|`$##gxc[x7#WVltmors$*#crgrRrU-##[\h]ecni$'##Uy&$q$##c|`$*#]kSWf:##WXelkZU-'##Uy&$q$##c|`$*#gxc[x7##uqnzl%'##Uy&$q$##c|`$($q$%e]nyn\*###{V]C+#Uy&###kT\7$#%)%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$$%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$)##sfo[x7#i}q3$##sfo[x7#i}q3###[V]C+%#%#'##q}A$#'##C$)#|)###kph6+#[nx%###_S\7$###%#'##q}A$#'##C$)v&+#{hX4#%#'##q}A$#'##C$)V&+$$#%#'##q}A$#'##C$)t%+%#%#'##q}A$#'##C$)#3#%#'##q}A$#'##C$)d%+#kpX4#%#'##q}A$#'##C$)r$+###%#'##q}A$#'##C$)b$+###%#'##q}A$#'##C$)R$+###%#'##q}A$#'##C$)B+###%#'##q}A$#'##C$)2+#####wnZy%+$P###Umz{%+$P###ygZy%+#####igZy%+#wfZy%###YgZy%+#wfZy%###SlZy%+#SlZy%###emZy%+#][{{%###[hZy%'$O($O%QbYy$###khZy%'#'###wX{{%$#%###wfZy%+#wfZy%###YoZy%+#]qZy%###]qZy%+#%###mqZy%+#kl\y%###[Z{{%+#3###yY{{%+#W.###slz{%+#####Slz{%+#c$###kZ{{%+#%###iY{{%+#Qkz{%###clz{%+#3###qkz{%+#####akz{%+#QQ}5###gX{{%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+###{Z{{%+#Uy&###a]{{%+$,###YY{{%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#S$###gfZy%+%#%#'##q}A$#%#'##3$$'##C$)#C#%#'##q}A$#'##C$)T%+%#%#'##q}A$#'##C$)#3($#Wf~eqLgc`gqL($)#Q|$(%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#q+ecy{WywR1a{RYQ`xR1(%#'##Uy&$#%#$$%#$%%#$''##'$)_ixxQmrs$}Zhtmors$(%#'##q}A$#'##C$)U[y{WywR1QsRYQ`xR1(%#'##Uy&$#'##'$)]ixxQmrs$Q[htmors$($$%iO($%#W.($&#syp%($*#syp%($+#ec`gqL($'#{ns(($(uh${Sv-($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&(%#'##Ty&$-%,%#'##C$)#Ur&#YofUWqnbbqz5##)%#'##q}A$#'##C$)Tsas&#Usas&$%#'##q}A$#'##C$)X'#3$%#'##q}A$#'##C$)f&#3#%#'##q}A$#'##C$)#+$$#%#'##q}A$#'##C$)3+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+#%#'##q}A$#'##C$)C+'#%'#%$$%#%#'##q}A$#%#'##3$$%#'##3$%%#$&'##C$)#S+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)S$+#)#%#'##q}A$#%#'##3$$%#'##3$%'##C$)c$+#YQa$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)s$+#+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)U%+#e%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)e%+#-#%#'##q}A$#%#'##3$$%#'##3$%'##C$)u%+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)W&+#C#%#'##q}A$#%#'##3$$%#'##3$%'##C$)g&+$,#%#'##q}A$#%#'##3$$%#'##3$%'##C$)w&+#/#%#'##q}A$#%#'##3$$%#'##3$%'##C$)Y'+#Uy&#%#'##q}A$#%#'##3$$%#'##3$%'##C$)i'+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)y'+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)[(+#;#%#'##q}A$#%#'##3$$%#'##3$%'##C$)k(+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$){(+#Q$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)])+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)m)+#U$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)})+%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#Q+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)_*+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)o*+##%%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)Q+#C<&c|`$[ph6&{ph6]qh6&eqh6oty6&quy6Svy6&kvy6svy6&Wwy6ewy6&Yyy6[dz6&cdz6Uiz6&Wjz6{lz6&Qmz6yY}6&eZ}6o\}6&k]}6q]}6&e^}6k^}6&__}6e_}6&m`}6o`}6&y`}6Qa}6&qa}6ug}6&uQT7mSW7&sSW7uSW7&oTW7QUW7&[UW7aUW7&cUW7iUW7&qUW7y{X7&c|X7YS\7&aS\7iS\7&yS\7kT\7&mT\7sT\7&{T\7uY\7&gZ\7Uy\7&ey\7y{\7&c|\7k|\7&w}\7cR]7&eR]7sR]7&uR]7US]7&WT]7gT]7&WX]7_X]7&c^]7{tVB&}uVBQvVB&SvVB[V]C&sV]C{V]C&]W]C_X]C&aRaCcRaC&ezdCo~dC&w~dCQQeC&i]eC[feC&kfeC}geC&_heCQieC&SjeCekeC&gkeC]weC&_weC[|tw%&]|tw%c|tw%&[}tw%]}tw%&e}tw%m}tw%&W~tw%qauw%&Sbuw%gduw%&Qeuw%Yeuw%&yguw%Qiuw%&Siuw%aiuw%&iiuw%qiuw%&uiuw%Sjuw%&gjuw%gfZy%&chZy%khZy%&shZy%QiZy%&SiZy%qkZy%&clZy%emZy%&umZy%wnZy%&[pZy%]qZy%&}qZy%akz{%&emz{%Wnz{%&_nz{%gnz{%&wnz{%Yoz{%&ioz{%_zz{%&ozz{%WX{{%&yX{{%YY{{%&][{{%a]{{%&q]{{%mc{{%&_d{{%od{{%&Ug{{%ug{{%&Wh{{%_l{{%&ol{{%qm{{%&Sn{{%Uo{{%&eo{{%gx{{%&wx{{%Q}{{%&a}{{%c~{{%&s~{{%uQ|{%&WR|{%]]|{%&_]|{%m]|{%&}]|{%_b~{%&ob~{%Qc~{%&ac~{%iaQ|%&qaQ|%yaQ|%&SbQ|%_dQ|%&odQ|%kpT|%)##o|Q6#eoyh%)##emz{%#WT+b-#1'##Uy&$[,#Uy&#'##Uy&$Z,#Ys*#'##Uy&$w+#oxsX(#'##Uy&$Y*#Uy&#'##Uy&$t(#Uy&#'##Uy&$Y(#c|`$#'##Uy&$X(#Uy&#'##Uy&$W(#Usas&&'##Uy&$i'#YqWklQ@#'##Uy&$h'#WRlo$#'##Uy&$q$#c|`$##crgrRrU-#[\h]ecni$$#]kSWf:#WXelkZU-&#gxc[x7#uqnzl%$sXfzhpat$ioV]ZS``%Yymz)/'##Uy&$[,#Uy&%#'##Uy&$Z,#Uy&#Uy&'##Uy&$w+#oxsX('##Uy&$Y*#Uy&'##Uy&$t(#Uy&'##Uy&$Y(#c|`$'##Uy&$X(#Uy&%#%#'##Uy&$i''##Ty&$j'#UwSklQ@#Uy&'##Uy&$h'#WRlo$'##Uy&$q$#c|`$#c|`$#Ysrz%%#%#'##q}A$#'##Uy&$-#Tsas&%#%#'##p}A$#'##Ty&$-#eoc{T`xR1''##Uy&$Z*#Uy&'##Uy&$Z,#Uy&%#'##Uy&$Z,#Uy&#Uy&'##Uy&$[,#Uy&cRYiu:'##Uy&$(#$[Q%")).

Definition HS1s (h : nat) : option acs :=
match h with | 0%nat => Some HS1s_0 | 6%nat => Some HS1s_6 | _ => None end.
End Mq4.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QqZL.Mq3.
Import QiyH.Mq6 QCoy.Mq8.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition istrncpy_words : list (bv 32) :=
[W_757b4; W_757b8; W_757bc; W_757c0; W_757c4; W_757c8; W_757cc; W_757d0;
W_757d4; W_757d8; W_757dc; W_757e0; W_757e4; W_757e8; W_757ec; W_757f0;
W_757f4; W_757f8; W_757fc; W_75800; W_75804; W_75808; W_7580c; W_75810;
W_75814; W_75818; W_7581c; W_75820].

Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].

Definition sealed8 : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e].
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.

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

Section ISTRNCPY.
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
| eapply QHup.Mq1.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
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
+ mzsb C68 D_757f8 k.
an C72 D_757fc.
ab_ft C76 D_75800 ltac:(condz).
an C80 D_75804.
aret C108 D_75820 ret.
mz_at 4087%Z. apply mst_refl.
+ unfold istrncpy_clob. solve_regs_agree.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
+ eexists. split.
* mzsb C68 D_757f8 k.
an C72 D_757fc.
ab_tk C76 D_75800 ltac:(condz).
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
- av C8 D_757bc (at_ src j) ltac:(apply v_add_at; lia).
mlbu C12 D_757c0 j.
ab_ft C16 D_757c4
ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
apply sealed8_nz; lia).
av C20 D_757c8 (at_ dst j) ltac:(apply v_add_at; lia).
an C24 D_757cc.
msb C28 D_757d0 j.
ab_tk C32 D_757d4 ltac:(condv).
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
- ab_ft C0 D_757b4 ltac:(condz).
an C4 D_757b8.
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
- av C8 D_757bc (at_ src 8) ltac:(apply v_add_at; lia).
chain_step; [reflexivity
| eapply step_lbu with (b := Z_to_bv 8 0);
[exact C12 | reflexivity | exact D_757c0
| gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
rewrite rdn_wbytes_out;
[ exact Hnul
| change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
| change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
| step_simpl]; vn.
ab_tk C16 D_757c4 ltac:(condz).
change (memk mem0 dst sealed8 8) with (MZ 0).
av C40 D_757dc (at_ dst 8) ltac:(apply v_add_at; lia).
an C44 D_757e0.

an C48 D_757e4.
av C52 D_757e8 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
ab_ft C56 D_757ec ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
ab_ft C60 D_757f0 ltac:(condz).
av C64 D_757f4 (at_ dst 4095) ltac:(apply v_add_at; lia).
apply mst_refl.
- post.
+ rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
+ unfold istrncpy_clob in *. ra_chain. }
cbv beta. intros r9 (M1 & M11 & M12 & K9).
destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End ISTRNCPY.

Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Definition asan_istrncpy_entry : word := 0x75774.
Definition asan_sealed_src : Z := 0x11afc.

Lemma asan_istrncpy_code :
code_at AsanUbsan.M.loaded_segments asan_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

Lemma asan_sealed_src_img : forall mem,
(forall i, (asan_sealed_src <= i < asan_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
rdn AsanUbsan.M.loaded_segments mem (Z_to_bv 64 asan_sealed_src) 8 = Some sealed8
/\ rdn AsanUbsan.M.loaded_segments mem (at_ (Z_to_bv 64 asan_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
intros mem Hnone. unfold asan_sealed_src in *. split.
- rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem asan_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
(forall i, (asan_sealed_src <= i < asan_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
store_ok AsanUbsan.M.loaded_segments mem0 dst 4095%nat = true ->
(bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
(bv_unsigned dst + 4095 <= asan_sealed_src \/ asan_sealed_src + 9 <= bv_unsigned dst)%Z ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 asan_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
exists regs',
msteps AsanUbsan.M.loaded_segments
(mkst regs asan_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
/\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
destruct (asan_sealed_src_img mem0 Hnone) as [Hs Hn].
rewrite <- (at_0 asan_istrncpy_entry).
apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 asan_sealed_src) rom asan_istrncpy_code Hs Hn); try assumption;
unfold asan_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1 Q85Z.Mq2 QHup.Mq1 QG64.Mq3.
Import QWZn.Mq0 Qrlk.Mq1 QJJu.Mq1 QCoy.Mqa QCoy.Mqb QCoy.Mqc QiyH.Mq4.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ALL.
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

Ltac conda := rwH; unfold at_; cond.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma al_finish : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xddb30 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
set (m := ((n - k) mod 16)%Z).
pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddb6c : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddb8c : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdddd0 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R | eapply keeps_trans; eassumption].
Qed.

Lemma mis_run : forall regs (ret : word) k q,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
(0 <= k <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda60 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
-
destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda68 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddaac D_ddaac.
stepb_ft F_ddab0 D_ddab0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
set (m := (n - k)%Z) in *.
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdddd0 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda84 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_ddaac D_ddaac.
stepb_tk F_ddab0 D_ddab0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
assert (CASE : exists regs' m,
msteps JOB6SEGS (mkst r1 (0xdda84 : word) (MK k) rom)
(mkst regs' (0xdddd0 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
{ destruct Hq as [-> | [-> | ->]].
- apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

Lemma j_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda58 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
pose proof (u64_range dst).
set (q := ((bv_unsigned dst + k) mod 4)%Z).
pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
destruct (Z.eq_dec q 0) as [Hq0|Hq0].
-
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddb30 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_ddaa4 D_ddaa4.
stepb_tk F_ddaa8 D_ddaa8 ltac:(conda).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
- eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda60 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_ddaa4 D_ddaa4.
stepb_ft F_ddaa8 D_ddaa8 ltac:(conda).
apply mst_refl.
* cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
change (bv_wrap 64 3) with 3%Z. reflexivity.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

Lemma hl_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
(Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda28 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
-
pose proof (u64_range src).
destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
+ eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda58 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_dda74 D_dda74 k.
stepn F_dda78 D_dda78.
stepn F_dda7c D_dda7c.
stepn F_dda80 D_dda80.
msb F_dda84 D_dda84 k ltac:(apply sb_val_plain).
stepn F_dda88 D_dda88.
stepn F_dda8c D_dda8c.
stepb_tk F_dda90 D_dda90 ltac:(conda).
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda58 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_dda74 D_dda74 k.
stepn F_dda78 D_dda78.
stepn F_dda7c D_dda7c.
stepn F_dda80 D_dda80.
msb F_dda84 D_dda84 k ltac:(apply sb_val_plain).
stepn F_dda88 D_dda88.
stepn F_dda8c D_dda8c.
stepb_ft F_dda90 D_dda90 ltac:(conda).
stepn F_dda94 D_dda94.
stepb_ft F_dda98 D_dda98 ltac:(cond).
stepn F_dda9c D_dda9c.
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
pose proof (u64_range src).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda28 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
/\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
+ eexists. split.
* mlbu F_dda74 D_dda74 k.
stepn F_dda78 D_dda78.
stepn F_dda7c D_dda7c.
stepn F_dda80 D_dda80.
msb F_dda84 D_dda84 k ltac:(apply sb_val_plain).
stepn F_dda88 D_dda88.
stepn F_dda8c D_dda8c.
stepb_ft F_dda90 D_dda90 ltac:(conda).
stepn F_dda94 D_dda94.
stepb_tk F_dda98 D_dda98 ltac:(cond).
apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

Theorem ref_memcpy : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps JOB6SEGS (mkst regs (0xdda10 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ keeps regs regs'.
Proof.
intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
-
destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
+ eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xddb30 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_dda5c D_dda5c.
stepb_tk F_dda60 D_dda60 ltac:(conda).
stepn F_ddb70 D_ddb70.
stepn F_ddb74 D_ddb74.
stepb_ft F_ddb78 D_ddb78 ltac:(cond).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda60 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
* eexists. split.
-- stepn F_dda5c D_dda5c.
stepb_tk F_dda60 D_dda60 ltac:(conda).
stepn F_ddb70 D_ddb70.
stepn F_ddb74 D_ddb74.
stepb_tk F_ddb78 D_ddb78 ltac:(cond).
apply mst_refl.
-- cbv beta. post; try (rewrite at_0; reflexivity).
unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
+ eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda58 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_dda5c D_dda5c.
stepb_ft F_dda60 D_dda60 ltac:(conda).
stepb_tk F_dda64 D_dda64 ltac:(cond).
stepn F_ddaa0 D_ddaa0.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
eapply (runs_trans JOB6SEGS _ (fun r => mkst r (0xdda28 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
* eexists. split.
-- stepn F_dda5c D_dda5c.
stepb_ft F_dda60 D_dda60 ltac:(conda).
stepb_ft F_dda64 D_dda64 ltac:(cond).
stepn F_dda68 D_dda68.
stepn F_dda6c D_dda6c.
stepn F_dda70 D_dda70.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
{ subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

End ALL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n QOTP.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition job6_stage2_r0_1 : plan :=
PRun [0x4c9ac]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x919d0]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 1 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition job6_stage2_r1_2 : plan :=
PRun [0x4c9ac]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x919d0]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 2 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition job6_stage2 : plan :=
PBump 478
(PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 4030
(job6_stage2_r0_1)
(job6_stage2_r1_2)).

Definition job6_stage2_ranges : list (Z * nat) := [(0x3e000, 1008%nat); (0x4bfc0, 4096%nat); (0x63fc0, 2048%nat); (0x68fc0, 1024%nat); (0x6afc0, 1024%nat); (0x6cfc0, 1024%nat); (0x6efc0, 1024%nat); (0x70fc0, 1024%nat); (0x74fc0, 1024%nat); (0x76fc0, 2048%nat); (0x7cfc0, 1024%nat); (0x80fc0, 4096%nat); (0x90fc0, 1024%nat); (0x92fc0, 1024%nat); (0xcdfc0, 1021%nat); (0xdcfb4, 1024%nat); (0xdefb4, 1024%nat)]%Z.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n QOTP.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition job6_stage2b_r0_1 : plan :=
PRun [0x4c9ac]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x919d0]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 3 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition job6_stage2b_r1_2 : plan :=
PRun [0x4c9ac]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x919d0]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 4 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition job6_stage2b : plan :=
PBump 478
(PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 4030
(job6_stage2b_r0_1)
(job6_stage2b_r1_2)).

Definition job6_stage2b_ranges : list (Z * nat) := [(0x3e000, 1008%nat); (0x4bfc0, 4096%nat); (0x63fc0, 2048%nat); (0x68fc0, 1024%nat); (0x6afc0, 1024%nat); (0x6cfc0, 1024%nat); (0x6efc0, 1024%nat); (0x70fc0, 1024%nat); (0x74fc0, 1024%nat); (0x76fc0, 2048%nat); (0x7cfc0, 1024%nat); (0x80fc0, 4096%nat); (0x90fc0, 1024%nat); (0x92fc0, 1024%nat); (0xcdfc0, 1021%nat); (0xdcfb4, 1024%nat); (0xdefb4, 1024%nat)]%Z.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import Qt8n QOTP.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition job6_startup1s_brkfail1 : plan :=
PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 9 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PRun []
(PMprotect
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 8 )))))))))))))
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 7 )))))))))))))
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (EVar 424) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 6 )))))))))))))))))))).

Definition job6_startup1s_tail2 : plan :=
PRun [0x7dcec]
(PRespell 10 (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10)))
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 374
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemcpy []
(PRun []
(PSys YBrk
(PRun []
(PSplit (EVar 5) 524276
(PBrk2
(job6_startup1s_brkfail1)
(PRun []
(PMmapIn
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 3 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 2 )))))))))))))))))
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 1 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 0 )))))))))))))))))
(PRun []
(PMmap
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 5 )))))))))))))))
(PGhost (escale 4096 (EVar 423)) (ELit 4096)
(PGhost (eaddz (escale 4096 (EVar 423)) 4096) (ELit 4096)
(PIntro 1 34359736319
(PGhost (escale 4096 (EVar 424)) (ELit 4096)
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x932ac]
(PBump 465
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PFact (KRange (EVar 423) 1 34359736319)
(PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 0 4095)
(PFact (KRange (EVar 10) 0 8)
(PHandoff 4 ))))))))))))))))))))
(PSys YBrk
(job6_startup1s_brkfail1)))))))))))))))))).

Definition job6_startup1s_s2A3 : plan :=
PBump 364
(job6_startup1s_tail2).

Definition job6_startup1s_tospin4 : plan :=
PRun []
(PX XIMemset []
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78ae4]
(PFresh 21 0 None
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun [0x78c74]
(PDiamond 0x78c4c [16]%nat
(PRun []
(PSpin ))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition job6_startup1s : plan :=
PRun []
(PX XIMemset []
(PRun []
(PX XEnvScan []
(PRun []
(PX XPnScan []
(PRun []
(PX XIMemcpy []
(PRun []
(PSys YSetTid
(PRun []
(PRun [0xcea48]
(PExt 1 [ELit 6575456; ELit 8]
(PRun [0x76990]
(PExt 2 []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x75774]
(PX XIStrncpy []
(PRun [0x75774]
(PX XIStrncpy []
(PRun [0x6ac98]
(PDropRange (ELit 1580160) (ELit 0xfff) (PDropRange (ELit 1584256) (ELit 0xfff)
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun [0x6ac9c]
(PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
(PRun [0x76990]
(PExt 2 []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x6ad60]
(PDropRange (ELit 981688) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x7d7b8]
(PFresh 9 12 None
(PRun []
(PMmapIn
(job6_startup1s_tospin4)
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 220
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun [0x64c54]
(PDiamond 0x64e80 []%nat
(PBump 249
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemIsZero []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PSys YMunmap
(PSplit (EVar 10) 0
(job6_startup1s_s2A3)
(PSplit (EVar 10) 7
(job6_startup1s_s2A3)
(job6_startup1s_s2A3)))))))))))))))))))))))))))))))))))))))
(job6_startup1s_tospin4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition job6_startup1s_ranges : list (Z * nat) := [(0x3e000, 1008%nat); (0x3ffc0, 2048%nat); (0x43fc0, 2048%nat); (0x49fc0, 3072%nat); (0x4efc0, 1024%nat); (0x54fc0, 1024%nat); (0x56fc0, 8192%nat); (0x60fc0, 5120%nat); (0x68fc0, 7168%nat); (0x70fc0, 8192%nat); (0x79fc0, 6144%nat); (0x80fc0, 1024%nat); (0x8afc0, 2048%nat); (0x8dfc0, 1024%nat); (0x90fc0, 1024%nat); (0x92fc0, 1024%nat); (0xcdfc0, 4093%nat); (0xd3fb4, 1024%nat); (0xdcfb4, 4096%nat)]%Z.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n.
Import QOTP.
Import QqZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HS1s_0 : acs := ltac:(acsb (AXB.acs_of "isb/C###grb/%#%#'##q}A$#'##C$)#X'#eyb$#wRdy%$V-$W-$X-#W^\6#s\\6#WTU7#cl|6#WTU7$Y-$Z-$[-$\-$]-#wr\/%#%#'##q}A$#%#'##3$$'##C$)#C################$^-$_-$`-$a-#~2($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&($Z,%U^nyn\*###kde7$#####c\f7+#Y_f7$##{`f7#-###k`f7+#####qcf7$#%###[`f7+#####y_f7+#####i_f7'#-###Y_f7+#yaq6###oz~w%$#####qz~w%$#%###Qs~w%+#uu~w%$##iw~w%#o$###Yw~w%+#####_z~w%$#%###wv~w%+#####gv~w%+#####Wv~w%'#o$###uu~w%+#Uiz6###sz~w%%#####msY|%+%#'##Uy&$Z,#u%#'##Uy&$Z,w&+###'##Uy&$Z,g&+#otk+#'##Uy&$Z,Y'+###'##Uy&$Z,W&+#gpk+#'##Uy&$Z,u%+#aik+#'##Uy&$Z,o%$#k(#'##Uy&$Z,i'$###'##Uy&$Z,q%%#####UyV|%+%#'##Uy&$(#Wz&#'##Uy&$(gz&+%#'##Uy&$(#Wz&#'##Uy&$(Wz&+%#'##Uy&$(#Wz&#'##Uy&$(Y{&'#eO#'##Uy&$(i{&+#a*#'##Uy&$Z,e%$#5#'##Uy&$Z,U%+%#'##Uy&$(#Wz&#'##Uy&$(wz&+%#'##Uy&$Z,#U%#'##Uy&$(a{&'#####u[W|%+#7#'##Uy&$Z,g:$###'##Uy&$Z,c8$###'##Uy&$Z,_6$###'##Uy&$Z,[4$###'##Uy&$Z,W2$###'##Uy&$Z,S0$###'##Uy&$Z,}-$###'##Uy&$Z,y+$###'##Uy&$Z,u)$###'##Uy&$Z,q'$###'##Uy&$Z,m%$###'##Uy&$Z,}$$#a+#'##Uy&$Z,Q%%#####m}V|%+%#'##Uy&$(#y{&#'##Uy&$([|&+%#'##Uy&$(#y{&#'##Uy&$(y{&+%#'##Uy&$(#y{&#'##Uy&$({|&'#'#'##Uy&$(]}&+#YN#'##Uy&$Z,s$$#%#'##Uy&$Z,c$+%#'##Uy&$(#y{&#'##Uy&$(k|&+%#'##Uy&$Z,#c$#'##Uy&$(U}&'#####_`W|%+#'#'##Uy&$Z,SP$###'##Uy&$Z,{$$###'##Uy&$Z,]$$#a+#'##Uy&$Z,_$%#####QQW|%+%#'##Uy&$(#m}&#'##Uy&$(}}&+%#'##Uy&$(#m}&#'##Uy&$(m}&+%#'##Uy&$(#m}&#'##Uy&$(o~&'#'#'##Uy&$(QQ'+#_Y$#'##Uy&$Z,S$$#%#'##Uy&$Z,C+%#'##Uy&$(#m}&#'##Uy&$(_~&+%#'##Uy&$Z,#C#'##Uy&$(w~&'#####qaW|%+#'#'##Uy&$Z,y{$$###'##Uy&$Z,[$$###'##Uy&$Z,=$#a+#'##Uy&$Z,?%#####cRW|%+%#'##Uy&$(#aQ'#'##Uy&$(qQ'+%#'##Uy&$(#aQ'#'##Uy&$(aQ'+%#'##Uy&$(#aQ'#'##Uy&$(cR''#'#'##Uy&$(sR'+#i^(#'##Uy&$Z,3$#%#'##Uy&$Z,#+%#'##Uy&$(#aQ'#'##Uy&$(SR'+'##Uy&$Z,#'##Uy&$(kR''#####UcW|%+#'###euV|%'#%($[,%U^nyn\*)'##]9$Z,krg[x7#]9$'##]9$Z,krg[x7#]9)'##Uy&$Z,##Uy&$'##Uy&$Z,5#+$'##Uy&$Z,U$#)$'##Uy&$Z,u$#)$'##Uy&$Z,g%#)$'##Uy&$Z,k'#)$'##Uy&$Z,s'#S%$'##Uy&$Z,w)#S%$'##Uy&$Z,{+#S%$'##Uy&$Z,Q.#S%$'##Uy&$Z,U0#S%$'##Uy&$Z,Y2#S%$'##Uy&$Z,]4#S%$'##Uy&$Z,a6#S%$'##Uy&$Z,e8#S%$'##Uy&$Z,i:#i8$'##Uy&$Z,UP#uN$'##Uy&$Z,{{$#Y|$*'##Uy&$Z,##Uy&##c|`$#agzz%*'##Uy&$Z,##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z,##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z,krg[x7#]9##sfo[x7#S|r3*'##]9$Z,krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z,##Uy&##gxc[x7#WVltmors$*'##Uy&$(##Ys*'##Uy&$Z,##Uy&*'##Uy&$w+##oxsX('##Uy&$Z,##Uy&*'##Uy&$Y*##Uy&'##Uy&$Z,##Uy&*'##Uy&$t(##Uy&'##Uy&$Z,##Uy&*'##Uy&$Y(##c|`$'##Uy&$Z,##Uy&*'##Uy&$X(##Uy&'##Uy&$Z,##Uy&*'##Uy&$W(##Usas&'##Uy&$Z,##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Z,##Uy&*'##Uy&$h'##WRlo$'##Uy&$Z,##Uy&*'##Uy&$q$##c|`$'##Uy&$Z,##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Z,##Uy&*#]kSWf:##WXelkZU-'##Uy&$Z,##Uy&*#gxc[x7##uqnzl%'##Uy&$Z,##Uy&($Z,%U^nyn\*###knW|%$#%###_vV|%+#['###}uV|%+%#'##Uy&$(#US'#'##Uy&$(uy&'#c'#'##Uy&$(Uy&+*#<3+###qwV|%+%#'##Uy&$(#Uy&###awV|%+%#'##Uy&$(#Uy&###SxV|%+%#'##Uy&$(#Ys*###ovV|%+#####{nW|%+%#'##Uy&$(#Ys*)'##]9$(krg[x7#iO$'##]9$(krg[x7#iO)'##Uy&$(Uy&#Uy&$'##Uy&$(ey&#3$'##Uy&$(}y&#+$'##Uy&$(US'#Uq&*'##Uy&$w+##oxsX('##Uy&$(##]m.*'##Uy&$Y*##Uy&'##Uy&$(##]m.*'##Uy&$t(##Uy&'##Uy&$(##]m.*'##Uy&$Y(##c|`$'##Uy&$(##]m.*'##Uy&$X(##Uy&'##Uy&$(##]m.*'##Uy&$W(##Usas&'##Uy&$(##]m.*'##Uy&$i'##YqWklQ@'##Uy&$(##]m.*'##Uy&$h'##WRlo$'##Uy&$(##]m.*'##Uy&$q$##c|`$'##Uy&$(##]m.*#crgrRrU-##[\h]ecni$'##Uy&$(##]m.*#]kSWf:##WXelkZU-'##Uy&$(##]m.*#gxc[x7##uqnzl%'##Uy&$(##]m.($(yh$mit-###]uV|%'#%###{tV|%+*#<3+###mif7+###'##Uy&$Y([('###'##Uy&$Y(y''#'#'##Uy&$Y(c$+#####akf7+#%###wRdy%+'##Uy&$w+#'##Uy&$X(W&+'##Uy&$w+#'##Uy&$w+w&+#K)'##]9$w+krg[x7#}Ur@$'##]9$w+krg[x7#}Ur@)'##Uy&$w+##oxsX($'##Uy&$w+##w&$'##Uy&$w+Y'#gtsX(*'##Uy&$w+##oxsX(##c|`$#agzz%*'##Uy&$w+##oxsX(%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$w+##oxsX(%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$w+krg[x7#}Ur@##sfo[x7#S|r3*'##]9$w+krg[x7#}Ur@%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$w+##oxsX(##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$w+##oxsX(*'##Uy&$t(##Uy&'##Uy&$w+##oxsX(*'##Uy&$Y(##c|`$'##Uy&$w+##oxsX(*'##Uy&$X(##Uy&'##Uy&$w+##oxsX(*'##Uy&$W(##Usas&'##Uy&$w+##oxsX(*'##Uy&$i'##YqWklQ@'##Uy&$w+##oxsX(*'##Uy&$h'##WRlo$'##Uy&$w+##oxsX(*'##Uy&$q$##c|`$'##Uy&$w+##oxsX(*#crgrRrU-##[\h]ecni$'##Uy&$w+##oxsX(*#]kSWf:##WXelkZU-'##Uy&$w+##oxsX(*#gxc[x7##uqnzl%'##Uy&$w+##oxsX(($w+%_mkyn\*#'##Uy&$X(u%+#YSdy%#'##Uy&$X(C+%#%#'##q}A$#'##Uy&$-#Tsas&#'##Uy&$X(3+%#'##q}A$#'##Uy&$-#'##Uy&$X(e%+#]Qfy%#'##Uy&$X(U%+#Yuey%*'##Uy&$Z*##Uy&##c|`$#agzz%*'##Uy&$Z*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z*krg[x7#]9##sfo[x7#S|r3*'##]9$Z*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z*##Uy&##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$Z*##Uy&*'##Uy&$t(##Uy&'##Uy&$Z*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Z*##Uy&*'##Uy&$X(##Uy&'##Uy&$Z*##Uy&*'##Uy&$W(##Usas&'##Uy&$Z*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Z*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Z*##Uy&*'##Uy&$q$##c|`$'##Uy&$Z*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Z*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Z*##Uy&*#gxc[x7##uqnzl%'##Uy&$Z*##Uy&($Z*%U^nyn\*###s|nC$#%#'##Uy&$Y*c$+###'##Uy&$Y*S$+#wRdy%###iuU7$#####kuU7&#####]ynC+#%###YSdy%+'##Uy&$Y*)'##Uy&$Y*##Uy&$'##Uy&$Y*##S$$'##Uy&$Y*s$#aw&*'##Uy&$Y*##Uy&##c|`$#agzz%*'##Uy&$Y*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y*krg[x7#]9##sfo[x7#S|r3*'##]9$Y*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y*##Uy&##gxc[x7#WVltmors$*'##Uy&$t(##Uy&'##Uy&$Y*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Y*##Uy&*'##Uy&$X(##Uy&'##Uy&$Y*##Uy&*'##Uy&$W(##Usas&'##Uy&$Y*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Y*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Y*##Uy&*'##Uy&$q$##c|`$'##Uy&$Y*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Y*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Y*##Uy&*#gxc[x7##uqnzl%'##Uy&$Y*##Uy&($Y*%U^nyn\*#'##Uy&$X(s$$###'##Uy&$X(c$+###'##Uy&$X(S$+#####_zcy%$#%###muZ|%+'##Uy&$Y(#'##Uy&$X(#+'##Uy&$Y(#'##Uy&$Y(m)+'##Uy&$X(#'##Uy&$Y(S($#%###_jf7+#%#'##Uy&$Y(s$+###'##Uy&$Y(C+#####Qkf7+#%###ojf7+#%#'##Uy&$t(#+'##Uy&$Y(###clf7+#%###Slf7+#Uy&###qkf7+'##Uy&$t()'##Uy&$t(##Uy&$'##Uy&$t(3#sx&*'##Uy&$t(##Uy&##c|`$#agzz%*'##Uy&$t(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$t(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$t(krg[x7#]9##sfo[x7#S|r3*'##]9$t(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$t(##Uy&##gxc[x7#WVltmors$*'##Uy&$Y(##c|`$'##Uy&$t(##Uy&*'##Uy&$X(##Uy&'##Uy&$t(##Uy&*'##Uy&$W(##Usas&'##Uy&$t(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$t(##Uy&*'##Uy&$h'##WRlo$'##Uy&$t(##Uy&*'##Uy&$q$##c|`$'##Uy&$t(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$t(##Uy&*#]kSWf:##WXelkZU-'##Uy&$t(##Uy&*#gxc[x7##uqnzl%'##Uy&$t(##Uy&($t(%U^nyn\*###Uef7+###'##Uy&$Y(#+#ue\6#'##Uy&$Y(e)%#iO#'##Uy&$Y(])'###'##Uy&$Y(S$'###'##Uy&$Y(3'###'##Uy&$Y(U%$###'##Uy&$Y({(+###'##Uy&$Y(k('###'##Uy&$Y(c('#####Wff7+%#'##Uy&$Y(#})###uef7+%#'##Uy&$Y(#c|`$)'##Uy&$Y(##c|`$$'##Uy&$Y(;#+$'##Uy&$Y([$#+$'##Uy&$Y(W%#s%$'##Uy&$Y(U(#)$'##Uy&$Y(s(#+$'##Uy&$Y(i)#'$'##Uy&$Y(})#eu`$*'##Uy&$Y(##c|`$##c|`$#agzz%*'##Uy&$Y(##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y(##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y(krg[x7#Ys*##sfo[x7#S|r3*'##]9$Y(krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y(##c|`$##gxc[x7#WVltmors$*'##Uy&$X(##Uy&'##Uy&$Y(##c|`$*'##Uy&$W(##Usas&'##Uy&$Y(##c|`$*'##Uy&$i'##YqWklQ@'##Uy&$Y(##c|`$*'##Uy&$h'##WRlo$'##Uy&$Y(##c|`$*'##Uy&$q$##c|`$'##Uy&$Y(##c|`$*#crgrRrU-##[\h]ecni$'##Uy&$Y(##c|`$*#]kSWf:##WXelkZU-'##Uy&$Y(##c|`$*#gxc[x7##uqnzl%'##Uy&$Y(##c|`$($Y(%e]nyn\*###[hf7'#####ygf7'#####igf7+#####Ygf7+#####sdf7+#gff7###Sdf7$#%###Qgf7'#####wff7'#####gff7+#####chf7'#####Shf7'#####cdf7+#khf7###Wnf7+#####umf7+#####emf7+#####Umf7+#####slf7+#####iof7'#####Yof7+#####wnf7+#####gnf7+#####Wjf7'#####}if7'#####]if7'#####{hf7+#[ijUWqnbbqz5###khf7+#yaa,)'##Uy&$X(##Uy&$'##Uy&$X(u$#1$'##Uy&$X(g&#mu&*'##Uy&$X(##Uy&##c|`$#agzz%*'##Uy&$X(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$X(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$X(krg[x7#]9##sfo[x7#S|r3*'##]9$X(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$X(##Uy&##gxc[x7#WVltmors$*'##Uy&$W(##Usas&'##Uy&$X(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$X(##Uy&*'##Uy&$h'##WRlo$'##Uy&$X(##Uy&*'##Uy&$q$##c|`$'##Uy&$X(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$X(##Uy&*#]kSWf:##WXelkZU-'##Uy&$X(##Uy&*#gxc[x7##uqnzl%'##Uy&$X(##Uy&($X(%U^nyn\*###Q{nC+#wdy-###eQV|%'#%###m]V|%+#wdy-###gRV|%+#Qqc4###uQV|%+#WRV|%###kZoC$#####gde7$#%###ide7$#%###YkX7+#kTr^uUS(###mkX7%#S|$###ikX7%#C###qkX7$#%###]~U7$#####[~U7$#####U{U7+#]Uj8###szU7+#yrT{`%###czU7+#uqnzl%###U[U7+'##Uy&$W(###W\U7+#yrZ%###u[U7+#Usas&###e[U7+'##Uy&$W(*'##Uy&$W(##Usas&##c|`$#agzz%*'##Uy&$W(##Usas&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$W(##Usas&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$W(krg[x7#]Uj8##sfo[x7#S|r3*'##]9$W(krg[x7#]Uj8%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$W(##Usas&##gxc[x7#WVltmors$*'##Uy&$i'##YqWklQ@'##Uy&$W(##Usas&*'##Uy&$h'##WRlo$'##Uy&$W(##Usas&*'##Uy&$q$##c|`$'##Uy&$W(##Usas&*#crgrRrU-##[\h]ecni$'##Uy&$W(##Usas&*#]kSWf:##WXelkZU-'##Uy&$W(##Usas&*#gxc[x7##uqnzl%'##Uy&$W(##Usas&($W(%Ualyn\*###sZU7+#Uy&###qYU7'#[ijUWqnbbqz5###eke7+#Uy&###Uke7+#%)%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&$%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&###SZU7+%#%#'##Uy&$i''##Ty&$j'#UwSklQ@###aYU7+%#%#'##Uy&$i''##Ty&$j'#c|`$($j'#A(%#'##Ty&$j'%,'##Uy&$i'#a|`$#####oXU7+#qn}$###_XU7+#YqWklQ@###}WU7+'##Uy&$i'*'##Uy&$i'##YqWklQ@##c|`$#agzz%*'##Uy&$i'##YqWklQ@%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$i'##YqWklQ@%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$i'krg[x7#iwh|vm&##sfo[x7#S|r3*'##]9$i'krg[x7#iwh|vm&%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$i'##YqWklQ@##gxc[x7#WVltmors$*'##Uy&$h'##WRlo$'##Uy&$i'##YqWklQ@*'##Uy&$q$##c|`$'##Uy&$i'##YqWklQ@*#crgrRrU-##[\h]ecni$'##Uy&$i'##YqWklQ@*#]kSWf:##WXelkZU-'##Uy&$i'##YqWklQ@*#gxc[x7##uqnzl%'##Uy&$i'##YqWklQ@($i'_|UrqLS_Yz_\*###cZU7$#####_Y`B$#%###YsZ|%'#####_tY|%+#cbk+###wrZ|%'#####wf`7'#####Q}cy%+#muZ|%###of`7$#%###Y_b7+#krg[x7###Qe`7$#%###{d`7$#%###Ue`7'#Q0###me`7+'##Uy&$h'###]e`7+#me`7)'##Uy&$h'##WRlo$$'##Uy&$h'##WRlo$*'##Uy&$h'##WRlo$##c|`$#agzz%*'##Uy&$h'##WRlo$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$h'##WRlo$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$h'krg[x7#cbk,##sfo[x7#S|r3*'##]9$h'krg[x7#cbk,%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$h'##WRlo$##gxc[x7#WVltmors$*'##Uy&$q$##c|`$'##Uy&$h'##WRlo$*#crgrRrU-##[\h]ecni$'##Uy&$h'##WRlo$*#]kSWf:##WXelkZU-'##Uy&$h'##WRlo$*#gxc[x7##uqnzl%'##Uy&$h'##WRlo$($h'%kdmyn\*###}d`7$#%###{X`B+#WVR,###_dq6+#3###i_b7'#%###}anC$#####aeq6'#'###QbnC&#####iwnC+#wxk+###_znC+#S~Q,###oznC+#}sQ,###wde7+#_{RYQ`xR1###Sfe7'#_$###gf`7$#%###_f`7'#'###aqX7$#%###_bnC+#%###obnC+#####QcnC+#####acnC+#Q|q$###qcnC+#SRclYZ>###SdnC+#####cdnC+#####sdnC+#####UenC+#####eenC+#eZu]oQT(###uenC+#ic`gqL###WfnC+#####gfnC+#####wfnC+#####YgnC+#e|`$###ignC+#[ijUWqnbbqz5###ygnC+#Wgg$###[hnC+#W.###khnC+#####{hnC+#####]inC+#####minC+#####}inC+#sV[mdumbbqz5###_jnC+#%###ojnC+#qsr$###QknC+#Q|q$###aknC+#Q|q$###qknC+#cZu]oQT(###SlnC+#####clnC+#}zm%###slnC+#_lu`ojeryc&###UmnC+#m`lXmogwyc&###emnC+#soTi*###umnC+#WgSugQT(###WnnC+#[yX%###gnnC+#wTUaQoqT?###_nX7'#iO###WnX7'#W.###ygfC'#####kX`B+%#'##Uy&$q$#au5###q{~w%%#####a{~w%+#Q|q$###Q{~w%%#####]a~w%'#%###[`~w%'#Y.###y_~w%+#yohneogwyc&###q_~w%'#####i_~w%$#####{`~w%+#Q|q$###k`~w%'#%###g`~w%$#####c`~w%%#####yqX7$#####wnX7$#####grX7+#Q|q$###_rX7'#'###WrX7$#%###}qX7'#####uqX7%#%###eqX7+#UX\Wmogwyc&###UqX7)#ic`gqL###cqX7$#####yoX7'#Uy&###qoX7$#####aoX7+#WTqqVW5###QoX7+#c]YXssfwyc&###onX7'#S|$###spX7+#####kpX7$#%###cpX7'#q&###SpX7+#Whm\Y]s&###gnX7'#C###}mX7'#gc`gqL###wrX7'#kYa$###[X`B+%#'##Uy&$q$#c|`$)'##Uy&$q$##c|`$$'##Uy&$q$c|`$##*'##Uy&$q$##c|`$##c|`$#agzz%*'##Uy&$q$##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$q$##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$q$krg[x7#Ys*##sfo[x7#S|r3*'##]9$q$krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$q$##c|`$##gxc[x7#WVltmors$*#crgrRrU-##[\h]ecni$'##Uy&$q$##c|`$*#]kSWf:##WXelkZU-'##Uy&$q$##c|`$*#gxc[x7##uqnzl%'##Uy&$q$##c|`$($q$%e]nyn\*###[hfC+#Uy&###yee7$#%)%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$$%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$)##sfo[x7#S|r3$##sfo[x7#S|r3###igfC+%#%#'##q}A$#'##C$)#|)###odq6+#{tx%###mde7$###%#'##q}A$#'##C$)v&+#cza4#%#'##q}A$#'##C$)V&+$$#%#'##q}A$#'##C$)t%+%#%#'##q}A$#'##C$)#3#%#'##q}A$#'##C$)d%+#STb4#%#'##q}A$#'##C$)r$+###%#'##q}A$#'##C$)b$+###%#'##q}A$#'##C$)R$+###%#'##q}A$#'##C$)B+###%#'##q}A$#'##C$)2+#####WRdy%+$P###c~U|%+$P###Yycy%+#####wxcy%+#Wxcy%###gxcy%+#Wxcy%###a}cy%+#a}cy%###s~cy%+#klV|%###iycy%'$O($O%QbYy$###yycy%'#'###WjV|%$#%###Wxcy%+#Wxcy%###gRdy%+#kTdy%###kTdy%+#%###{Tdy%+#y}ey%###ikV|%+#3###YkV|%+#W.###S~U|%+#####a}U|%+#c$###ykV|%+#%###wjV|%+#_|U|%###q}U|%+#3###Q}U|%+#####o|U|%+#obX6###uiV|%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+###[lV|%+#Uy&###onV|%+$,###gjV|%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#S$###uwcy%+%#%#'##q}A$#%#'##3$$'##C$)#C#%#'##q}A$#'##C$)T%+%#%#'##q}A$#'##C$)#3($#Wf~eqLgc`gqL($)#Q|$(%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#q+ecy{WywR1a{RYQ`xR1(%#'##Uy&$#%#$$%#$%%#$''##'$)_ixxQmrs$}Zhtmors$(%#'##q}A$#'##C$)U[y{WywR1QsRYQ`xR1(%#'##Uy&$#'##'$)]ixxQmrs$Q[htmors$($$%iO($%#W.($&#syp%($*#syp%($+#ec`gqL($'#{ns(($(yh$QTv-($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&(%#'##Ty&$-%,%#'##C$)#Ur&#YofUWqnbbqz5##)%#'##q}A$#'##C$)Tsas&#Usas&$%#'##q}A$#'##C$)X'#3$%#'##q}A$#'##C$)f&#3#%#'##q}A$#'##C$)#+$$#%#'##q}A$#'##C$)3+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+#%#'##q}A$#'##C$)C+'#%'#%$$%#%#'##q}A$#%#'##3$$%#'##3$%%#$&'##C$)#S+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)S$+#)#%#'##q}A$#%#'##3$$%#'##3$%'##C$)c$+#YQa$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)s$+#+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)U%+#e%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)e%+#-#%#'##q}A$#%#'##3$$%#'##3$%'##C$)u%+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)W&+#C#%#'##q}A$#%#'##3$$%#'##3$%'##C$)g&+$,#%#'##q}A$#%#'##3$$%#'##3$%'##C$)w&+#/#%#'##q}A$#%#'##3$$%#'##3$%'##C$)Y'+#Uy&#%#'##q}A$#%#'##3$$%#'##3$%'##C$)i'+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)y'+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)[(+#;#%#'##q}A$#%#'##3$$%#'##3$%'##C$)k(+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$){(+#Q$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)])+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)m)+#U$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)})+%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#Q+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)_*+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)o*+##%%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)Q+#C<&c|`$_dq6&Qeq6aeq6&ieq6}WU7&QYU7aYU7&yYU7SZU7&eZU7sZU7&g\U7iuU7&quU7czU7&e{U7[~U7&_~U7YkX7&skX7}mX7&ynX7QoX7&soX7yoX7&mpX7spX7&{qX7}qX7&YrX7_rX7&QsX7UyX7&Uc]7{d`7&Se`7Ue`7&}e`7_f`7&if`7of`7&qf`7wf`7&Qg`7Y_b7&q_b7gde7&ode7wde7&Yee7yee7&{ee7Sfe7&[fe7Uke7&uke7c\f7&s\f7Y_f7&q_f7y_f7&Waf7qcf7&scf7Sdf7&Udf7cdf7&eef7uef7&eif7mif7&qof7[X`B&]Y`B_Y`B&aY`BigfC&ShfC[hfC&khfCmifC&ocjCqcjC&s]nC}anC&WbnC_bnC&wnnCiwnC&ywnC]ynC&mynC_znC&a{nCs|nC&u|nCkZoC&mZoCi_~w%&k_~w%q_~w%&i`~w%k`~w%&s`~w%{`~w%&ea~w%Qs~w%&as~w%uu~w%&_v~w%gv~w%&Yy~w%_z~w%&az~w%oz~w%&wz~w%Q{~w%&U{~w%a{~w%&u{~w%uwcy%&qycy%yycy%&Szcy%_zcy%&azcy%Q}cy%&q}cy%s~cy%&UQdy%WRdy%&iSdy%kTdy%&]Udy%o|U|%&s~U|%eQV|%&mQV|%uQV|%&WRV|%gRV|%&wRV|%m]V|%&}]V|%eiV|%&YjV|%gjV|%&klV|%onV|%&QoV|%{tV|%&muV|%}uV|%&QwV|%awV|%&cxV|%UyV|%&eyV|%m}V|%&}}V|%QQW|%&aQW|%cRW|%&sRW|%u[W|%&W\W|%_`W|%&o`W|%qaW|%&SbW|%UcW|%&ecW|%knW|%&mnW|%{nW|%&]oW|%msY|%&}sY|%_tY|%&otY|%wrZ|%&QsZ|%YsZ|%&asZ|%muZ|%&}uZ|%sd\|%)##wpY6#k^{h%)##s~U|%#Qe)b-#1'##Uy&$Z,#Uy&#'##Uy&$(#Ys*#'##Uy&$w+#oxsX(#'##Uy&$Y*#Uy&#'##Uy&$t(#Uy&#'##Uy&$Y(#c|`$#'##Uy&$X(#Uy&#'##Uy&$W(#Usas&&'##Uy&$i'#YqWklQ@#'##Uy&$h'#WRlo$#'##Uy&$q$#c|`$##crgrRrU-#[\h]ecni$$#]kSWf:#WXelkZU-&#gxc[x7#uqnzl%${zmzhpat$ioV]ZS``%]sqz)/'##Uy&$Z,#Uy&'##Uy&$(#Ys*'##Uy&$w+#oxsX('##Uy&$Y*#Uy&'##Uy&$t(#Uy&'##Uy&$Y(#c|`$'##Uy&$X(#Uy&%#%#'##Uy&$i''##Ty&$j'#UwSklQ@#Uy&'##Uy&$h'#WRlo$'##Uy&$q$#c|`$#c|`$#agzz%%#%#'##q}A$#'##Uy&$-#Tsas&%#%#'##p}A$#'##Ty&$-#eoc{T`xR1''##Uy&$Z*#Uy&'##Uy&$Z,#Uy&%#'##Uy&$Z,#Uy&#Uy&'##Uy&$[,#Uy&eUfiu:%#'##Uy&$(#Ys*#$[Q%")).

Definition HS1s_6 : acs := ltac:(acsb (AXB.acs_of "isb/C###grb/%#%#'##q}A$#'##C$)#X'#eyb$#wRdy%$V-$W-$X-#W^\6#s\\6#WTU7#cl|6#WTU7$Y-$Z-$[-$\-$]-#wr\/%#%#'##q}A$#%#'##3$$'##C$)#C################$^-$_-$`-$a-#V3($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&($[,%U^nyn\*($Z,%U^nyn\*###kde7$#####c\f7+#Y_f7$##{`f7#-###k`f7+#####qcf7$#%###[`f7+#####y_f7+#####i_f7'#-###Y_f7+#yaq6###oz~w%$#####qz~w%$#%###Qs~w%+#uu~w%$##iw~w%#o$###Yw~w%+#####_z~w%$#%###wv~w%+#####gv~w%+#####Wv~w%'#o$###uu~w%+#Uiz6###sz~w%%#####msY|%+%#'##Uy&$[,#u%#'##Uy&$[,w&+###'##Uy&$[,g&+#otk+#'##Uy&$[,Y'+###'##Uy&$[,W&+#gpk+#'##Uy&$[,u%+#aik+#'##Uy&$[,o%$#k(#'##Uy&$[,i'$###'##Uy&$[,q%%#####UyV|%+%#'##Uy&$Z,#Wz&#'##Uy&$Z,gz&+%#'##Uy&$Z,#Wz&#'##Uy&$Z,Wz&+%#'##Uy&$Z,#Wz&#'##Uy&$Z,Y{&'#eO#'##Uy&$Z,i{&+#a*#'##Uy&$[,e%$#5#'##Uy&$[,U%+%#'##Uy&$Z,#Wz&#'##Uy&$Z,wz&+%#'##Uy&$[,#U%#'##Uy&$Z,a{&'#####u[W|%+#7#'##Uy&$[,g:$###'##Uy&$[,c8$###'##Uy&$[,_6$###'##Uy&$[,[4$###'##Uy&$[,W2$###'##Uy&$[,S0$###'##Uy&$[,}-$###'##Uy&$[,y+$###'##Uy&$[,u)$###'##Uy&$[,q'$###'##Uy&$[,m%$###'##Uy&$[,}$$#a+#'##Uy&$[,Q%%#####m}V|%+%#'##Uy&$Z,#y{&#'##Uy&$Z,[|&+%#'##Uy&$Z,#y{&#'##Uy&$Z,y{&+%#'##Uy&$Z,#y{&#'##Uy&$Z,{|&'#'#'##Uy&$Z,]}&+#YN#'##Uy&$[,s$$#%#'##Uy&$[,c$+%#'##Uy&$Z,#y{&#'##Uy&$Z,k|&+%#'##Uy&$[,#c$#'##Uy&$Z,U}&'#####_`W|%+#'#'##Uy&$[,SP$###'##Uy&$[,{$$###'##Uy&$[,]$$#a+#'##Uy&$[,_$%#####QQW|%+%#'##Uy&$Z,#m}&#'##Uy&$Z,}}&+%#'##Uy&$Z,#m}&#'##Uy&$Z,m}&+%#'##Uy&$Z,#m}&#'##Uy&$Z,o~&'#'#'##Uy&$Z,QQ'+#_Y$#'##Uy&$[,S$$#%#'##Uy&$[,C+%#'##Uy&$Z,#m}&#'##Uy&$Z,_~&+%#'##Uy&$[,#C#'##Uy&$Z,w~&'#####qaW|%+#'#'##Uy&$[,y{$$###'##Uy&$[,[$$###'##Uy&$[,=$#a+#'##Uy&$[,?%#####cRW|%+%#'##Uy&$Z,#aQ'#'##Uy&$Z,qQ'+%#'##Uy&$Z,#aQ'#'##Uy&$Z,aQ'+%#'##Uy&$Z,#aQ'#'##Uy&$Z,cR''#'#'##Uy&$Z,sR'+#i^(#'##Uy&$[,3$#%#'##Uy&$[,#+%#'##Uy&$Z,#aQ'#'##Uy&$Z,SR'+'##Uy&$[,#'##Uy&$Z,kR''#####UcW|%+#'###euV|%'#%)'##]9$[,krg[x7#]9$'##]9$[,krg[x7#]9)'##Uy&$[,##Uy&$'##Uy&$[,5#+$'##Uy&$[,U$#)$'##Uy&$[,u$#)$'##Uy&$[,g%#)$'##Uy&$[,k'#)$'##Uy&$[,s'#S%$'##Uy&$[,w)#S%$'##Uy&$[,{+#S%$'##Uy&$[,Q.#S%$'##Uy&$[,U0#S%$'##Uy&$[,Y2#S%$'##Uy&$[,]4#S%$'##Uy&$[,a6#S%$'##Uy&$[,e8#S%$'##Uy&$[,i:#i8$'##Uy&$[,UP#uN$'##Uy&$[,{{$#Y|$*'##Uy&$[,##Uy&##c|`$#agzz%*'##Uy&$[,##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$[,##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$[,krg[x7#]9##sfo[x7#S|r3*'##]9$[,krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$[,##Uy&##gxc[x7#WVltmors$*'##Uy&$Z,##Ys*'##Uy&$[,##Uy&*'##Uy&$w+##oxsX('##Uy&$[,##Uy&*'##Uy&$Y*##Uy&'##Uy&$[,##Uy&*'##Uy&$t(##Uy&'##Uy&$[,##Uy&*'##Uy&$Y(##c|`$'##Uy&$[,##Uy&*'##Uy&$X(##Uy&'##Uy&$[,##Uy&*'##Uy&$W(##Usas&'##Uy&$[,##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$[,##Uy&*'##Uy&$h'##WRlo$'##Uy&$[,##Uy&*'##Uy&$q$##c|`$'##Uy&$[,##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$[,##Uy&*#]kSWf:##WXelkZU-'##Uy&$[,##Uy&*#gxc[x7##uqnzl%'##Uy&$[,##Uy&($[,%U^nyn\*###knW|%$#%###_vV|%+#['###}uV|%+%#'##Uy&$Z,#US'#'##Uy&$Z,uy&'#c'#'##Uy&$Z,Uy&+*#<3+###qwV|%+%#'##Uy&$Z,#Uy&###awV|%+%#'##Uy&$Z,#Uy&###SxV|%+%#'##Uy&$Z,#Ys*###ovV|%+##)'##]9$Z,wZh[x7#]9$'##]9$Z,wZh[x7#]9)'##Uy&$Z,Uy&#Uy&$'##Uy&$Z,ey&#3$'##Uy&$Z,}y&#+$'##Uy&$Z,US'#Uq&###QwV|%+#%*'##Uy&$Z,##Ys*##c|`$#agzz%*'##Uy&$Z,##Ys*%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z,##Ys*%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z,krg[x7#iO##sfo[x7#S|r3*'##]9$Z,krg[x7#iO%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z,##Ys*##gxc[x7#WVltmors$*'##Uy&$w+##oxsX('##Uy&$Z,##Ys**'##Uy&$Y*##Uy&'##Uy&$Z,##Ys**'##Uy&$t(##Uy&'##Uy&$Z,##Ys**'##Uy&$Y(##c|`$'##Uy&$Z,##Ys**'##Uy&$X(##Uy&'##Uy&$Z,##Ys**'##Uy&$W(##Usas&'##Uy&$Z,##Ys**'##Uy&$i'##YqWklQ@'##Uy&$Z,##Ys**'##Uy&$h'##WRlo$'##Uy&$Z,##Ys**'##Uy&$q$##c|`$'##Uy&$Z,##Ys**#crgrRrU-##[\h]ecni$'##Uy&$Z,##Ys**#]kSWf:##WXelkZU-'##Uy&$Z,##Ys**#gxc[x7##uqnzl%'##Uy&$Z,##Ys*($Z,%S^nyn\*###{nW|%+#[ijUWqnbbqz5###]uV|%'#%###{tV|%+*#<3+###mif7+###'##Uy&$Y([('###'##Uy&$Y(y''#'#'##Uy&$Y(c$+#####akf7+#%###wRdy%+'##Uy&$w+#'##Uy&$X(W&+'##Uy&$w+#'##Uy&$w+w&+#K)'##]9$w+krg[x7#}Ur@$'##]9$w+krg[x7#}Ur@)'##Uy&$w+##oxsX($'##Uy&$w+##w&$'##Uy&$w+Y'#gtsX(*'##Uy&$w+##oxsX(##c|`$#agzz%*'##Uy&$w+##oxsX(%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$w+##oxsX(%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$w+krg[x7#}Ur@##sfo[x7#S|r3*'##]9$w+krg[x7#}Ur@%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$w+##oxsX(##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$w+##oxsX(*'##Uy&$t(##Uy&'##Uy&$w+##oxsX(*'##Uy&$Y(##c|`$'##Uy&$w+##oxsX(*'##Uy&$X(##Uy&'##Uy&$w+##oxsX(*'##Uy&$W(##Usas&'##Uy&$w+##oxsX(*'##Uy&$i'##YqWklQ@'##Uy&$w+##oxsX(*'##Uy&$h'##WRlo$'##Uy&$w+##oxsX(*'##Uy&$q$##c|`$'##Uy&$w+##oxsX(*#crgrRrU-##[\h]ecni$'##Uy&$w+##oxsX(*#]kSWf:##WXelkZU-'##Uy&$w+##oxsX(*#gxc[x7##uqnzl%'##Uy&$w+##oxsX(($w+%_mkyn\*#'##Uy&$X(u%+#YSdy%#'##Uy&$X(C+%#%#'##q}A$#'##Uy&$-#Tsas&#'##Uy&$X(3+%#'##q}A$#'##Uy&$-#'##Uy&$X(e%+#]Qfy%#'##Uy&$X(U%+#Yuey%*'##Uy&$Z*##Uy&##c|`$#agzz%*'##Uy&$Z*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Z*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Z*krg[x7#]9##sfo[x7#S|r3*'##]9$Z*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Z*##Uy&##gxc[x7#WVltmors$*'##Uy&$Y*##Uy&'##Uy&$Z*##Uy&*'##Uy&$t(##Uy&'##Uy&$Z*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Z*##Uy&*'##Uy&$X(##Uy&'##Uy&$Z*##Uy&*'##Uy&$W(##Usas&'##Uy&$Z*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Z*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Z*##Uy&*'##Uy&$q$##c|`$'##Uy&$Z*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Z*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Z*##Uy&*#gxc[x7##uqnzl%'##Uy&$Z*##Uy&($Z*%U^nyn\*###s|nC$#%#'##Uy&$Y*c$+###'##Uy&$Y*S$+#wRdy%###iuU7$#####kuU7&#####]ynC+#%###YSdy%+'##Uy&$Y*)'##Uy&$Y*##Uy&$'##Uy&$Y*##S$$'##Uy&$Y*s$#aw&*'##Uy&$Y*##Uy&##c|`$#agzz%*'##Uy&$Y*##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y*##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y*krg[x7#]9##sfo[x7#S|r3*'##]9$Y*krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y*##Uy&##gxc[x7#WVltmors$*'##Uy&$t(##Uy&'##Uy&$Y*##Uy&*'##Uy&$Y(##c|`$'##Uy&$Y*##Uy&*'##Uy&$X(##Uy&'##Uy&$Y*##Uy&*'##Uy&$W(##Usas&'##Uy&$Y*##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$Y*##Uy&*'##Uy&$h'##WRlo$'##Uy&$Y*##Uy&*'##Uy&$q$##c|`$'##Uy&$Y*##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$Y*##Uy&*#]kSWf:##WXelkZU-'##Uy&$Y*##Uy&*#gxc[x7##uqnzl%'##Uy&$Y*##Uy&($Y*%U^nyn\*#'##Uy&$X(s$$###'##Uy&$X(c$+###'##Uy&$X(S$+#####_zcy%$#%###muZ|%+'##Uy&$Y(#'##Uy&$X(#+'##Uy&$Y(#'##Uy&$Y(m)+'##Uy&$X(#'##Uy&$Y(S($#%###_jf7+#%#'##Uy&$Y(s$+###'##Uy&$Y(C+#####Qkf7+#%###ojf7+#%#'##Uy&$t(#+'##Uy&$Y(###clf7+#%###Slf7+#Uy&###qkf7+'##Uy&$t()'##Uy&$t(##Uy&$'##Uy&$t(3#sx&*'##Uy&$t(##Uy&##c|`$#agzz%*'##Uy&$t(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$t(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$t(krg[x7#]9##sfo[x7#S|r3*'##]9$t(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$t(##Uy&##gxc[x7#WVltmors$*'##Uy&$Y(##c|`$'##Uy&$t(##Uy&*'##Uy&$X(##Uy&'##Uy&$t(##Uy&*'##Uy&$W(##Usas&'##Uy&$t(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$t(##Uy&*'##Uy&$h'##WRlo$'##Uy&$t(##Uy&*'##Uy&$q$##c|`$'##Uy&$t(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$t(##Uy&*#]kSWf:##WXelkZU-'##Uy&$t(##Uy&*#gxc[x7##uqnzl%'##Uy&$t(##Uy&($t(%U^nyn\*###Uef7+###'##Uy&$Y(#+#ue\6#'##Uy&$Y(e)%#iO#'##Uy&$Y(])'###'##Uy&$Y(S$'###'##Uy&$Y(3'###'##Uy&$Y(U%$###'##Uy&$Y({(+###'##Uy&$Y(k('###'##Uy&$Y(c('#####Wff7+%#'##Uy&$Y(#})###uef7+%#'##Uy&$Y(#c|`$)'##Uy&$Y(##c|`$$'##Uy&$Y(;#+$'##Uy&$Y([$#+$'##Uy&$Y(W%#s%$'##Uy&$Y(U(#)$'##Uy&$Y(s(#+$'##Uy&$Y(i)#'$'##Uy&$Y(})#eu`$*'##Uy&$Y(##c|`$##c|`$#agzz%*'##Uy&$Y(##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$Y(##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$Y(krg[x7#Ys*##sfo[x7#S|r3*'##]9$Y(krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$Y(##c|`$##gxc[x7#WVltmors$*'##Uy&$X(##Uy&'##Uy&$Y(##c|`$*'##Uy&$W(##Usas&'##Uy&$Y(##c|`$*'##Uy&$i'##YqWklQ@'##Uy&$Y(##c|`$*'##Uy&$h'##WRlo$'##Uy&$Y(##c|`$*'##Uy&$q$##c|`$'##Uy&$Y(##c|`$*#crgrRrU-##[\h]ecni$'##Uy&$Y(##c|`$*#]kSWf:##WXelkZU-'##Uy&$Y(##c|`$*#gxc[x7##uqnzl%'##Uy&$Y(##c|`$($Y(%e]nyn\*###[hf7'#####ygf7'#####igf7+#####Ygf7+#####sdf7+#gff7###Sdf7$#%###Qgf7'#####wff7'#####gff7+#####chf7'#####Shf7'#####cdf7+#khf7###Wnf7+#####umf7+#####emf7+#####Umf7+#####slf7+#####iof7'#####Yof7+#####wnf7+#####gnf7+#####Wjf7'#####}if7'#####]if7'#####{hf7+#[ijUWqnbbqz5###khf7+#yaa,)'##Uy&$X(##Uy&$'##Uy&$X(u$#1$'##Uy&$X(g&#mu&*'##Uy&$X(##Uy&##c|`$#agzz%*'##Uy&$X(##Uy&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$X(##Uy&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$X(krg[x7#]9##sfo[x7#S|r3*'##]9$X(krg[x7#]9%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$X(##Uy&##gxc[x7#WVltmors$*'##Uy&$W(##Usas&'##Uy&$X(##Uy&*'##Uy&$i'##YqWklQ@'##Uy&$X(##Uy&*'##Uy&$h'##WRlo$'##Uy&$X(##Uy&*'##Uy&$q$##c|`$'##Uy&$X(##Uy&*#crgrRrU-##[\h]ecni$'##Uy&$X(##Uy&*#]kSWf:##WXelkZU-'##Uy&$X(##Uy&*#gxc[x7##uqnzl%'##Uy&$X(##Uy&($X(%U^nyn\*###Q{nC+#wdy-###eQV|%'#%###m]V|%+#wdy-###gRV|%+#Qqc4###uQV|%+#WRV|%###kZoC$#####gde7$#%###ide7$#%###YkX7+#kTr^uUS(###mkX7%#S|$###ikX7%#C###qkX7$#%###]~U7$#####[~U7$#####U{U7+#]Uj8###szU7+#yrT{`%###czU7+#uqnzl%###U[U7+'##Uy&$W(###W\U7+#yrZ%###u[U7+#Usas&###e[U7+'##Uy&$W(*'##Uy&$W(##Usas&##c|`$#agzz%*'##Uy&$W(##Usas&%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$W(##Usas&%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$W(krg[x7#]Uj8##sfo[x7#S|r3*'##]9$W(krg[x7#]Uj8%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$W(##Usas&##gxc[x7#WVltmors$*'##Uy&$i'##YqWklQ@'##Uy&$W(##Usas&*'##Uy&$h'##WRlo$'##Uy&$W(##Usas&*'##Uy&$q$##c|`$'##Uy&$W(##Usas&*#crgrRrU-##[\h]ecni$'##Uy&$W(##Usas&*#]kSWf:##WXelkZU-'##Uy&$W(##Usas&*#gxc[x7##uqnzl%'##Uy&$W(##Usas&($W(%Ualyn\*###sZU7+#Uy&###qYU7'#[ijUWqnbbqz5###eke7+#Uy&###Uke7+#%)%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&$%#'##Uy&$i''##Ty&$j'UwSklQ@#Uy&###SZU7+%#%#'##Uy&$i''##Ty&$j'#UwSklQ@###aYU7+%#%#'##Uy&$i''##Ty&$j'#c|`$($j'#A(%#'##Ty&$j'%,'##Uy&$i'#a|`$#####oXU7+#qn}$###_XU7+#YqWklQ@###}WU7+'##Uy&$i'*'##Uy&$i'##YqWklQ@##c|`$#agzz%*'##Uy&$i'##YqWklQ@%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$i'##YqWklQ@%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$i'krg[x7#iwh|vm&##sfo[x7#S|r3*'##]9$i'krg[x7#iwh|vm&%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$i'##YqWklQ@##gxc[x7#WVltmors$*'##Uy&$h'##WRlo$'##Uy&$i'##YqWklQ@*'##Uy&$q$##c|`$'##Uy&$i'##YqWklQ@*#crgrRrU-##[\h]ecni$'##Uy&$i'##YqWklQ@*#]kSWf:##WXelkZU-'##Uy&$i'##YqWklQ@*#gxc[x7##uqnzl%'##Uy&$i'##YqWklQ@($i'_|UrqLS_Yz_\*###cZU7$#####_Y`B$#%###YsZ|%'#####_tY|%+#cbk+###wrZ|%'#####wf`7'#####Q}cy%+#muZ|%###of`7$#%###Y_b7+#krg[x7###Qe`7$#%###{d`7$#%###Ue`7'#Q0###me`7+'##Uy&$h'###]e`7+#me`7)'##Uy&$h'##WRlo$$'##Uy&$h'##WRlo$*'##Uy&$h'##WRlo$##c|`$#agzz%*'##Uy&$h'##WRlo$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$h'##WRlo$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$h'krg[x7#cbk,##sfo[x7#S|r3*'##]9$h'krg[x7#cbk,%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$h'##WRlo$##gxc[x7#WVltmors$*'##Uy&$q$##c|`$'##Uy&$h'##WRlo$*#crgrRrU-##[\h]ecni$'##Uy&$h'##WRlo$*#]kSWf:##WXelkZU-'##Uy&$h'##WRlo$*#gxc[x7##uqnzl%'##Uy&$h'##WRlo$($h'%kdmyn\*###}d`7$#%###{X`B+#WVR,###_dq6+#3###i_b7'#%###}anC$#####aeq6'#'###QbnC&#####iwnC+#wxk+###_znC+#S~Q,###oznC+#}sQ,###wde7+#_{RYQ`xR1###Sfe7'#_$###gf`7$#%###_f`7'#'###aqX7$#%###_bnC+#%###obnC+#####QcnC+#####acnC+#Q|q$###qcnC+#SRclYZ>###SdnC+#####cdnC+#####sdnC+#####UenC+#####eenC+#eZu]oQT(###uenC+#ic`gqL###WfnC+#####gfnC+#####wfnC+#####YgnC+#e|`$###ignC+#[ijUWqnbbqz5###ygnC+#Wgg$###[hnC+#W.###khnC+#####{hnC+#####]inC+#####minC+#####}inC+#sV[mdumbbqz5###_jnC+#%###ojnC+#qsr$###QknC+#Q|q$###aknC+#Q|q$###qknC+#cZu]oQT(###SlnC+#####clnC+#}zm%###slnC+#_lu`ojeryc&###UmnC+#m`lXmogwyc&###emnC+#soTi*###umnC+#WgSugQT(###WnnC+#[yX%###gnnC+#wTUaQoqT?###_nX7'#iO###WnX7'#W.###ygfC'#####kX`B+%#'##Uy&$q$#au5###q{~w%%#####a{~w%+#Q|q$###Q{~w%%#####]a~w%'#%###[`~w%'#Y.###y_~w%+#yohneogwyc&###q_~w%'#####i_~w%$#####{`~w%+#Q|q$###k`~w%'#%###g`~w%$#####c`~w%%#####yqX7$#####wnX7$#####grX7+#Q|q$###_rX7'#'###WrX7$#%###}qX7'#####uqX7%#%###eqX7+#UX\Wmogwyc&###UqX7)#ic`gqL###cqX7$#####yoX7'#Uy&###qoX7$#####aoX7+#WTqqVW5###QoX7+#c]YXssfwyc&###onX7'#S|$###spX7+#####kpX7$#%###cpX7'#q&###SpX7+#Whm\Y]s&###gnX7'#C###}mX7'#gc`gqL###wrX7'#kYa$###[X`B+%#'##Uy&$q$#c|`$)'##Uy&$q$##c|`$$'##Uy&$q$c|`$##*'##Uy&$q$##c|`$##c|`$#agzz%*'##Uy&$q$##c|`$%#'##q}A$#'##C$)Tsas&#qwTaQoqT?*'##Uy&$q$##c|`$%#'##q}A$#'##Uy&$-Tsas&#qwTaQoqT?*'##]9$q$krg[x7#Ys*##sfo[x7#S|r3*'##]9$q$krg[x7#Ys*%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$*'##Uy&$q$##c|`$##gxc[x7#WVltmors$*#crgrRrU-##[\h]ecni$'##Uy&$q$##c|`$*#]kSWf:##WXelkZU-'##Uy&$q$##c|`$*#gxc[x7##uqnzl%'##Uy&$q$##c|`$($q$%e]nyn\*###[hfC+#Uy&###yee7$#%)%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$$%#'##Uy&$#'##]9$-_n|sw7%#%#'##Ty&$#'##\9$-#_`S\nors$)##sfo[x7#S|r3$##sfo[x7#S|r3###igfC+%#%#'##q}A$#'##C$)#|)###odq6+#{tx%###mde7$###%#'##q}A$#'##C$)v&+#cza4#%#'##q}A$#'##C$)V&+$$#%#'##q}A$#'##C$)t%+%#%#'##q}A$#'##C$)#3#%#'##q}A$#'##C$)d%+#STb4#%#'##q}A$#'##C$)r$+###%#'##q}A$#'##C$)b$+###%#'##q}A$#'##C$)R$+###%#'##q}A$#'##C$)B+###%#'##q}A$#'##C$)2+#####WRdy%+$P###c~U|%+$P###Yycy%+#####wxcy%+#Wxcy%###gxcy%+#Wxcy%###a}cy%+#a}cy%###s~cy%+#klV|%###iycy%'$O($O%QbYy$###yycy%'#'###WjV|%$#%###Wxcy%+#Wxcy%###gRdy%+#kTdy%###kTdy%+#%###{Tdy%+#y}ey%###ikV|%+#3###YkV|%+#W.###S~U|%+#####a}U|%+#c$###ykV|%+#%###wjV|%+#_|U|%###q}U|%+#3###Q}U|%+#####o|U|%+#obX6###uiV|%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+###[lV|%+#Uy&###onV|%+$,###gjV|%+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#S$###uwcy%+%#%#'##q}A$#%#'##3$$'##C$)#C#%#'##q}A$#'##C$)T%+%#%#'##q}A$#'##C$)#3($#Wf~eqLgc`gqL($)#Q|$(%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#q+ecy{WywR1a{RYQ`xR1(%#'##Uy&$#%#$$%#$%%#$''##'$)_ixxQmrs$}Zhtmors$(%#'##q}A$#'##C$)U[y{WywR1QsRYQ`xR1(%#'##Uy&$#'##'$)]ixxQmrs$Q[htmors$($$%iO($%#W.($&#syp%($*#syp%($+#ec`gqL($'#{ns(($(yh$QTv-($-#3(%#%#'##C$)'##Ty&$-#Ur&#Sy&(%#'##Ty&$-%,%#'##C$)#Ur&#YofUWqnbbqz5##)%#'##q}A$#'##C$)Tsas&#Usas&$%#'##q}A$#'##C$)X'#3$%#'##q}A$#'##C$)f&#3#%#'##q}A$#'##C$)#+$$#%#'##q}A$#'##C$)3+%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)#Q+#%#'##q}A$#'##C$)C+'#%'#%$$%#%#'##q}A$#%#'##3$$%#'##3$%%#$&'##C$)#S+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)S$+#)#%#'##q}A$#%#'##3$$%#'##3$%'##C$)c$+#YQa$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)s$+#+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)U%+#e%#%#'##q}A$#%#'##3$$%#'##3$%'##C$)e%+#-#%#'##q}A$#%#'##3$$%#'##3$%'##C$)u%+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)W&+#C#%#'##q}A$#%#'##3$$%#'##3$%'##C$)g&+$,#%#'##q}A$#%#'##3$$%#'##3$%'##C$)w&+#/#%#'##q}A$#%#'##3$$%#'##3$%'##C$)Y'+#Uy&#%#'##q}A$#%#'##3$$%#'##3$%'##C$)i'+#9#%#'##q}A$#%#'##3$$%#'##3$%'##C$)y'+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)[(+#;#%#'##q}A$#%#'##3$$%#'##3$%'##C$)k(+$+#%#'##q}A$#%#'##3$$%#'##3$%'##C$){(+#Q$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)])+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)m)+#U$#%#'##q}A$#%#'##3$$%#'##3$%'##C$)})+%#%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)#Q+#%#'##q}A$#%#'##3$$%#'##3$%'##C$)_*+###%#'##q}A$#%#'##3$$%#'##3$%'##C$)o*+##%%#'##q}A$#%#'##3$$%#'##3$%%#'##3$''##C$)Q+#C<&c|`$_dq6&Qeq6aeq6&ieq6}WU7&QYU7aYU7&yYU7SZU7&eZU7sZU7&g\U7iuU7&quU7czU7&e{U7[~U7&_~U7YkX7&skX7}mX7&ynX7QoX7&soX7yoX7&mpX7spX7&{qX7}qX7&YrX7_rX7&QsX7UyX7&Uc]7{d`7&Se`7Ue`7&}e`7_f`7&if`7of`7&qf`7wf`7&Qg`7Y_b7&q_b7gde7&ode7wde7&Yee7yee7&{ee7Sfe7&[fe7Uke7&uke7c\f7&s\f7Y_f7&q_f7y_f7&Waf7qcf7&scf7Sdf7&Udf7cdf7&eef7uef7&eif7mif7&qof7[X`B&]Y`B_Y`B&aY`BigfC&ShfC[hfC&khfCmifC&ocjCqcjC&s]nC}anC&WbnC_bnC&wnnCiwnC&ywnC]ynC&mynC_znC&a{nCs|nC&u|nCkZoC&mZoCi_~w%&k_~w%q_~w%&i`~w%k`~w%&s`~w%{`~w%&ea~w%Qs~w%&as~w%uu~w%&_v~w%gv~w%&Yy~w%_z~w%&az~w%oz~w%&wz~w%Q{~w%&U{~w%a{~w%&u{~w%uwcy%&qycy%yycy%&Szcy%_zcy%&azcy%Q}cy%&q}cy%s~cy%&UQdy%WRdy%&iSdy%kTdy%&]Udy%o|U|%&s~U|%eQV|%&mQV|%uQV|%&WRV|%gRV|%&wRV|%m]V|%&}]V|%eiV|%&YjV|%gjV|%&klV|%onV|%&QoV|%{tV|%&muV|%}uV|%&cxV|%UyV|%&eyV|%m}V|%&}}V|%QQW|%&aQW|%cRW|%&sRW|%u[W|%&W\W|%_`W|%&o`W|%qaW|%&SbW|%UcW|%&ecW|%knW|%&mnW|%{nW|%&]oW|%msY|%&}sY|%_tY|%&otY|%wrZ|%&QsZ|%YsZ|%&asZ|%muZ|%&}uZ|%sd\|%)##wpY6#k^{h%)##s~U|%#Qe)b-#1'##Uy&$[,#Uy&#'##Uy&$Z,#Ys*#'##Uy&$w+#oxsX(#'##Uy&$Y*#Uy&#'##Uy&$t(#Uy&#'##Uy&$Y(#c|`$#'##Uy&$X(#Uy&#'##Uy&$W(#Usas&&'##Uy&$i'#YqWklQ@#'##Uy&$h'#WRlo$#'##Uy&$q$#c|`$##crgrRrU-#[\h]ecni$$#]kSWf:#WXelkZU-&#gxc[x7#uqnzl%${zmzhpat$ioV]ZS``%Yymz)/'##Uy&$[,#Uy&%#'##Uy&$Z,#Uy&#Uy&'##Uy&$w+#oxsX('##Uy&$Y*#Uy&'##Uy&$t(#Uy&'##Uy&$Y(#c|`$'##Uy&$X(#Uy&%#%#'##Uy&$i''##Ty&$j'#UwSklQ@#Uy&'##Uy&$h'#WRlo$'##Uy&$q$#c|`$#c|`$#agzz%%#%#'##q}A$#'##Uy&$-#Tsas&%#%#'##p}A$#'##Ty&$-#eoc{T`xR1''##Uy&$Z*#Uy&'##Uy&$Z,#Uy&%#'##Uy&$Z,#Uy&#Uy&'##Uy&$[,#Uy&Usaiu:'##Uy&$(#$[Q%")).

Definition HS1s (h : nat) : option acs :=
match h with | 0%nat => Some HS1s_0 | 6%nat => Some HS1s_6 | _ => None end.
End Mqa.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition jo6_stage2_r0_1 : plan :=
PRun [0x4c5d4]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x915f8]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 1 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition jo6_stage2_r1_2 : plan :=
PRun [0x4c5d4]
(PJoin e_sp0 (-2280) 8
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x6487c]
(PDiamond 0x64aa8 []%nat
(PBump 2252
(PRun []
(PX XMemset []
(PRun [0x915f8]
(PHavoc [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 2 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition jo6_stage2 : plan :=
PBump 478
(PSplit (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 3935) 4030
(jo6_stage2_r0_1)
(jo6_stage2_r1_2)).

Definition jo6_stage2_ranges : list (Z * nat) := [(0x3d000, 1018%nat); (0x4bfe8, 4096%nat); (0x63fe8, 2048%nat); (0x68fe8, 1024%nat); (0x6afe8, 1024%nat); (0x6cfe8, 1024%nat); (0x6efe8, 3072%nat); (0x73fe8, 4096%nat); (0x7cfe8, 1024%nat); (0x80fe8, 4096%nat); (0x90fe8, 2048%nat); (0xcafe8, 1024%nat); (0xdafdc, 1024%nat); (0xdcfdc, 1024%nat)]%Z.
