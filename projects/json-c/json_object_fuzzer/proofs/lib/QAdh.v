(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QOJv.Mq8.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Ltac Q0z1.sf_hide_poison ::= sf_hide_poison_divlit. Local Ltac mkr__sf_hide_poison_1 := sf_hide_poison_divlit.

Ltac pk_key3 A X0 :=
match constr:(tt) with
| _ => Q0z1.pk_lit X0
| _ => lazymatch A with (bv_unsigned _ + _)%Z => X0 end
end.
Local Ltac Q0z1.pk_sep_get A sA A2 X0 ::=
tryif (let X := pk_key3 A X0 in idtac) then (
let X := pk_key3 A X0 in
first [ match goal with _ : Q0z1.pk_sep A sA A2 X |- _ => idtac end
| match goal with _ : Q0z1.pk_nosep A sA A2 X |- _ => idtac end
| match goal with _ : Q0z1.pk_seen A sA |- _ => idtac end;
first [ let HS := fresh "__pks" in assert (HS : Q0z1.pk_sep A sA A2 X)
by (unfold Q0z1.pk_sep; Q0z1.transport_lia)
| let HS := fresh "__pkn" in pose proof (I : Q0z1.pk_nosep A sA A2 X) as HS ]
| idtac ]) else idtac. Local Ltac mkr__pk_sep_get_2 A sA A2 X0 := tryif (let X := pk_key3 A X0 in idtac) then (
let X := pk_key3 A X0 in
first [ match goal with _ : Q0z1.pk_sep A sA A2 X |- _ => idtac end
| match goal with _ : Q0z1.pk_nosep A sA A2 X |- _ => idtac end
| match goal with _ : Q0z1.pk_seen A sA |- _ => idtac end;
first [ let HS := fresh "__pks" in assert (HS : Q0z1.pk_sep A sA A2 X)
by (unfold Q0z1.pk_sep; Q0z1.transport_lia)
| let HS := fresh "__pkn" in pose proof (I : Q0z1.pk_nosep A sA A2 X) as HS ]
| idtac ]) else idtac.
Local Ltac Q0z1.pk_side A sA kn n ::=
first [ lazymatch goal with
| |- (?A2 + ?X0 <= A + Z.of_nat kn \/ A + Z.of_nat kn + n <= ?A2)%Z =>
let X := pk_key3 A X0 in
match goal with HS : Q0z1.pk_sep A sA A2 X |- _ =>
exact (Q0z1.pk_sep_sub A sA A2 X (Z.of_nat kn) n HS eq_refl eq_refl) end
end
| Q0z1.simpl_sizes_goal; Q0z1.transport_lia ]. Local Ltac mkr__pk_side_3 A sA kn n := first [ lazymatch goal with
| |- (?A2 + ?X0 <= A + Z.of_nat kn \/ A + Z.of_nat kn + n <= ?A2)%Z =>
let X := pk_key3 A X0 in
match goal with HS : Q0z1.pk_sep A sA A2 X |- _ =>
exact (Q0z1.pk_sep_sub A sA A2 X (Z.of_nat kn) n HS eq_refl eq_refl) end
end
| Q0z1.simpl_sizes_goal; Q0z1.transport_lia ].

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition getfrom_entry : Z := 0x4431c.
Definition GETFROM_STACK : Z := 640.

Section Loops.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma copy_loop : forall cnt (i : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (k nf0 dst src : Z) (SRC CHW : list word) (Q : machine_state -> Prop),
Z.of_nat cnt = k - i -> 0 <= i < k -> 0 <= nf0 -> nf0 + k <= Z.of_nat (length SRC) -> k <= Z.of_nat (length CHW) ->
0 <= dst -> dst + 4 * Z.of_nat (length CHW) <= src \/ src + 4 * Z.of_nat (length SRC) <= dst -> src + 4 * Z.of_nat (length SRC) <= band_lo ->
dst + 4 * Z.of_nat (length CHW) <= band_lo ->
mem_inv asegs m ->
u32arr asegs m src SRC -> u32arr asegs m dst CHW ->
(forall j, (j < Z.to_nat i)%nat -> nth_error CHW j = nth_error SRC (Z.to_nat nf0 + j)%nat) ->
(forall m' CHW' (a2' : word), mem_inv asegs m' -> munch [(dst, dst + 4 * k)] m m' -> wmono asegs m m' ->
u32arr asegs m' dst CHW' -> length CHW' = length CHW ->
(forall j, (j < Z.to_nat k)%nat -> nth_error CHW' j = nth_error SRC (Z.to_nat nf0 + j)%nat) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (dst + 4 * k)) a2' (wz (dst + 4 * k)) a4 a5 a6 a7
s2 s3 (wz (src + 4 * nf0 + 4 * k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x444a4) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (dst + 4 * k)) a2 (wz (dst + 4 * i)) a4 a5 a6 a7
s2 s3 (wz (src + 4 * nf0 + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x44490) fc None m (seg_rom asegs)).
Proof.
induction cnt as [|cnt IH]; intros until Q; intros HK Hi Hnf HS HKC DLO DISJ SHI DHI MI ASRC ADST PREV CONT; [lia|].
pose proof (munch_refl [(dst, dst + 4 * k)] m) as MU. pose proof (wmono_refl asegs m) as WM.

destruct (nth_error SRC (Z.to_nat (nf0 + i))) as [w|] eqn:EW.
2:{ exfalso. apply nth_error_None in EW. lia. }
pose proof (u32arr_read asegs m src SRC (nf0 + i) w (wa (src + 4 * nf0 + 4 * i)) ASRC EW ltac:(lia) ltac:(f_equal; lia)) as HR.
pose proof (u32arr_store_ok asegs m dst CHW i (wa (dst + 4 * i)) ADST ltac:(lia) eq_refl) as HS0.
step.
step.
rewrite le4_sx32'.
pose proof (u32arr_write asegs m dst CHW i w ADST ltac:(lia)) as ADST'. clear ADST HR. store_done. rename ADST' into ADST.
step. step.
replace (dst + 4 * i + 4) with (dst + 4 * (i + 1)) by lia.
replace (src + 4 * nf0 + 4 * i + 4) with (src + 4 * nf0 + 4 * (i + 1)) by lia.
assert (PREV' : forall j, (j < Z.to_nat (i + 1))%nat -> nth_error (upd CHW (Z.to_nat i) w) j = nth_error SRC (Z.to_nat nf0 + j)%nat).
{ intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE].
- rewrite nth_error_upd_same by lia. rewrite <- EW. f_equal. lia.
- rewrite nth_error_upd_other by lia. apply PREV. lia. }
step.
destruct (Z.eq_dec (i + 1) k) as [EQ|NE].
- rewrite EQ. unfold_cond. rewrite Z.eqb_refl. cbn [negb].
rewrite EQ in PREV'. apply (CONT _ _ _ MI MU WM ADST); [apply upd_length| exact PREV'].
- ifz. eapply (IH (i + 1)) with (SRC := SRC) (CHW := upd CHW (Z.to_nat i) w) (nf0 := nf0);
rewrite ?upd_length; try assumption; try lia.
intros m' CHW' a2' MI' MU' WM' AD' LEN' PR'. apply (CONT m' CHW' a2' MI'); [| | exact AD'| rewrite LEN', ?upd_length; reflexivity| exact PR'].
+ eapply munch_trans; [exact MU| exact MU'].
+ eapply wmono_trans; [exact WM| exact WM'].
Qed.

Lemma getfrom_unlock : forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra : word)
(sp : word) (F : bvmap 5 word) fc (m : word -> option byte) (lo RIc res : Z) (rest : list cell) (fj : list byte) (Q : machine_state -> Prop),
rw_cells asegs m RIc (C8 (wz MUTEX_HELD) :: rest) -> amo_aligned AD (wz RIc) = true -> 0 <= res < 2 -> RIc + 8 <= lo ->
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 128 ->
rw_cells asegs m (bv_unsigned sp + -128) [CB 24 fj; C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
(forall m' (u0 u1 u2 u3 w1 w2 w3 w4 w5 w6 w7 : word),
mem_inv asegs m' -> munch [(bv_unsigned sp + -128, bv_unsigned sp); (RIc, RIc + 8)] m m' -> wmono asegs m m' ->
rw_cells asegs m' RIc (C8 (wz 0) :: rest) -> stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR vra sp gp tp u0 u1 u2 v0 v1 (wz res) w1 w2 w3 w4 w5 w6 w7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 u3 t4 t5 t6)
F (ret_pc vra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz RIc) (wz res) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz 2305843009213693952) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x444b4) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros HD AMO Hres RIL MI ST CEIL LO FR CONT. idtac. unfold MUTEX_HELD in *.
pose proof (bv_unsigned_in_range 64 sp) as SP. unfold bv_modulus in SP. change (2 ^ Z.of_N 64) with (2^64) in SP.
pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (RIc, RIc + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ HD) as RB. cbn [cells_size csize] in RB.
step.
do 7 step.
step.
do 5 step.
step.
stp. stp. step. if_lit.
stp. step. if_lit.
stp. stp. stp. stp. stp. stp. stp.
step. if_lit.
amo_step AMO.
step. if_lit.
amo_step AMO. fix_lit_store.
step. if_lit.
step. if_lit.
step. if_lit.
step.
do 13 step. step. step.
release_frame FR ST (bv_unsigned sp).
eapply CONT; [exact MI| exact MU| exact WM| exact HD| exact ST].
Qed.
End Loops.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition gfa_W (sp c au : Z) : list (Z * Z) :=
[ (sp - GETFROM_STACK, sp); (pc_addr X c, pc_addr X c + 80); (rl_T X + 2768, rl_T X + 3168);
(ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition gfa_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c k lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (gfa_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ gstep RE X a (snd r) G G1
/\ a0 = wz (if fst r then 1 else 0)
/\ if fst r then
rw_cells asegs m' (pc_addr X c) [C4 (wz 0)]
/\ forall m'', munch [(pc_addr X c, pc_addr X c + 4)] m' m'' -> wmono asegs m' m'' ->
rw_cells asegs m'' (pc_addr X c) [C4 (wz k)] -> RPrim (upd_cls c (set_count k) (snd r)) G1 RE X m''
else RPrim (snd r) G1 RE X m'.

Lemma getfrom_tail : forall ra gp t0 t1 t2 a0 a1 a2 a6 a7 s1 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 vra : word)
(sp : word) (F : bvmap 5 word) fc (m0 mP m : word -> option byte) (s : PStateA) (a aX : AState) (G GX : ghost) (K : Z -> pcls)
(c k lo RIc : Z) j1 j2 j3 j4 CH fj,
let x := cls aX c in let nf := c_num_freed x in let pcA := pc_addr X c in let fb := fa_beg (ae_L RE) c in
rlay_ok RE X -> 1 <= c <= 30 -> 1 <= k <= 8 -> k <= nf -> k <= max_count c -> c_count x = 0 -> as_cache_inited aX = true ->
RIc = ri_addr RE c -> band_lo <= lo -> lo <= bv_unsigned sp - GETFROM_STACK ->
c_alloc_user (cls a c) <= c_alloc_user x -> gstep RE X a aX G GX ->

RTconst RE X m -> RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) ->
munch (gfa_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m0 m -> wmono asegs m0 m ->
munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp); (RIc, RIc + 128); (pcA, pcA + 80)] mP m -> wmono asegs mP m ->
rw_cells asegs m (bv_unsigned sp + -128) [CB 24 fj; C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
rw_cells asegs m RIc
[C8 (wz MUTEX_HELD); CB 8 j1; C8 (wz (nf - k)); C8 (wz (c_mapped_fa x)); C8 (wz (c_alloc_user x)); C8 (wz 0); C8 (wz (c_mapped_user x));
C8 (wz 0); CB 4 j2; C1 (b8 0); CB 3 j3; CB 56 j4] ->
rw_cells asegs m pcA [C4 (wz 0); C4 (wz (bmax c)); C8 (wz (bsize c))] ->
u32arr asegs m (pcA + 16) CH -> length CH = 16%nat ->
u32arr asegs m fb (map (fun i => wz (coff c i)) (pk_fl (K c))) ->

hjunk mP (rl_T X + 2768) (rl_T X + 2800) ->
(forall c0, GX c0 <> [] -> 1 <= c0 < kNumClasses) ->
(forall c0, 0 <= c0 < kNumClasses -> c0 <> c -> class_rep aX GX RE X mP c0 (K c0)) ->
cr_pure aX GX c (K c) ->
hjunk mP (fb + 4 * nf) (fb + c_mapped_fa x) -> cr_user aX GX RE mP c -> hjunk mP (SH fb) (SH fb + 67108864) ->
evt asegs (gfa_post vra sp gp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 F fc s a G c k lo m0
(true, set_cls c (set_num_freed (nf - k) x) aX) s)
(MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz RIc) s1 a0 a1 a2 (wz (pcA + 16)) (wz k) (wz (nf - k)) a6 a7
s2 (wz 2305843009213693952) (wz fb) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x44480) fc None m (seg_rom asegs)).
Proof.
intros until fj; intros x nf pcA fb RL Hc HK Hkn Hkm CNT EI ERIc CEIL LO AUle GS RT RS MI ST MU WM MUP WMP FR RI PC0 ACH LCH FA
HJS GNE HCall PU FJ HU FS. unfold ri_addr in ERIc.
pose proof (bv_unsigned_in_range 64 sp) as SP. unfold bv_modulus in SP. change (2 ^ Z.of_N 64) with (2^64) in SP.
pose proof CEIL as CEIL'. idtac. unfold GETFROM_STACK in LO, MUP.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. hide TA.
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _).
assert (LFL : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K c)))) = nf) by (rewrite length_map; exact P1).
assert (AMO : amo_aligned AD (wz RIc) = true).
{ apply amo_aligned_intro8; [rewrite ERIc; lia|]. rewrite ERIc. rewrite RIq. unhide PAL.
replace (prim_lo RE + 137438953472 + 128 * c) with (8 * (prim_lo RE / 8 + 17179869184 + 16 * c)) by (Z.div_mod_to_equations; lia).
rewrite Z.mul_comm. apply Z_mod_mult. }
assert (RIB : 17594333495296 <= RIc /\ RIc + 128 <= band_lo) by (rewrite ERIc; rewrite RIq; lia).
subst x nf pcA fb. unfold pc_addr in *. rewrite KS in P13.
pose proof (munch_refl [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)] m) as MUt.
pose proof (wmono_refl asegs m) as WMt.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| rewrite ERIc, RIq; lia| rewrite ERIc, RIq, PH; lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
assert (FWst : Forall st_avoid [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)]).
{ repeat (constructor; [st_avoid_solve|]). constructor. }
assert (FWc : Forall (wc_ok RE X c) [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)]).
{ constructor; [cbn; left; lia|]. constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; unfold ri_addr; rewrite <- ERIc; exact Hz|].
constructor; [| constructor]. cbn -[fp_cls]; do 2 right; intros z Hz; right; left; unfold pc_addr; exact Hz. }
unfold gfa_W, GETFROM_STACK, pc_addr, ri_addr in MU. rewrite <- ERIc, ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
step. step. step. step.
rewrite (unsigned_lit (c_num_freed (cls aX c) - k)), (unsigned_lit k) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
set (dst := rl_T X + 208 + 80 * c + 16) in *. set (nf := c_num_freed (cls aX c)) in *.
replace (wz dst) with (wz (dst + 4 * 0)) by (f_equal; lia).
replace (wz (fa_beg (ae_L RE) c + (nf - k) * 4)) with (wz (fa_beg (ae_L RE) c + 4 * (nf - k) + 4 * 0)) by (f_equal; lia).
replace (dst + k * 4) with (dst + 4 * k) by lia.
eapply (copy_loop (Z.to_nat k) 0) with (nf0 := nf - k) (SRC := map (fun i : Z => wz (coff c i)) (pk_fl (K c))) (CHW := CH);
[lia| lia| lia| rewrite LFL; lia| rewrite LCH; lia| subst dst; lia| | rewrite LFL, FB; lia| rewrite LCH; subst dst; lia| exact MI| exact FA| exact ACH| intros j Hj; lia|].
{ rewrite LCH, LFL, FB. subst dst. destruct TD as [TD1|TD2]; [left; lia| right; lia]. }
intros m1 CH1 a2' MI1 MU1 WM1 ACH1 LCH1 PR1.
hide MU. hide MUP. hide MUt. transport_after_call asegs m m1 MU1 WM1. unhide MU. unhide MUP. unhide MUt.
assert (MU' : munch _ m0 m1) by (eapply munch_chain; [exact MU| exact MU1| subst dst; sub_fp_solve]).
assert (MUP' : munch _ mP m1) by (eapply munch_chain; [exact MUP| exact MU1| subst dst; sub_fp_solve]).
assert (MUt' : munch _ m m1) by (eapply munch_chain; [exact MUt| exact MU1| subst dst; sub_fp_solve]).
clear MU MUP MUt MU1 MI; try clear ACH; rename MU' into MU; rename MUP' into MUP; rename MUt' into MUt; rename MI1 into MI.
step. step. step.
stp.

eapply getfrom_unlock with (lo := lo); [exact RI| exact AMO| lia| lia| exact MI| exact ST| exact CEIL'| lia| exact FR|].
intros m3 u0 u1 u2 u3 w1 w2 w3 w4 w5 w6 w7 MI3 MU3 WM3 HD3 ST3. clear RI ST.
apply (proj1 (rw_cells_app asegs _ _ [C4 (wz 0)] _)) in PC0 as [PCh PCt]. cbn [cells_size csize Nat.add] in PCt.
hide MU. hide MUP. hide MUt. transport_after_call asegs m2 m3 MU3 WM3. unhide MU. unhide MUP. unhide MUt.
assert (MU' : munch _ m0 m3) by (eapply munch_chain; [exact MU| exact MU3| sub_fp_solve]).
assert (MUP' : munch _ mP m3) by (eapply munch_chain; [exact MUP| exact MU3| sub_fp_solve]).
assert (MUt' : munch _ m m3) by (eapply munch_chain; [exact MUt| exact MU3| sub_fp_solve]).
clear MU MUP MUt MU3 MI; rename MU' into MU; rename MUP' into MUP; rename MUt' into MUt; rename MI3 into MI.

pose proof PU as (_ & _ & P3 & _ & P5 & _).
assert (NNF : Forall (fun i => 0 <= i) (pk_fl (K c))).
{ apply Forall_forall. intros i Hi. exact (proj1 (tag_at_Some_lt _ _ _ _ (P5 i Hi))). }
assert (NN : Forall (fun i => 0 <= i) (skipn (Z.to_nat (nf - k)) (pk_fl (K c)))).
{ apply Forall_forall. intros i Hi. exact (proj1 (List.Forall_forall _ _) NNF i (In_skipn_In _ _ _ Hi)). }
assert (OLD : forall j, In j (skipn (Z.to_nat (nf - k)) (pk_fl (K c))) -> tag_at GX c j = Some TFree).
{ intros j Hj. apply P5. exact (In_skipn_In _ _ _ Hj). }

apply evt_done.
unfold gfa_post. do 16 eexists. exists (retag_list c (skipn (Z.to_nat (nf - k)) (pk_fl (K c))) TCached GX).
split; [reflexivity|]. split; [reflexivity|].
split. { unfold gfa_W, GETFROM_STACK, pc_addr, ri_addr. rewrite <- ERIc, ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
split; [eapply RTconst_munch; [exact RT| exact MUt| exact WMt| exact FWrt]|].
split; [eapply RStats_munch; [exact RS| exact MUt| exact WMt| exact FWst]|].
split. { cbn [snd]. eapply gstep_trans; [exact GS|]. eapply gstep_trans.
- apply (gstep_ext RE X aX (set_cls c (set_num_freed (nf - k) (cls aX c)) aX) GX); [intros c0| intros c0| reflexivity| reflexivity];
(destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]).
- apply gstep_retag_cached; [exact NN| exact OLD]. }
split; [reflexivity|]. cbn [fst snd].
split; [exact PCh|].
intros m4 MU4 WM4 PCk. unfold pc_addr in MU4, PCk.
hide MU. hide MUP. hide MUt. transport_after_call asegs m3 m4 MU4 WM4. unhide MU. unhide MUP. unhide MUt.
assert (MUP' : munch _ mP m4) by (eapply munch_chain; [exact MUP| exact MU4| sub_fp_solve]). clear MUP; rename MUP' into MUP.
apply ri_stat_recast in HD3.
assert (PC4 : rw_cells asegs m4 (rl_T X + 208 + 80 * c) [C4 (wz k); C4 (wz (bmax c)); C8 (wz (bsize c))]).
{ apply (proj2 (rw_cells_app asegs _ _ [C4 (wz k)] _)). cbn [cells_size csize Nat.add]. split; [exact PCk| exact PCt]. }
assert (SRB : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ unhide PAL. rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
eapply (gfa_close aX _ GX RE X mP m4 c k K j1 j2 j3 _ CH1 RL Hc ltac:(lia) Hkm CNT EI);
[ unfold upd_cls; rewrite !cls_set_cls_eq; reflexivity
| intros c0 NE; unfold upd_cls; rewrite !cls_set_cls_ne by exact NE; reflexivity
| exact EI
| exact HJS | exact GNE | exact HCall | exact PU
| exact WMP
| eapply agree_other_classes; [exact RL| lia| exact MUP| exact WMP| exact FWc]
| eapply agree_on_of_munch; [exact MUP| exact WMP|]; intros z Uz Hz; apply (uzone_bounds RE X c z RL ltac:(lia)) in Uz; cbn [outside];
clear - Uz Hz SRB RB RIB ERIc RIq PK PCH PH TK TB TD CEIL LO Hc; lia
| unfold ri_addr; rewrite <- ERIc; exact HD3
| exact PC4 | exact ACH1 | rewrite LCH1; exact LCH | exact PR1 | exact FA | exact FJ | exact HU | exact FS ].
Qed.

Ltac exact_gfaW MU ERIc QA SFB :=
unfold gfa_W, GETFROM_STACK, pc_addr, ri_addr; rewrite <- ?ERIc, ?(proj1 (proj2 (proj2 kconsts))), ?(proj1 (proj2 kconsts));
change (536870912 / 8) with 67108864; change (3758096384 / 8) with 469762048; rewrite ?QA, ?SH_plus8, ?SFB; exact MU.

Lemma getfrom_spec : forall ra sp gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c k lo : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - GETFROM_STACK ->
1 <= c <= 30 -> k = max_count c / 2 -> c_count (cls a c) = 0 -> as_cache_inited a = true ->
aimplT atn (get_from_allocator (ae_L RE) a c k) s
(gfa_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c k lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 2768)) (wz c) (wz (pc_addr X c + 16)) (wz k) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz getfrom_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RT RL RS RP MI ST CEIL LO Hc Hk CNT0 EI.
pose proof CEIL as CEIL'. idtac. unfold GETFROM_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.
pose proof (max_count_facts c ltac:(lia)) as [MC1 MC2].
assert (HK : 1 <= k <= 8) by (subst k; Z.div_mod_to_equations; lia). hide MC2.
assert (HKM : k <= max_count c) by lia.
assert (RIA : exists q, ri_addr RE c = 8 * q) by (exists (ri_addr RE c / 8); unfold ri_addr; rewrite RIq; unhide PAL; Z.div_mod_to_equations; lia).
destruct RIA as [qri RIA].
assert (SRB : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ unhide PAL. rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
assert (SFB : SH (fa_beg (ae_L RE) c) = SH (reg_beg (ae_L RE) c) + 469762048).
{ rewrite FB, RB. replace (prim_lo RE + c * 4294967296 + 3758096384) with (prim_lo RE + c * 4294967296 + 8 * 469762048) by lia. apply SH_plus8. }

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. apply class_rep_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & P13 & _ & _ & Q1 & G2 & G3 & G4 & G5). hide G5.
pose proof (cr_pure_div8 a G c (K c) PU ltac:(lia)) as ((qa & QA0 & QA & QAE) & _ & _). hide QAE.
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
cbv beta delta [ri_cells] in RI. cbv beta delta [pc_cells] in PC0. rewrite CNT0 in P2, PC0. rewrite EI in PC0. unfold ri_addr, pc_addr in *.
assert (LFL : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K c)))) = c_num_freed (cls a c)) by (rewrite length_map; exact P1).
rewrite KS in P13.
rtc RT 24%nat K24. unfold A_INSTANCE in *.
assert (AMO : amo_aligned AD (wz (region_info RE + 128 * c)) = true).
{ apply amo_aligned_intro8; [lia| rewrite RIA, Z.mul_comm; apply Z_mod_mult]. }

remember (region_info RE + 128 * c) as RIc eqn:ERIc.

pose proof (munch_refl [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 8)] m) as MU0. pose proof (wmono_refl asegs m) as WM.
unfold getfrom_entry. apply aimplT_from_evt.
carve_frame 128%nat ST.
do 14 step.
step. step. step.
step. step.
do 12 step.
rewrite !(unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2^7) with 128. change (2^32) with 4294967296.
replace (region_info RE + c * 128) with RIc by lia.
replace (al_space_beg (ae_L RE) + (c * 4294967296 + 3758096384)) with (fa_beg (ae_L RE) c) by (rewrite FB; unfold prim_lo; lia).
step.
step.
do 5 step.
stp. step. if_lit.
stp. stp.
amo_step AMO.
step. if_lit.
amo_step AMO. fix_lit_store.
step. if_lit.
step. if_lit.
step.
step.
unfold_cond. rewrite (unsigned_lit (c_num_freed (cls a c))), (unsigned_lit k) by lia.
match type of FR with rw_cells _ _ _ (CB 24 ?J :: _) => set (fj := J) in FR end.
apply evt_done. unfold get_from_allocator.

lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RPL : RPrimL a G RE X mm c MUTEX_HELD);
[ eapply (RPrimL_reclose a a G G RE X m mm c K (K c) MUTEX_HELD RL HJS GNE (fun c0 H _ => HCall c0 H) ltac:(rewrite K32; lia));
[ intros; reflexivity| reflexivity| intros; reflexivity| intros; lia| exact WM
| eapply agree_other_classes; [exact RL| lia| exact MU0| exact WM|];
apply Forall_cons; [cbn; left; lia|]; apply Forall_cons; [| apply Forall_nil]; cbn -[fp_cls]; do 2 right; intros z Hz; left; unfold ri_addr; rewrite <- ERIc; lia
| apply class_repL_split; split; [| split; [exact PU|]];
[ split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; unfold ri_addr; rewrite <- ERIc; unfold MUTEX_HELD; exact RI|];
split; [cbv beta delta [pc_cells]; rewrite CNT0, EI; unfold pc_addr; exact PC0|];
exists CH; unfold pc_addr; split; [exact ACH| split; [exact LCH| exact HCH]]
| intros _; split; [exact FA|]; split; [eapply hjunk_wmono; [exact FJ| exact WM]|];
split; [| eapply hjunk_wmono; [exact FS| exact WM]];
eapply cr_user_agree; [exact PU| exact HU| lia|];
eapply agree_on_of_munch; [exact MU0| exact WM|]; intros z Uz Hz; apply (uzone_bounds RE X c z RL ltac:(lia)) in Uz; cbn [outside];
clear - Uz Hz SRB RB ERIc RIq PK PCH PH TK TB TD CEIL LO Hc; lia ] ]
| ] end.

lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (MU : munch [(bv_unsigned sp - 640, bv_unsigned sp); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80);
(rl_T X + 2768, rl_T X + 3168); (RIc, RIc + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + 536870912);
(SH (reg_beg (ae_L RE) c) + 469762048, SH (reg_beg (ae_L RE) c) + 469762048 + 67108864);
(reg_beg (ae_L RE) c + 8 * qa, reg_beg (ae_L RE) c + 3758096384);
(SH (reg_beg (ae_L RE) c) + qa, SH (reg_beg (ae_L RE) c) + 469762048)] m mm)
by (eapply munch_weaken; [| exact MU0]; sub_fp_solve);
assert (MUP : munch [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)] m mm)
by (eapply munch_weaken; [| exact MU0]; sub_fp_solve)
end.
clear MU0.
assert (FW3rt : Forall (rt_avoid RE X) [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)]).
{ apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]|].
apply Forall_cons; [apply rt_avoid_prim; [exact RL| rewrite ERIc, RIq; lia| rewrite ERIc, RIq, PH; lia]|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
assert (FW3st : Forall st_avoid [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)]).
{ repeat (apply Forall_cons; [st_avoid_solve|]). apply Forall_nil. }
lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RT1 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MUP| exact WM| exact FW3rt]);
assert (RS1 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MUP| exact WM| exact FW3st]) end.
destruct (Z.ltb_spec (c_num_freed (cls a c)) k) as [LT|GE].
2:{
lazymatch goal with |- aimplT _ _ _ _ ?ms0 =>
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\ ms' = ms0) end.
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb].
replace (c_num_freed (cls a c) <? k) with false by (symmetry; apply Z.ltb_ge; lia).
apply aimplT_ret.
step. rewrite (unsigned_lit (c_num_freed (cls a c))), (unsigned_lit k) by lia.
step.
step. ifz.
eapply (getfrom_tail ra gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra sp F fc m m _ s a a G G K c k lo RIc
j1 j2 j3 j4 CH fj RL Hc HK ltac:(lia) HKM CNT0 EI ERIc CEIL' ltac:(unfold GETFROM_STACK; lia) ltac:(lia) (gstep_refl RE X a G));
[ | | exact MI| exact ST| exact_gfaW MU ERIc QA SFB| exact WM| exact MUP| exact WM| exact FR| unfold MUTEX_HELD; exact RI| exact PC0| exact ACH| exact LCH| exact FA
| exact HJS| exact GNE| intros c0 H0 _; exact (HCall c0 H0)| exact PU| exact FJ| exact HU
| rewrite KS in FS; replace 536870912 with (8 * 67108864) in FS by reflexivity; rewrite SH_plus8 in FS; exact FS].
- eapply RTconst_munch; [exact RT| exact MUP| exact WM| exact FW3rt].
- eapply RStats_munch; [exact RS| exact MUP| exact WM| exact FW3st]. }

clear MUP. eapply aimplT_bind.
{ apply aimplT_from_evt.
step. step. step.
step.
rewrite (unsigned_lit (c_num_freed (cls a c))), (unsigned_lit k) by lia.
step. step. step.
apply evt_done. subst RIc.
eapply (aimplT_tall atn); [apply populate_prel|].
eapply (populate_spec L RE X); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold POPULATE_STACK. lia.
- lia. }
intros [ok a1] s' ms' [PREL POST]. cbn [snd] in PREL.
unfold pop_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & kk & -> & -> & MU2 & WM2 & MI2 & ST2 & RT2 & RS2 & RP2 & A0).
cbn [fst snd] in A0, RP2. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -128)) in * by lia.
replace (ret_pc (wz 280024)) with (wz 280024) by (symmetry; apply ret_pc_even; [lia| reflexivity]). rewrite <- !ERIc.
unfold pop_W, POPULATE_STACK, ri_addr in MU2. rewrite <- ERIc, ?KS, ?KO in MU2.
change (536870912 / 8) with 67108864 in MU2. change (3758096384 / 8) with 469762048 in MU2. rewrite QA, SH_plus8, SFB in MU2.
clear RI PC0 ACH HCH FA FJ HU FS RPL.
hide MU. transport_after_call asegs m1 m2 MU2 WM2. unhide MU.
assert (MU' : munch _ m m2) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
clear MU MU2 WM2 MI RT RS RT1 RS1; try clear ST; rename MU' into MU; rename MI2 into MI; rename ST2 into ST; rename RT2 into RT; rename RS2 into RS.
destruct ok; cbn [negb].
-
destruct (RPrimL_open _ _ _ _ _ _ _ RP2) as (K2 & HJS2 & GNE2 & HCall2 & _ & HC2). apply class_repL_split in HC2.
destruct HC2 as (((k1 & k2 & k3 & k4 & RI) & PC0 & (CH2 & ACH & LCH2 & HCH2)) & PU2 & REG2).
specialize (REG2 ltac:(lia)). destruct REG2 as (FA & FJ & HU & FS).
pose proof PU2 as (R1 & R2 & _ & _ & _ & _ & _ & _ & _ & R10 & R11 & R12 & R13 & _ & _ & S1 & _).
destruct PREL as (EO & EIa & ER & EN & CNT1). rewrite CNT0 in CNT1.
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. rewrite EIa, EI, CNT1 in PC0. unfold ri_addr, pc_addr in RI, PC0, ACH, FA, FJ, HU, FS. rewrite <- ERIc in RI.
rewrite KS in R13, FS. replace 536870912 with (8 * 67108864) in FS by reflexivity. rewrite SH_plus8 in FS.
assert (LFL2 : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K2 c)))) = c_num_freed (cls a1 c)) by (rewrite length_map; exact R1).
assert (AUle : c_alloc_user (cls a c) <= c_alloc_user (cls a1 c)).
{ rewrite gappend_class, length_app, repeat_length in S1. clear - Q1 S1 SZ1. nia. }
pose proof (munch_refl [(bv_unsigned sp - 640, bv_unsigned sp); (RIc, RIc + 128); (rl_T X + 208 + 80 * c, rl_T X + 208 + 80 * c + 80)] m2) as MUP.
pose proof (wmono_refl asegs m2) as WMP.
apply aimplT_from_evt.
step. ifz.
step.
step.
step.
unfold_cond. rewrite (unsigned_lit (c_num_freed (cls a1 c))), (unsigned_lit k) by lia.
destruct (Z.ltb_spec (c_num_freed (cls a1 c)) k) as [LT1|GE1].
{  apply evt_done. apply aimplT_unr. }
step.
step.
rewrite (unsigned_lit (c_num_freed (cls a1 c))), (unsigned_lit k) by lia.
step.
step. step.
apply evt_done. apply aimplT_ret.
eapply (getfrom_tail _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra sp F fc m m2 _ s a a1 G _ K2 c k lo RIc
k1 k2 k3 k4 CH2 fj RL Hc HK ltac:(lia) HKM CNT1 ltac:(rewrite EIa; exact EI) ERIc CEIL' ltac:(unfold GETFROM_STACK; lia) AUle);
[ eapply (gstep_populate RE X a a1 G c (K c) (K2 c) kk); [rewrite K32; lia| split; [exact EO| split; [exact EIa| split; [exact ER| split; [exact EN| rewrite CNT0; exact CNT1]]]]| exact PU| exact PU2]
| | | exact MI| exact ST| exact_gfaW MU ERIc QA SFB| exact WM| exact MUP| exact WMP| exact FR| unfold MUTEX_HELD; exact RI| exact PC0| exact ACH| exact LCH2| exact FA
| exact HJS2| exact GNE2| exact HCall2| exact PU2| exact FJ| exact HU| exact FS].
+ eapply RTconst_munch; [exact RT| exact MUP| exact WMP| exact FW3rt].
+ eapply RStats_munch; [exact RS| exact MUP| exact WMP| exact FW3st].
-
pose proof (RPrimL_mutex _ _ _ _ _ _ _ RP2) as HD. unfold ri_addr in HD. rewrite <- ERIc in HD. unfold MUTEX_HELD in HD.
destruct (RPrimL_open _ _ _ _ _ _ _ RP2) as (K2 & _ & _ & _ & _ & HC2). apply class_repL_split in HC2. destruct HC2 as (_ & PU2 & _).
apply aimplT_ret.
step. if_lit.
stp.
step. step.
eapply getfrom_unlock with (lo := lo); [exact HD| exact AMO| lia| lia| exact MI| exact ST| exact CEIL'| lia| exact FR|].
intros m3 u0' u1' u2' u3' w1 w2 w3 w4 w5 w6 w7 MI3 MU3 WM3 HD3 ST3.
assert (RP3 : RPrim a1 (gappend c (repeat TFree kk) G) RE X m3).
{ eapply RPrimL_un0. eapply RPrimL_set_mutex_stk; [exact RP2| exact RL| | unfold ri_addr; rewrite <- ERIc; exact MU3| exact WM3| unfold ri_addr; rewrite <- ERIc; exact HD3].
idtac. lia. }
clear HD FR. hide MU. transport_after_call asegs m2 m3 MU3 WM3. unhide MU.
assert (MU' : munch _ m m3) by (eapply munch_chain; [exact MU| exact MU3| sub_fp_solve]). clear MU; rename MU' into MU.
apply evt_done. unfold gfa_post. do 16 eexists. exists (gappend c (repeat TFree kk) G).
split; [reflexivity|]. split; [reflexivity|].
split; [exact_gfaW MU ERIc QA SFB|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
split. { eapply RTconst_munch; [exact RT| exact MU3| exact WM3|].
apply Forall_cons; [apply rt_avoid_stack; [exact RL| lia]|].
apply Forall_cons; [apply rt_avoid_prim; [exact RL| rewrite ERIc, RIq; lia| rewrite ERIc, RIq, PH; lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS| exact MU3| exact WM3|].
repeat (apply Forall_cons; [st_avoid_solve|]). apply Forall_nil. }
split. { cbn [snd]. destruct PREL as (EO & EIa & ER & EN & CNT1).
eapply (gstep_populate RE X a a1 G c (K c) (K2 c) kk); [rewrite K32; lia| split; [exact EO| split; [exact EIa| split; [exact ER| split; [exact EN| exact CNT1]]]]| exact PU| exact PU2]. }
split; [reflexivity|]. cbn [fst snd]. exact RP3.
Qed.
End S.
