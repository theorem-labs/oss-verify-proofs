(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z Qdyh Q7UD Qhd4 Qwm6 QlKV QsKa Qiiq Q1Ey Ql4f QrQv QYZ0 Q228 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3 Qdyh.Mq6.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QYZ0.Mq3 Q228.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt3A (c : Z) : Z :=
match c with
| 34 | 47 | 92 => 0x96d2c
| 117 => 0x96edc
| 98 | 102 | 110 | 114 | 116 => 0x96060
| _ => 0x98bec
end.

Definition pe_jtab3A : list byte := Eval vm_compute in match image_bytes asegs 0x22da8 336 with Some bs => bs | None => [] end.
Lemma pe_jtab3A_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22da8 [CB 336 pe_jtab3A].
Proof.
intros m MI. change 336%nat with (length pe_jtab3A).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab3A)) with 336%Z. lia.
Qed.
Definition pe_jtab4A : list byte := Eval vm_compute in match image_bytes asegs 0x22ef8 40 with Some bs => bs | None => [] end.
Lemma pe_jtab4A_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22ef8 [CB 40 pe_jtab4A].
Proof.
intros m MI. change 40%nat with (length pe_jtab4A).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab4A)) with 40%Z. lia.
Qed.

Lemma pe_jt3A_cases : forall c, (pe_jt3A c = 0x96d2c /\ (c = 34 \/ c = 47 \/ c = 92)) \/ (pe_jt3A c = 0x96edc /\ c = 117)
\/ (pe_jt3A c = 0x96060 /\ (c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116)) \/ pe_jt3A c = 0x98bec.
Proof.
intros c. unfold pe_jt3A. destruct c as [|p|p]; [tauto | | tauto].
do 8 (try (destruct p as [p|p|]; try tauto)).
Qed.

Section PeSSescDA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Lemma sesc_dispatch_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(forall a3' a4',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jt3A (bv_unsigned cb)) (t_co ts) gp t0 t1 t2 a0 (Z_to_bv 64 (bv_unsigned cb)) a2 a3' a4' a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_string_escape) (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR). pose proof REST as (HP & _).
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (_ & _ & _ & FF & _). unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtab3A_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_string_escape. cbn [pe_jtA].
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step.
destruct (Z_lt_dec (bv_unsigned cb) 34) as [LT | GE].
- replace (Z_to_bv 64 (bv_unsigned cb + -34)) with (Z_to_bv 64 (bv_unsigned cb + -34 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -34) 1 (2^64)). f_equal. }
step. if_falsex. step. evt_done5.
replace (pe_jt3A (bv_unsigned cb)) with 0x98bec in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 117 (bv_unsigned cb)) as [GT | LE].
+ step. if_falsex. step. evt_done5.
replace (pe_jt3A (bv_unsigned cb)) with 0x98bec in K. 2:{ assert (R : 118 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 118%Z 138%nat; reflexivity. }
apply K.
+ step. if_truex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.
pose proof (bytes_at_read asegs m 0x22da8 pe_jtab3A ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab3A) with 336%nat; lia)) as RD.
unfold wa in RD. replace (0x22da8 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 142760) in RD by lia.
step. step. step.
evt_done5.
assert (R : 34 <= bv_unsigned cb <= 117) by lia.
match goal with |- AJ5 _ _ _ _ _ (MS _ _ ?pc _ _ _ _) =>
replace pc with (Z_to_bv 64 (pe_jt3A (bv_unsigned cb))); [apply K |] end.
clear - R. enum_from (bv_unsigned cb) 34%Z 84%nat; apply bv_eq; vm_compute; reflexivity.
Qed.
End PeSSescDA.
End RC__1.
End Mq0.
From Stdlib Require NArith Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg Lib.SepCache Qfw3_c1 QTEu QnCn Q30W Q4v2 QgHv Q1Y6 Q4xz Q9O6 QL3k QnPO QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq3 Q30W.Mq0 Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 Q4xz QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Q228.Mq4 Qwm6.Mq1 QnPO.Mq0 Q228.Mq6.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac post_callS segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callS" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callS segs m ]
end.

Ltac if_rw E b :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (rewrite E; vm_compute; reflexivity)
end; cbv iota.

Lemma land1_cases : forall fl, 0 <= fl -> Z.land fl 1 = 0 \/ Z.land fl 1 = 1.
Proof.
intros fl H. change 1 with (Z.ones 1) at 1. change 1 with (Z.ones 1) at 2. rewrite !Z.land_ones by lia.
change (2^1) with 2. pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia.
Qed.
Lemma land58_bit : forall fl b, Z.land fl 58 = 0 -> Z.land 58 b = b -> Z.land fl b = 0.
Proof. intros fl b H Hb. rewrite <- Hb. rewrite Z.land_assoc, H. reflexivity. Qed.
Lemma land3_of_58 : forall fl, Z.land fl 58 = 0 -> Z.land fl 3 = Z.land fl 1.
Proof.
intros fl H. change 3 with (Z.lor 1 2). rewrite Z.land_lor_distr_r. rewrite (land58_bit fl 2 H eq_refl). apply Z.lor_0_r.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Arr.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo p rc pb0 lv fl a arr size bpos0 cap0 w : Z).
Variables (ps : list Z) (KBS : list (list blk)) (kids : list (option jshape)) (T : TSet) (Y R : list blk).
Let usp := bv_unsigned sp.
Hypothesis KIDS : forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s'.
Hypothesis FL : aflags_ok fl.
Hypothesis Hlv : 0 <= lv.
Hypothesis Hlvd : lv + sdepth (Sarr kids) <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ser_budgetA (Sarr kids).
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis FRSN : Z.of_nat (length FRS) + 1 < 4096.
Hypothesis INCL : incl ((p, 48) :: [(a, AL_SZ); (arr, 8 * size)] ++ concat KBS) LB.
Hypothesis NODE0 : rw_cells asegs m0 p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string A4F) pb0 0 0 ++ [C8 (wz a)]).
Hypothesis AL0 : alist asegs A4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps.
Hypothesis KOK : kids_okp asegs A4F m0 kids ps KBS.
Hypothesis JTX : jtxk_arr kids (concat KBS ++ Y) 24 = Some (w, R).
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w).
Let LEN := Z.of_nat (length ps).
Definition savedR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma facts :
0 <= usp < 2^64 /\ In (p, 48) LB /\ 0 <= fl < 2^31 /\
Z.land fl 2 = 0 /\ Z.land fl 8 = 0 /\ Z.land fl 32 = 0 /\ Z.land fl 3 = Z.land fl 1 /\ (Z.land fl 1 = 0 \/ Z.land fl 1 = 1) /\
0 <= kdepth kids /\ lo <= usp - 160 - 256 * kdepth kids - 16384 - 96 /\
LEN = Z.of_nat (length kids) /\ length KBS = length kids /\ LEN <= size /\ 1 <= size /\ 8 * size < 2^64.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (INp : In (p, 48) LB) by (apply INCL; left; reflexivity).
destruct FL as [Rfl FL58].
pose proof (kdepth_nonneg kids) as KD. unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS. rewrite sdepth_arr in LOS.
destruct (kids_okp_len _ _ _ _ _ _ KOK) as [L1 L2].
destruct AL0 as (arr' & size' & junk & E & Hps & Hsz & _). injection E as _ E2. assert (size' = size) by lia. subst size'.
split; [exact SPR|]. split; [exact INp|]. split; [exact Rfl|].
split; [exact (land58_bit fl 2 FL58 eq_refl)|]. split; [exact (land58_bit fl 8 FL58 eq_refl)|]. split; [exact (land58_bit fl 32 FL58 eq_refl)|].
split; [exact (land3_of_58 fl FL58)|]. split; [apply land1_cases; lia|].
split; [exact KD|]. split; [unfold usp in *; lia|].
unfold LEN. repeat split; try assumption; lia.
Qed.

Lemma factsM : forall A FA CH e m md, ser_memx A FRS FA CH e m md ->
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
rw_cells asegs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string A4F) pb0 0 0 ++ [C8 (wz a)]) /\
ro_cells asegs m (p / 8 + 2147450885) [C1 (Z_to_bv 8 0)] /\
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps /\
kids_okp asegs A4F m kids ps KBS.
Proof.
intros A FA CH e m md (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & INp & _).
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp')) as (_ & Hpal & Hplo & Hphi & _).
assert (AG : agree_on asegs LB m0 m).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app. left. exact Hb. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]. }
split. { pose proof (blk_granS HIx _ _ _ _ _ _ _ p 48 5 HP INp' ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia. exact SH5. }
split. { eapply (alist_agree asegs A4F); [exact AL0 | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. left. exact Hb. }
eapply (kids_okp_agree asegs A4F); [exact KOK | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. right. exact Hb.
Qed.

Lemma al_lengthE : forall (x1 x4 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' A FA CH e m md,
ser_memx A FRS FA CH e m md -> lo <= FA - 16 -> FA <= usp ->
evt asegs (array_list_length_A_post x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' a3 a4 ps m lo)
(MS (mkR x1 (wz FA) gp x4 t0 t1 t2 x8 x9 (wz a) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz array_list_length_A_entry) fc' None m (seg_rom asegs)).
Proof.
intros until md. intros INV LOF FAU.
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & AL & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INa : In (a, 32) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; left; reflexivity).
assert (INr : In (arr, 8 * size) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INa)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INr)) as (_ & Hral & Hrlo & Hrhi & _).
shadow_inA A4L HIx HP INa SHa.
pose proof alloc_ceiling_range as ACR.
assert (UF : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
eapply (array_list_length_A x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' (wz a) a1 a2 a3 a4 m lo _ a arr size ps).
- unfold small_pre. rewrite UF. split; [exact MI|]. split; [exact ST|]. split; [lia|]. split; [exact LO|]. split; [exact GOT|]. split; [exact CELL|].
a4l_goal. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- exact AL.
- reflexivity.
- unfold al_blkA. repeat split; try lia; clear - Haal Hral; Z.div_mod_to_equations; lia.
- exact SHa.
Qed.

Lemma al_get_idxE : forall (x1 x4 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' A FA CH e m md i,
ser_memx A FRS FA CH e m md -> lo <= FA - 16 -> FA <= usp -> 0 <= i < 2^64 ->
evt asegs (array_list_get_idx_A_post x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' ps i m lo)
(MS (mkR x1 (wz FA) gp x4 t0 t1 t2 x8 x9 (wz a) (wz i) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz array_list_get_idx_A_entry) fc' None m (seg_rom asegs)).
Proof.
intros until i. intros INV LOF FAU Hi.
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & AL & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INa : In (a, 32) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; left; reflexivity).
assert (INr : In (arr, 8 * size) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INa)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INr)) as (_ & Hral & Hrlo & Hrhi & _).
shadow_inA A4L HIx HP INa SHa.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr) as SHr. unfold shad in SHr. cbn [hl_sb hl_segs hla_base A4L A4H] in SHr.
pose proof alloc_ceiling_range as ACR.
assert (UF : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
eapply (array_list_get_idx_A x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' (wz a) (wz i) a2 a3 a4 m lo _ a arr size ps i).
- unfold small_pre. rewrite UF. split; [exact MI|]. split; [exact ST|]. split; [lia|]. split; [exact LO|]. split; [exact GOT|]. split; [exact CELL|].
a4l_goal. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- exact AL.
- reflexivity.
- reflexivity.
- exact Hi.
- unfold al_blkA. repeat split; try lia; clear - Haal Hral; Z.div_mod_to_equations; lia.
- exact SHa.
- exact SHr.
Qed.

Lemma arr_failA :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -160) [(usp + -160, PRE ++ savedR)] e m md -> cells_size PRE = 56%nat ->
0 <= e <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9b750) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 56) with 56 in SAVc.
replace (usp + -160 + 56) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -160) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 56) with 56 in S1.
replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS' | intros _; exact FR']|].
split; [exact VM|]. split; [exact STU|]. split; [exact HPR|]. split; [exact ERR|]. split; [exact HP|]. split; [exact PB|].
split; [lia|]. split; [exact Hcap|]. split; [exact HBB | exact HBD].
Qed.

Lemma arr_closeA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -160) [(usp + -160, PRE ++ savedR)] e m md -> cells_size PRE = 56%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9b94c) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 56) with 56 in SAVc.
replace (usp + -160 + 56) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof PB as (Hbp0 & Hcap0 & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. rewrite (unsigned_lit fl) by lia. rewrite FL3.
step. step.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -160) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 56) with 56 in S1.
replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
assert (INVU : ser_memx A FRS (bv_unsigned sp) [] e m md).
{ exists buf, cap, bpos, content, errv, B.
split; [exact HP|]. split; [exact PB|]. split; [constructor|]. split; [constructor|]. split; [exact FSUB|].
split; [exact ERR|]. split; [exact STU|]. split; [exact HPR|]. split; [exact VM|].
split; [exact Hbp|]. split; [exact Hcap|]. split; [exact HBB | exact HBD]. }
assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> src_ro_chk lit k = true -> 0 < k <= 2 -> 0 <= lit -> lit + k < 2^32 ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra sp gp (Z_to_bv 64 6434400) t0_ t1_ t2_ s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3_ a4_ a5_ a6_ a7_
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F' (Z_to_bv 64 0x9a0ac) fc' None m (seg_rom asegs))).
{ intros lit k bs t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ RB BL CHK Hk Hl Hlk.
evt_done5.
rewrite <- (Z_to_bv_bv_unsigned ra) at 1. rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF lit k bs RB BL CHK ltac:(lia) Hl Hlk) with (F := F) (e := e);
[ exact INVU | exact He | lia | lia | exact SPA | lia | lia | reflexivity | word_range ra RAR; lia | exact RA | exact FS' | exact FR' | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & _ & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply K. unfold ser_postA.
exists m2, a0', errv2, buf2, cap2, bpos2, content2, B2.
rewrite !Z_to_bv_bv_unsigned.
assert (ERA : ra = ret_pc ra).
{ word_range ra RAR. rewrite <- (Z_to_bv_bv_unsigned ra) at 2. rewrite ret_pc_even by (try exact RA; lia). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [unfold ret_statew; do 16 eexists; split; [rewrite <- ERA; reflexivity|]; split; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [lia|]. split; [exact Hc2|]. split; [exact HB2 | exact HD2]. }
destruct FC1 as [E1 | E1]; rewrite E1.
-
if_lit. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x23840 1 LIT_RBRACK); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
-
if_lit. step. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x23820 2 LIT_SP_RBRACK); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
Qed.

Lemma arr_exitA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (c0 : word) (PRE : list cell) e,
ser_memx A FRS (usp + -160) [(usp + -160, (C8 c0 :: PRE) ++ savedR)] e m md -> cells_size PRE = 48%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 (wz 0) x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9b944) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. cbn [app] in CHm.
apply (proj1 (rw_cells_app asegs _ _ [C8 c0] _)) in CHm. destruct CHm as [C0c RESTc]. stash RESTc. stash INV.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
evt_done5. unstash INV.
eapply arr_closeA; [exact INV | cbn [cells_size csize Nat.add]; rewrite HPRE; reflexivity | exact He | exact Hew | exact FS' | exact FR'].
Qed.

Lemma kid_callA : forall (pc0 retpc : Z) (s' : jshape) (v pbk : Z) (RESTk : list blk)
(x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x19 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' A CH e m md,
(pc0 = 0x9b724 /\ retpc = 0x9b74c) \/ (pc0 = 0x9b8b8 /\ retpc = 0x9b8e0) ->
ser_memx A FRS (usp + -160) CH e m md -> jnode asegs A4F s' m RESTk v 1 pbk -> incl RESTk LB ->
(AJ5 A4L HIx A T md (MS (mkR (wz retpc) (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 (wz v) (wz pb) (wz (lv + 1)) (wz fl) (wz (afn_of s')) a5 a6 a7
(wz fl) x19 (wz (lv + 1)) (wz 2147450880) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz (afn_of s')) fc' None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 (wz v) a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 (wz (lv + 1)) (wz 2147450880) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz pc0) fc' None m (seg_rom asegs)).
Proof.
intros until md. intros PCS INV JN INCLk KONT.
pose proof facts as (SPR & _ & Rfl & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
assert (INv : In (v, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCLk; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; exact INv)) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ v n 1 HP INv ltac:(lia) ltac:(lia)) as SHv.
replace (v / 8 + 2147450880 + 1) with (v / 8 + 2147450881) in SHv by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] cs)) in HDR. destruct HDR as [HDR _].
clear INV JN.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l.
unfold afn_of in KONT.
destruct PCS as [[-> ->] | [-> ->]].
- reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
destruct s' as [|[|]| |[|]|kids'|kids'];
(lazymatch type of HDR with context [fn_ofF A4F ?s] => let fv := eval vm_compute in (fn_ofF A4F s) in change (fn_ofF A4F s) with fv in HDR, KONT end);
step; do 3 step; step; fold_mkR; evt_done5; exact KONT.
- reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
destruct s' as [|[|]| |[|]|kids'|kids'];
(lazymatch type of HDR with context [fn_ofF A4F ?s] => let fv := eval vm_compute in (fn_ofF A4F s) in change (fn_ofF A4F s) with fv in HDR, KONT end);
step; do 3 step; step; fold_mkR; evt_done5; exact KONT.
Qed.

Definition arrFR : list cell :=
[C8 (wz lv); C8 (wz 0x234e0); C8 (wz 0x23540); C8 (wz 0x23480); C8 (wz (2 * (lv + 1))); C8 (wz 0); C8 (wz 0)] ++ savedR.

Definition st_loop (pc i : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz (p / 8 + 2147450885)) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (p + 40)) (wz (lv + 1)) (wz 2147450880) (wz i) (wz 0x23440) (wz 0) (wz 0x23360) (wz (Z.land fl 1)) (wz 0x23460) t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom asegs).

Definition loopK (bound : Z) : Prop :=
forall (i acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound ->
pbtail P -> jtxk_arr (skipn (Z.to_nat i) kids) (P ++ concat (skipn (Z.to_nat i) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -160) [(usp + -160, arrFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9b834 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).

Lemma arr_nextA : forall bound, loopK bound ->
forall (i acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat (i + 1)) kids) (P ++ concat (skipn (Z.to_nat (i + 1)) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -160) [(usp + -160, arrFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9b934 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & AL & KOKm).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold arrFR, savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp)] m) as MU.
stash INV. stash AL. stash KOKm.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step. fold_mkR.
unstash INV.
callS (al_lengthE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -160) _ (acc - 2) m md INV ltac:(lia) ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -160) [(bv_unsigned sp + -160, arrFR)] (acc - 2) m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
fold LEN.
step.
destruct (Z.ltb_spec (i + 1) LEN) as [LT | GE].
- if_truex. fold_mkR. evt_done5.
eapply (IH (i + 1) acc P); [lia | lia | exact HP0 | exact JT | exact Hacc | exact INV2 | exact FS' | exact FR'].
- if_falsex. fold_mkR. evt_done5.
assert (Ew : w = acc) by (eapply (jtxk_arr_done kids (Z.to_nat (i + 1))); [lia | exact JT]).
eapply arr_exitA with (c0 := Z_to_bv 64 lv) (e := acc - 2)
(PRE := [C8 (Z_to_bv 64 0x234e0); C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x23480); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]);
[exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'].
Qed.

Lemma arr_ret_kidA : forall bound, loopK bound ->
forall (i acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat (i + 1)) kids) (P ++ concat (skipn (Z.to_nat (i + 1)) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc -> acc <= w ->
ser_memx A FRS (usp + -160) [(usp + -160, arrFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9b8e0 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc Haw INV FS' FR'.
pose proof facts as (SPR & _).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & _ & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_cases NEG; fold_mkR.
- evt_done5. unstash INV.
eapply arr_failA with (e := acc - 2)
(PRE := [C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0x234e0); C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x23480); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]);
[exact INV | reflexivity | lia | exact FS' | exact FR'].
- step. step. if_lit. fold_mkR.
evt_done5. unstash INV.
eapply (arr_nextA bound IH i acc P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
Qed.
Lemma arr_ret_nullA : forall bound, loopK bound ->
forall (i acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat (i + 1)) kids) (P ++ concat (skipn (Z.to_nat (i + 1)) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -160) [(usp + -160, arrFR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9b92c i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & _).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & _ & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit. fold_mkR.
evt_done5. unstash INV.
eapply (arr_nextA bound IH i acc P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
Qed.

Lemma arr_elemA : forall bound, loopK bound ->
forall (i acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat i) kids) (P ++ concat (skipn (Z.to_nat i) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -160) [(usp + -160, arrFR)] acc m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9b8a0 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold arrFR, savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
step. step. step. fold_mkR.
unstash INV.
callS (al_get_idxE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -160) _ acc m md i INV ltac:(lia) ltac:(lia) ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -160) [(bv_unsigned sp + -160, arrFR)] acc m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
fold LEN. replace (i <? LEN) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (factsM _ _ _ _ _ _ INV2) as (_ & _ & _ & _ & _ & _ & KOK2).
pose proof (al_nth_in ps i ltac:(fold LEN; lia)) as NTHp.
destruct (nth_error kids (Z.to_nat i)) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
destruct k as [s'|].
-
destruct (kids_okp_nth asegs A4F _ _ _ _ _ _ KOK2 NTHk) as (v & bs & Hv & Hbs & _).
rewrite NTHp in Hv. injection Hv as Hv.
destruct (jtxk_arr_step_some asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ _ KOK2 NTHk NTHp Hbs HP0 JT) as (Hvnz & JV & pbk & PBSk & RESTk & wi & P' & Ebs & JN & Hwi & Haw & JTXk & HP' & JT').
rewrite Hv in *. clear Hv.
assert (INk : In (Some s') kids) by (eapply nth_error_In; exact NTHk).
assert (INCLk : incl RESTk LB).
{ intros bq Hbq. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | rewrite Ebs; apply in_or_app; left; exact Hbq]. }
pose proof (kdepth_in _ _ INk) as KDk.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & _).
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP2 ltac:(apply in_or_app; left; right; right; apply INCLk; rewrite ER; left; reflexivity)) as (_ & _ & Hvlo & Hvhi & _).
unfold_consts.
step. if_falsex. fold_mkR.
evt_done5.
eapply (kid_callA 0x9b8b8 0x9b8e0 s' v pbk RESTk); [right; split; reflexivity | exact INV2 | exact JN | exact INCLk |].
eapply (ser_childA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 (afn_of s') s' (KIDS s' INk)) with (F := F) (e := acc);
[ exact INV2 | exact JN | exact INCLk | exact JTXk | lia | lia | exact FL | lia | rewrite sdepth_arr in Hlvd; lia | exact FRSN
| unfold ser_budgetA, ASER_LEVEL, ASER_LEAF; lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in JT' by lia.
eapply (arr_ret_kidA bound IH i (acc + (2 + wi)) P'); [lia | lia | exact HP' | exact JT' | lia | lia | | exact FS3 | exact FR3].
replace (acc + (2 + wi) - 2) with (acc + wi) by lia. exact INV3.
-
destruct (jtxk_arr_step_none asegs A4F _ _ _ _ _ _ _ _ _ _ KOK2 NTHk HP0 JT) as (Hv0 & Haw & JT').
rewrite NTHp in Hv0. injection Hv0 as Hv0. rewrite Hv0.
step. if_lit. step. step. step. if_lit. step. step. step. fold_mkR.
evt_done5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23360 4 LIT_NULL) with (F := F) (e := acc);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV2 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in JT' by lia.
eapply (arr_ret_nullA bound IH i (acc + 6) P); [lia | lia | exact HP0 | exact JT' | lia | | exact FS3 | exact FR3].
replace (acc + 6 - 2) with (acc + 4) by lia. exact INV3.
Qed.

Lemma arr_iter : forall bound, loopK bound -> loopK (bound + 1).
Proof.
intros bound IH. unfold loopK. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
assert (Haw : acc <= w) by (eapply (jtxk_arr_acc (fun _ => True)); [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JT]).
assert (Haw2 : acc + 2 <= w).
{ destruct (nth_error kids (Z.to_nat i)) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk) in JT. cbn [jtxk_arr] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JT). lia.
- pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JT). unfold NULL_W in *. lia. }
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23440 1 LIT_COMMA) with (F := F) (e := acc - 2);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
clear INV HP MI WM MU.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _ & CHm & _ & _ & _ & ST3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold arrFR, savedR in CHm. cbn [app] in CHm.
pose proof (wmono_refl asegs m3) as WM.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU.
stash INV3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. if_lit.
step.
destruct FC1 as [E1 | E1].
-
if_rw E1 true. fold_mkR. evt_done5. unstash INV3.
eapply (arr_elemA bound IH i acc P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
-
if_rw E1 false. step. step. step. step. fold_mkR.
evt_done5. unstash INV3.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23480 1 LIT_SPACE) with (F := F) (e := acc - 2 + 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV3 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros A4 m4 md4 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 INV4 FS4 FR4.
clear INV3 HP3 MI3 WM MU CHm ST3.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (wmono_refl asegs m4) as WM.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU.
stash INV4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. fold_mkR. evt_done5. unstash INV4.
eapply (arr_elemA bound IH i acc P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS4 | exact FR4].
replace (acc - 2 + 1 + 1) with acc in INV4 by lia. exact INV4.
Qed.

Lemma arr_loop : forall n, loopK (Z.of_nat n).
Proof.
induction n as [|n IH].
- unfold loopK. intros. lia.
- replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. apply arr_iter. exact IH.
Qed.

Lemma arr_after0A :
forall (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word) (j24 : list byte) F' fc' m md A,
1 <= LEN ->
pbtail P -> jtxk_arr (skipn 1 kids) (P ++ concat (skipn 1 KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -160) [(usp + -160, [C8 (wz lv); CB 24 j24; C8 (wz (2 * (lv + 1))); C8 (wz 0); C8 (wz 0)] ++ savedR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz (p / 8 + 2147450885)) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (p + 40)) (wz (lv + 1)) (wz 2147450880) (wz lv) (wz 0) (wz 0) x25 (wz (Z.land fl 1)) x27 t3 t4 t5 t6)
F' (wz 0x9b7dc) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros HL1 HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
step. step. fold_mkR.
unstash INV.
callS (al_lengthE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -160) _ (acc - 2) m md INV ltac:(lia) ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
fold LEN.
step. step.
destruct (Z.ltb_spec LEN 2) as [LT | GE].
-
if_truex. fold_mkR.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -160)
[(bv_unsigned sp + -160, (C8 (Z_to_bv 64 lv) :: [CB 24 j24; C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) ++ savedR)] (acc - 2) m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
assert (Ew : w = acc) by (eapply (jtxk_arr_done kids 1%nat); [lia | exact JT]).
eapply arr_exitA with (e := acc - 2); [exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'].
- if_falsex.
step. do 6 step.
step. step. stepz. step. step. stepz. step. stepz. step.
fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
assert (INV3 : ser_memx A FRS (bv_unsigned sp + -160) [(bv_unsigned sp + -160, arrFR)] (acc - 2) m3 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI3 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
pose proof (arr_loop (Z.to_nat LEN)) as LK. unfold loopK, st_loop in LK.
eapply (LK 1 acc P); [lia | lia | exact HP0 | exact JT | exact Hacc | exact INV3 | exact FS' | exact FR'].
Qed.

Lemma arr_elem0A :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word) (j32 j16 : list byte) F' fc' m md A,
1 <= LEN ->
ser_memx A FRS (usp + -160) [(usp + -160, [CB 32 j32; C8 (wz (2 * (lv + 1))); CB 16 j16] ++ savedR)] 2 m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz (p / 8 + 2147450885)) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (p + 40)) (wz (lv + 1)) (wz 2147450880) (wz lv) (wz 0) (wz 0) x25 (wz (Z.land fl 1)) x27 t3 t4 t5 t6)
F' (wz 0x9b6fc) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros HL1 INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
step. step. rewrite (unsigned_lit fl) by lia. rewrite FL32.
step. step. fold_mkR.
unstash INV.
callS (al_get_idxE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -160) _ 2 m md 0 INV ltac:(lia) ltac:(lia) ltac:(lia)).
fold LEN. replace (0 <? LEN) with true by (symmetry; apply Z.ltb_lt; lia).
step. stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -160)
[(bv_unsigned sp + -160, [C8 (Z_to_bv 64 lv); CB 24 (skipn 8 j32); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ savedR)] 2 m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI2 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
pose proof (factsM _ _ _ _ _ _ INV2) as (_ & _ & _ & _ & _ & _ & KOK2).
pose proof (al_nth_in ps 0 ltac:(fold LEN; lia)) as NTHp. change (Z.to_nat 0) with 0%nat in NTHp.
assert (JT0 : jtxk_arr (skipn 0 kids) ([] ++ concat (skipn 0 KBS) ++ Y) 24 = Some (w, R)) by exact JTX.
destruct (nth_error kids 0) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
destruct k as [s'|].
-
destruct (kids_okp_nth asegs A4F _ _ _ _ _ _ KOK2 NTHk) as (v & bs & Hv & Hbs & _).
rewrite NTHp in Hv. injection Hv as Hv.
destruct (jtxk_arr_step_some asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ _ KOK2 NTHk NTHp Hbs pbtail_nil JT0) as (Hvnz & JV & pbk & PBSk & RESTk & wi & P' & Ebs & JN & Hwi & Haw & JTXk & HP' & JT').
rewrite Hv in *. clear Hv.
assert (INk : In (Some s') kids) by (eapply nth_error_In; exact NTHk).
assert (INCLk : incl RESTk LB).
{ intros bq Hbq. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | rewrite Ebs; apply in_or_app; left; exact Hbq]. }
pose proof (kdepth_in _ _ INk) as KDk.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & _).
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP2 ltac:(apply in_or_app; left; right; right; apply INCLk; rewrite ER; left; reflexivity)) as (_ & _ & Hvlo & Hvhi & _).
unfold_consts.
step. if_falsex. fold_mkR.
evt_done5.
eapply (kid_callA 0x9b724 0x9b74c s' v pbk RESTk); [left; split; reflexivity | exact INV2 | exact JN | exact INCLk |].
eapply (ser_childA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 (afn_of s') s' (KIDS s' INk)) with (F := F) (e := 2);
[ exact INV2 | exact JN | exact INCLk | exact JTXk | lia | lia | exact FL | lia | rewrite sdepth_arr in Hlvd; lia | exact FRSN
| unfold ser_budgetA, ASER_LEVEL, ASER_LEAF; lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
clear INV INV2 HP HP2 MI2 WM MU CHm POST NODE SH5.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
pose proof (wmono_refl asegs m3) as WM.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU.
stash INV3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. if_cases NEG; fold_mkR.
+ evt_done5. unstash INV3.
eapply (arr_after0A (24 + (2 + wi)) P'); [exact HL1 | exact HP' | exact JT' | lia | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
+ evt_done5. unstash INV3.
eapply arr_failA with (e := 2 + wi)
(PRE := [C8 (Z_to_bv 64 lv); CB 24 (skipn 8 j32); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]);
[exact INV3 | reflexivity | lia | exact FS3 | exact FR3].
-
destruct (jtxk_arr_step_none asegs A4F _ _ _ _ _ _ _ _ _ _ KOK2 NTHk pbtail_nil JT0) as (Hv0 & Haw & JT').
rewrite NTHp in Hv0. injection Hv0 as Hv0. rewrite Hv0.
step. if_lit. step. if_lit. step. step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23360 4 LIT_NULL) with (F := F) (e := 2);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV2 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (arr_after0A (24 + 6) []); [exact HL1 | exact pbtail_nil | exact JT' | lia | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
Qed.

Lemma arr_startA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x20 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (j56 : list byte) F' fc' m md A,
ser_memx A FRS (usp + -160) [(usp + -160, [CB 56 j56] ++ savedR)] 1 m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -160)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz p) x20 (wz 2147450880) (wz lv) x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz 0x9b668) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Hw3 : 24 <= w) by (eapply (jtxk_arr_acc (fun _ => True)); [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
assert (Hlv1 : lv <= 999) by (rewrite sdepth_arr in Hlvd; lia).
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step. fold_mkR.
unstash INV.
callS (al_lengthE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -160) _ 1 m md INV ltac:(lia) ltac:(lia)).
fold LEN.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (Z.eq_dec LEN 0) as [L0 | LN0].
-
rewrite L0. if_lit. fold_mkR.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -160) [(bv_unsigned sp + -160, [CB 56 j56] ++ savedR)] 1 m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
eapply arr_closeA with (e := 1) (PRE := [CB 56 j56]); [exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'].
- if_falsex.
step. rewrite (unsigned_lit fl) by lia. rewrite FL2.
step. norm_w32.
step. rewrite (unsigned_lit fl) by lia. rewrite FL8.
step. norm_w32.
rewrite (Z.shiftl_mul_pow2 (lv + 1) 1) by lia. change (2^1) with 2. rewrite (swrap32_id ((lv + 1) * 2)) by lia. replace ((lv + 1) * 2) with (2 * (lv + 1)) by lia.
step. step. rewrite (unsigned_lit fl) by lia.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
lazymatch type of CHm with rw_cells _ _ _ ?frc =>
assert (INV3 : ser_memx A FRS (bv_unsigned sp + -160) [(bv_unsigned sp + -160, frc)] 1 m3 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI3 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
assert (HL1 : 1 <= LEN) by (unfold LEN in *; lia).
assert (Hw2 : 26 <= w).
{ destruct kids as [|k0 kids']; [cbn [length] in LENk; lia|]. clear - JTX. cbn [jtxk_arr] in JTX. destruct k0 as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JTX). lia.
- pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JTX). unfold NULL_W in *. lia. }
destruct FC1 as [E1 | E1].
+
if_rw E1 true. fold_mkR. evt_done5.
lazymatch type of INV3 with context [[(_, [CB 32 ?ja; _; CB 16 ?jb; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (arr_elem0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ja jb); [exact HL1 | | exact FS' | exact FR'] end.
eapply ser_memA_weaken_e; [| exact INV3]. lia.
+
if_rw E1 false. step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x23480 1 LIT_SPACE) with (F := F) (e := 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV3 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A4 m4 md4 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 INV4 FS4 FR4.
clear INV INV3 HP MI3 WM MU CHm POST NODE SH5.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (wmono_refl asegs m4) as WM.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU.
stash INV4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. fold_mkR. evt_done5. unstash INV4.
lazymatch type of INV4 with context [[(_, [CB 32 ?ja; _; CB 16 ?jb; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (arr_elem0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ja jb); [exact HL1 | exact INV4 | exact FS4 | exact FR4] end.
Qed.

End Arr.

Section Top.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Theorem ser_arrA : forall kids, (forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s') -> ser_specA HIx ASER_ARR (Sarr kids).
Proof.
intros kids KIDS. unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (a & ABS & ps & KBS & EREST & NODE & AL & L1 & L2 & KOK).
pose proof AL as (arr & size & junk & EABS & _). subst ABS.
subst a0 a1 a2 a3 tp REST.
cbn [app] in JTX. rewrite jtx_arr_eq in JTX. cbn [snd] in JTX. change (48 =? 48) with true in JTX. change (32 =? 32) with true in JTX. cbn [andb] in JTX.
pose proof NODE as NODE0. pose proof JHX as JHX0. pose proof HP as HP00. pose proof PB as PB00.
assert (LOS0 : lo <= bv_unsigned sp - 160 - 4096 - 112) by (unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS; rewrite sdepth_arr in LOS; pose proof (kdepth_nonneg kids); lia).
stash NODE0. stash JHX0. stash AL. stash KOK. stash LOS. stash HP00. stash PB00.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold ASER_ARR. unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 160%nat ST.
do 14 step. do 3 step. do 3 step. step. do 4 step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap w A FRS (bv_unsigned sp + -160) [(bv_unsigned sp + -160, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw3 : 24 <= w) by (eapply (jtxk_arr_acc (fun _ => True)); [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
evt_done5.
eapply (ser_litA HIx sp gp m md LB LM FRS B pb lo bpos cap w LO HT CAP TXT NEED OBL_REALLOC_NF 0x23800 1 LIT_LBRACK) with (F := F) (e := 0);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV1 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
unstash NODE0. unstash JHX0. unstash AL. unstash KOK. unstash LOS.
lazymatch type of INV3 with context [[(_, [CB 56 ?jj; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (arr_startA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo p rc pb0 lv fl a arr size bpos cap w
ps KBS kids T Y R KIDS FL Hlv Hlvd LO LOS SPA HT RA CAP TXT NEED JHX0 FRSN INCL NODE0 AL KOK JTX K
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jj); [exact INV3 | exact FS3 | exact FR3] end.
Qed.
End Top.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB QpNt Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Ql4f.Mq2 Qwm6.Mq1 Q228.Mq5.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 128 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ADBL_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 9 lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation dbl_invx := (dbl_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr).

Lemma dbl_epiA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x24 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (e len : Z) (bufb : list byte),
dbl_invx 0 A e bufb m md -> fsaved F F' -> (frm0 fc -> frm0 fc') -> 0 <= e <= 9 ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7 (wz Fr) x19 x20 x21 x22 (wz len) x24 (wz (Fr / 8 + 2147450880)) (wz Fr) x27 t3 t4 t5 t6)
F' (wz 0x9d59c) fc' None m (seg_rom asegs)).
Proof.
intros until bufb. intros INV FS FR He.
destruct INV as (LOCc & j8 & jr & t8 & HLOC & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold dblCH in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, SAV, FFx, SHx.
unfold dblSaved in SAV. unfold dblFF in FFx. unfold dblSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_2 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_2 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_2 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 32 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
stash LOC. stash PBUF. stash HFal. stash Hq32.
remember (Fr / 8 + 2147450880) as sh eqn:Esh. stash Esh.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr, Fr + 248); (sh, sh + 32)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. do 16 stepz.
step. step. stepz.
step. if_falsex.
step. do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
match goal with H : mem_inv asegs mX |- _ => rename H into MIX end.
unstash Esh.
assert (HPX : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 2) :: FRS) B mX md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MIX].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 2. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. rewrite <- Esh. lia. }
assert (SUBX : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 2 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
assert (HPRX : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUBX ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. rewrite <- Esh. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
stash Esh.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPX | exact INF | rewrite fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m7 md7 A7 VM7 HP7 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP7. rewrite Z.eqb_refl in HP7.
assert (MUr : munch [(fp, fp + 1)] mX m7).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs mX m7) by exact Hwv.
assert (MI7 : mem_inv asegs m7).
{ intros y b Hb0. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb0. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
assert (FPpb : ~ (pb <= fp < pb + PB_SZ)) by (intros Hin; apply FPnc; right; right; exists (pb, PB_SZ); split; [exact INpbX | exact Hin]).
assert (FPbuf : ~ (buf <= fp < buf + cap)) by (intros Hin; apply FPnc; right; right; exists (buf, cap); split; [exact INbufX | exact Hin]).
unfold alloc_ceiling in FPlow.
unstash LOC. unstash PBUF. unstash Esh.
assert (HLOCz : Z.of_nat (cells_size LOCc) = 24 + d) by (rewrite HLOC; lia).
assert (TRf : forall a cs, rw_cells asegs m a cs -> (a + Z.of_nat (cells_size cs) <= fp \/ fp + 1 <= a) ->
(a + Z.of_nat (cells_size cs) <= Fr \/ Fr + 248 <= a) -> (a + Z.of_nat (cells_size cs) <= sh \/ sh + 32 <= a) -> rw_cells asegs m7 a cs).
{ intros a cs H A1 A2 A3. eapply (rw_cells_transport asegs _ mX m7); [| exact MUr | exact WMr | cbn [disjoint_from]; split; [exact A1 | exact I]].
eapply (rw_cells_transport asegs _ m mX); [exact H | exact MU | exact WM |]. cbn [disjoint_from]. split; [exact A2 | split; [exact A3 | exact I]]. }
assert (LOC7 : rw_cells asegs m7 q LOCc) by (apply TRf; [exact LOC | rewrite HLOCz; lia | rewrite HLOCz; lia | rewrite HLOCz; lia]).
assert (PBUF7 : rw_cells asegs m7 buf [CB (Z.to_nat cap) content]) by (apply TRf; [exact PBUF | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]).
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in SAV; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in ERR; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_ERRNO, A_TP in *; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in PBS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] mX m7) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
reenterA asegs A4L HIx asegs_wx HP7.
step. step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m7, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS | exact FR]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM7]|].
split.
{ pose proof (stk_release asegs m7 lo q _ ST LOC7 ltac:(lia)) as S1. rewrite HLOCz in S1.
replace (q + (24 + d)) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m7 lo (bv_unsigned sp + -104) _ S1 SAV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S3 by lia. exact S3. }
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPRX|].
exact (pres_fp HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) fp HPX SUBX ltac:(unfold alloc_ceiling; lia) FPnc FPfr Hoff Hwv). }
split; [exact ERR|]. split; [exact HP7|].
split; [split; [exact Hbp|]; split; [exact Hcap|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF7]|].
split; [lia|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.
End Dbl.
End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Ql4f.Mq2 Qwm6.Mq1 Q228.Mq5.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 128 - d.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ADBL_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.

Notation dbl_invx := (dbl_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr).

Definition dbl_apart (a k : Z) : Prop :=
(a + k <= lo \/ q <= a) /\ (a + k <= Fr \/ Fr + 248 <= a) /\ (a + k <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 32 <= a).
Definition dbl_privW (iv : Z * Z) : Prop :=
(lo <= fst iv /\ snd iv <= q) \/ (Fr <= fst iv /\ snd iv <= Fr + 248) \/ (Fr / 8 + 2147450880 <= fst iv /\ snd iv <= Fr / 8 + 2147450880 + 32).
Lemma dbl_apart_disjoint : forall W a k, Forall dbl_privW W -> dbl_apart a k -> disjoint_from W a k.
Proof.
intros W a k HW (H1 & H2 & H3). induction HW as [|[l h] W Hiv _ IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
unfold dbl_privW in Hiv. cbn [fst snd] in Hiv. lia.
Qed.

Lemma dbl_inv_privA : forall v v' (A : ASA A4L HIx) e m m' md W bufb j8' bufb' jr' t8',
dbl_invx v A e bufb m md ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall dbl_privW W ->
rw_cells asegs m' Fr (dblFF j8' bufb' jr') -> rw_cells asegs m' (Fr / 8 + 2147450880) (dblSH v' t8') -> stk asegs m' lo q ->
dbl_invx v' A e bufb' m' md.
Proof.
intros until t8'. intros (LOCc & j8 & jr & t8 & HLOC & INV) MU WM MI' HW FF' SH' ST'.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_2 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (_ & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_2 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_2 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 32 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
assert (HLOCz : Z.of_nat (cells_size LOCc) = 24 + d) by (rewrite HLOC; destruct Hd; lia).
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (TR : forall a cs, rw_cells asegs m a cs -> dbl_apart a (Z.of_nat (cells_size cs)) -> rw_cells asegs m' a cs).
{ intros a cs H AP. eapply (rw_cells_transport asegs W m m'); [exact H | exact MU | exact WM | apply dbl_apart_disjoint; [exact HW | exact AP]]. }
exists LOCc, j8', jr', t8'. split; [exact HLOC|]. exists buf, cap, bpos, content, errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold dbl_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. left. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. lia. }
split.
{ destruct PB as (P1 & P2 & P3 & PBS & PBUF). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
split; [apply TR; [exact PBS | unfold dbl_apart; cbn [cells_size csize Nat.add]; lia]
| apply TR; [exact PBUF | unfold dbl_apart; cbn [cells_size csize Nat.add]; lia]]. }
unfold dblCH in CHm |- *.
apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHm as [C2 _].
cbn [fst snd] in C1, C2.
split.
{ constructor; [cbn [fst snd]; apply TR; [exact C1 | unfold dbl_apart; rewrite HLOCz; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C2 | unfold dbl_apart, dblSaved; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; exact FF'|].
constructor; [cbn [fst snd]; exact SH' | constructor]. }
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 2 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold dblFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_2; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 2); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, dblSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 2) with 32; unfold A_SB; lia]|].
constructor. }
split; [exact FSUB|].
split; [apply TR; [exact ERR | unfold dbl_apart, A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia]|].
split; [exact ST'|].
split.
{ eapply heap_pres_trans; [exact HPR|].
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 2 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB1 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold dbl_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. lia. }
split; [exact VM|]. split; [exact Hb|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.
End Dbl.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuER QarM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH Q0Ek.
Import Q7UD Qhd4 Qwm6.Mq0 QgHv.Mq0 Q9O6.Mq2 QlKV.Mq6 QuER QarM.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Ser.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPA A4L HIx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_LD : isnprintf_ld_stmt PFRT PFLO.
Hypothesis SNP_LU : isnprintf_lu_stmt PFRT PFLO.

Theorem ser_intA : ser_specA HIx ASER_INT Sint.
Proof.
apply ser_specA_of_al.
- exact (ser_intA_0 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_LD SNP_LU).
- exact (ser_intA_16 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_LD SNP_LU).
Qed.
End Ser.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QUrr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QnCn.Mq0.
Import QbFI.  Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4 Q4v2 QgHv Q1Y6 QsKa.Mqf QUrr. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 Q228.Mqc. Import Qwm6.Mq1. Import QnPO.Mq4 Q228.Mqe.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Ltac post_callS segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
rewrite ?unsigned_lit in MUc by lia; try rewrite ?unsigned_lit in PO by lia;
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "callS" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callS segs m ]
end.

Ltac if_rw E b :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (rewrite E; vm_compute; reflexivity)
end; cbv iota.

Lemma land1_cases : forall fl, 0 <= fl -> Z.land fl 1 = 0 \/ Z.land fl 1 = 1.
Proof.
intros fl H. change 1 with (Z.ones 1) at 1. change 1 with (Z.ones 1) at 2. rewrite !Z.land_ones by lia.
change (2^1) with 2. pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia.
Qed.
Lemma land58_bit : forall fl b, Z.land fl 58 = 0 -> Z.land 58 b = b -> Z.land fl b = 0.
Proof. intros fl b H Hb. rewrite <- Hb. rewrite Z.land_assoc, H. reflexivity. Qed.
Lemma land3_of_58 : forall fl, Z.land fl 58 = 0 -> Z.land fl 3 = Z.land fl 1.
Proof.
intros fl H. change 3 with (Z.lor 1 2). rewrite Z.land_lor_distr_r. rewrite (land58_bit fl 2 H eq_refl). apply Z.lor_0_r.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Arr.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo p rc pb0 lv fl a arr size bpos0 cap0 w : Z).
Variables (ps : list Z) (KBS : list (list blk)) (kids : list (option jshape)) (T : TSet) (Y R : list blk).
Let usp := bv_unsigned sp.
Hypothesis KIDS : forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s'.
Hypothesis FL : aflags_ok fl.
Hypothesis Hlv : 0 <= lv.
Hypothesis Hlvd : lv + sdepth (Sarr kids) <= 1000.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ser_budgetA (Sarr kids).
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + w < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 w <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis FRSN : Z.of_nat (length FRS) + 1 < 4096.
Hypothesis INCL : incl ((p, 48) :: [(a, AL_SZ); (arr, 8 * size)] ++ concat KBS) LB.
Hypothesis NODE0 : rw_cells asegs m0 p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string A4F) pb0 0 0 ++ [C8 (wz a)]).
Hypothesis AL0 : alist asegs A4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps.
Hypothesis KOK : kids_okp asegs A4F m0 kids ps KBS.
Hypothesis JTX : jtxk_arr kids (concat KBS ++ Y) 24 = Some (w, R).
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation ser_memx := (ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w).
Let LEN := Z.of_nat (length ps).
Definition savedR : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma facts :
0 <= usp < 2^64 /\ In (p, 48) LB /\ 0 <= fl < 2^31 /\
Z.land fl 2 = 0 /\ Z.land fl 8 = 0 /\ Z.land fl 32 = 0 /\ Z.land fl 3 = Z.land fl 1 /\ (Z.land fl 1 = 0 \/ Z.land fl 1 = 1) /\
0 <= kdepth kids /\ lo <= usp - 192 - 256 * kdepth kids - 16384 - 64 /\
LEN = Z.of_nat (length kids) /\ length KBS = length kids /\ LEN <= size /\ 1 <= size /\ 8 * size < 2^64.
Proof.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (INp : In (p, 48) LB) by (apply INCL; left; reflexivity).
destruct FL as [Rfl FL58].
pose proof (kdepth_nonneg kids) as KD. unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS. rewrite sdepth_arr in LOS.
destruct (kids_okp_len _ _ _ _ _ _ KOK) as [L1 L2].
destruct AL0 as (arr' & size' & junk & E & Hps & Hsz & _). injection E as _ E2. assert (size' = size) by lia. subst size'.
split; [exact SPR|]. split; [exact INp|]. split; [exact Rfl|].
split; [exact (land58_bit fl 2 FL58 eq_refl)|]. split; [exact (land58_bit fl 8 FL58 eq_refl)|]. split; [exact (land58_bit fl 32 FL58 eq_refl)|].
split; [exact (land3_of_58 fl FL58)|]. split; [apply land1_cases; lia|].
split; [exact KD|]. split; [unfold usp in *; lia|].
unfold LEN. repeat split; try assumption; lia.
Qed.

Lemma factsM : forall A FA CH e m md, ser_memx A FRS FA CH e m md ->
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
rw_cells asegs m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string A4F) pb0 0 0 ++ [C8 (wz a)]) /\
ro_cells asegs m (p / 8 + 2147450885) [C1 (Z_to_bv 8 0)] /\
alist asegs A4F m [(a, AL_SZ); (arr, 8 * size)] a ps /\
kids_okp asegs A4F m kids ps KBS.
Proof.
intros A FA CH e m md (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & INp & _).
assert (INp' : In (p, 48) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INp')) as (_ & Hpal & Hplo & Hphi & _).
assert (AG : agree_on asegs LB m0 m).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app. left. exact Hb. }
split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]. }
split. { pose proof (blk_granS HIx _ _ _ _ _ _ _ p 48 5 HP INp' ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia. exact SH5. }
split. { eapply (alist_agree asegs A4F); [exact AL0 | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. left. exact Hb. }
eapply (kids_okp_agree asegs A4F); [exact KOK | exact AG |]. intros b Hb. apply INCL. right. apply in_or_app. right. exact Hb.
Qed.

Lemma al_lengthE : forall (x1 x4 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' A FA CH e m md,
ser_memx A FRS FA CH e m md -> lo <= FA - 16 -> FA <= usp ->
evt asegs (array_list_length_A_post x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' a3 a4 ps m lo)
(MS (mkR x1 (wz FA) gp x4 t0 t1 t2 x8 x9 (wz a) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz array_list_length_A_entry) fc' None m (seg_rom asegs)).
Proof.
intros until md. intros INV LOF FAU.
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & AL & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INa : In (a, 32) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; left; reflexivity).
assert (INr : In (arr, 8 * size) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INa)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INr)) as (_ & Hral & Hrlo & Hrhi & _).
shadow_inA A4L HIx HP INa SHa.
pose proof alloc_ceiling_range as ACR.
assert (UF : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
eapply (array_list_length_A x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' (wz a) a1 a2 a3 a4 m lo _ a arr size ps).
- unfold small_pre. rewrite UF. split; [exact MI|]. split; [exact ST|]. split; [lia|]. split; [exact LO|]. split; [exact GOT|]. split; [exact CELL|].
a4l_goal. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- exact AL.
- reflexivity.
- unfold al_blkA. repeat split; try lia; clear - Haal Hral; Z.div_mod_to_equations; lia.
- exact SHa.
Qed.

Lemma al_get_idxE : forall (x1 x4 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' A FA CH e m md i,
ser_memx A FRS FA CH e m md -> lo <= FA - 16 -> FA <= usp -> 0 <= i < 2^64 ->
evt asegs (array_list_get_idx_A_post x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' ps i m lo)
(MS (mkR x1 (wz FA) gp x4 t0 t1 t2 x8 x9 (wz a) (wz i) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz array_list_get_idx_A_entry) fc' None m (seg_rom asegs)).
Proof.
intros until i. intros INV LOF FAU Hi.
pose proof (factsM _ _ _ _ _ _ INV) as (_ & _ & _ & _ & _ & AL & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & _).
pose proof facts as (SPR & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INa : In (a, 32) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; left; reflexivity).
assert (INr : In (arr, 8 * size) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; right; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a 32 HP ltac:(apply in_or_app; left; exact INa)) as (_ & Haal & Halo & Hahi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP ltac:(apply in_or_app; left; exact INr)) as (_ & Hral & Hrlo & Hrhi & _).
shadow_inA A4L HIx HP INa SHa.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr) as SHr. unfold shad in SHr. cbn [hl_sb hl_segs hla_base A4L A4H] in SHr.
pose proof alloc_ceiling_range as ACR.
assert (UF : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
eapply (array_list_get_idx_A x1 (wz FA) gp x4 t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F' fc' (wz a) (wz i) a2 a3 a4 m lo _ a arr size ps i).
- unfold small_pre. rewrite UF. split; [exact MI|]. split; [exact ST|]. split; [lia|]. split; [exact LO|]. split; [exact GOT|]. split; [exact CELL|].
a4l_goal. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- exact AL.
- reflexivity.
- reflexivity.
- exact Hi.
- unfold al_blkA. repeat split; try lia; clear - Haal Hral; Z.div_mod_to_equations; lia.
- exact SHa.
- exact SHr.
Qed.

Lemma arr_failA :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -192) [(usp + -192, PRE ++ savedR)] e m md -> cells_size PRE = 88%nat ->
0 <= e <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9ceec) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 88) with 88 in SAVc.
replace (usp + -192 + 88) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -192) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 88) with 88 in S1.
replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS' | intros _; exact FR']|].
split; [exact VM|]. split; [exact STU|]. split; [exact HPR|]. split; [exact ERR|]. split; [exact HP|]. split; [exact PB|].
split; [lia|]. split; [exact Hcap|]. split; [exact HBB | exact HBD].
Qed.

Lemma arr_closeA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -192) [(usp + -192, PRE ++ savedR)] e m md -> cells_size PRE = 88%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x9d148) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & _).
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hbp & Hcap & HBB & HBD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm.
apply (proj1 (rw_cells_app asegs _ _ PRE _)) in CHm. destruct CHm as [PREc SAVc]. rewrite HPRE in SAVc. change (Z.of_nat 88) with 88 in SAVc.
replace (usp + -192 + 88) with (usp + -104) in SAVc by lia.
unfold savedR in SAVc. unfold usp in *. unfold_consts.
pose proof PB as (Hbp0 & Hcap0 & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. rewrite (unsigned_lit fl) by lia. rewrite FL3.
step. step.
assert (STU : stk asegs m lo (bv_unsigned sp)).
{ pose proof (stk_release asegs m lo (bv_unsigned sp + -192) _ ST PREc ltac:(lia)) as S1. rewrite HPRE in S1. change (Z.of_nat 88) with 88 in S1.
replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m lo (bv_unsigned sp + -104) _ S1 SAVc ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S2 by lia. exact S2. }
assert (INVU : ser_memx A FRS (bv_unsigned sp) [] e m md).
{ exists buf, cap, bpos, content, errv, B.
split; [exact HP|]. split; [exact PB|]. split; [constructor|]. split; [constructor|]. split; [exact FSUB|].
split; [exact ERR|]. split; [exact STU|]. split; [exact HPR|]. split; [exact VM|].
split; [exact Hbp|]. split; [exact Hcap|]. split; [exact HBB | exact HBD]. }
assert (TAILK : forall (lit k : Z) (bs : list byte) (t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
ro_bytes_b asegs lit bs = true -> Z.of_nat (length bs) = k -> src_ro_chk lit k = true -> 0 < k <= 2 -> 0 <= lit -> lit + k < 2^32 ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra sp gp (Z_to_bv 64 6444320) t0_ t1_ t2_ s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 lit) (Z_to_bv 64 k) a3_ a4_ a5_ a6_ a7_
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F' (Z_to_bv 64 0x9b4fc) fc' None m (seg_rom asegs))).
{ intros lit k bs t0_ t1_ t2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ RB BL CHK Hk Hl Hlk.
evt_done5.
rewrite <- (Z_to_bv_bv_unsigned ra) at 1. rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF lit k bs RB BL CHK ltac:(lia) Hl Hlk) with (F := F) (e := e);
[ exact INVU | exact He | lia | lia | exact SPA | lia | lia | reflexivity | word_range ra RAR; lia | exact RA | exact FS' | exact FR' | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & _ & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply K. unfold ser_postA.
exists m2, a0', errv2, buf2, cap2, bpos2, content2, B2.
rewrite !Z_to_bv_bv_unsigned.
assert (ERA : ra = ret_pc ra).
{ word_range ra RAR. rewrite <- (Z_to_bv_bv_unsigned ra) at 2. rewrite ret_pc_even by (try exact RA; lia). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [unfold ret_statew; do 16 eexists; split; [rewrite <- ERA; reflexivity|]; split; [exact FS2 | intros _; exact FR2]|].
split; [exact VM2|]. split; [exact ST2|]. split; [exact HPR2|]. split; [exact ERR2|]. split; [exact HP2|]. split; [exact PB2|].
split; [lia|]. split; [exact Hc2|]. split; [exact HB2 | exact HD2]. }
destruct FC1 as [E1 | E1]; rewrite E1.
-
if_lit. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x238a0 1 LIT_RBRACK); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
-
if_lit. step. step. step. step. step. do 13 step. step. step. fold_mkR.
eapply (TAILK 0x23880 2 LIT_SP_RBRACK); [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia].
Qed.

Lemma arr_exitA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x26 x27 t3 t4 t5 t6 : word) F' fc' m md A (PRE : list cell) e,
ser_memx A FRS (usp + -192) [(usp + -192, PRE ++ savedR)] e m md -> cells_size PRE = 88%nat ->
0 <= e -> e + 2 <= w ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) x9 a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 x21 x22 x23 x24 (wz 0) x26 x27 t3 t4 t5 t6) F' (wz 0x9d0fc) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV HPRE He Hew FS' FR'.
pose proof facts as (SPR & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
stash INV.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
evt_done5. unstash INV.
eapply arr_closeA; [exact INV | exact HPRE | exact He | exact Hew | exact FS' | exact FR'].
Qed.

Lemma kid_callA : forall (pc0 retpc : Z) (s' : jshape) (v pbk : Z) (RESTk : list blk)
(x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x20 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) F' fc' A CH e m md,
(pc0 = 0x9cec0 /\ retpc = 0x9cee8) \/ (pc0 = 0x9d070 /\ retpc = 0x9d098) ->
ser_memx A FRS (usp + -192) CH e m md -> jnode asegs A4F s' m RESTk v 1 pbk -> incl RESTk LB ->
(AJ5 A4L HIx A T md (MS (mkR (wz retpc) (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 2147450880) (wz v) (wz pb) (wz (lv + 1)) (wz fl) (wz (afn_of s')) a5 a6 a7
(wz fl) x19 x20 (wz (lv + 1)) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz (afn_of s')) fc' None m (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 2147450880) (wz v) a1 a2 a3 a4 a5 a6 a7
(wz fl) x19 x20 (wz (lv + 1)) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz pc0) fc' None m (seg_rom asegs)).
Proof.
intros until md. intros PCS INV JN INCLk KONT.
pose proof facts as (SPR & _ & Rfl & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & HDR).
assert (INv : In (v, n) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCLk; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP ltac:(apply in_or_app; left; exact INv)) as (_ & Hval & Hvlo & Hvhi & _).
pose proof (blk_granS HIx _ _ _ _ _ _ _ v n 1 HP INv ltac:(lia) ltac:(lia)) as SHv.
replace (v / 8 + 2147450880 + 1) with (v / 8 + 2147450881) in SHv by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] cs)) in HDR. destruct HDR as [HDR _].
clear INV JN.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
a4l.
unfold afn_of in KONT.
destruct PCS as [[-> ->] | [-> ->]].
- reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
destruct s' as [|[|]| |[|]|kids'|kids'];
(lazymatch type of HDR with context [fn_ofF A4F ?s] => let fv := eval vm_compute in (fn_ofF A4F s) in change (fn_ofF A4F s) with fv in HDR, KONT end);
step; do 3 step; step; fold_mkR; evt_done5; exact KONT.
- reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
destruct s' as [|[|]| |[|]|kids'|kids'];
(lazymatch type of HDR with context [fn_ofF A4F ?s] => let fv := eval vm_compute in (fn_ofF A4F s) in change (fn_ofF A4F s) with fv in HDR, KONT end);
step; do 3 step; step; fold_mkR; evt_done5; exact KONT.
Qed.

Definition arrFR (j0 : list byte) : list cell :=
[CB 8 j0; C8 (wz 0x23540); C8 (wz 0x235a0); C8 (wz 0x234e0); C8 (wz LEN); C8 (wz (2 * (lv + 1))); C8 (wz (lv + 1073741825)); C8 (wz lv);
C8 (wz 0); C8 (wz (Z.land fl 1)); C8 (wz 0)] ++ savedR.

Definition st_loop (pc i : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (p + 40)) (wz 0) (wz (lv + 1)) (wz 0x234c0) (wz i) (wz 0x234a0) (wz 0) (wz 0x233c0) (wz (p / 8 + 2147450885)) t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom asegs).

Definition loopK (bound : Z) : Prop :=
forall (i acc : Z) (j0 : list byte) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound ->
pbtail P -> jtxk_arr (skipn (Z.to_nat i) kids) (P ++ concat (skipn (Z.to_nat i) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, arrFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9cfd0 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).

Lemma arr_nextA : forall bound, loopK bound ->
forall (i acc : Z) (j0 : list byte) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat (i + 1)) kids) (P ++ concat (skipn (Z.to_nat (i + 1)) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, arrFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9d0ec i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & AL & KOKm).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold arrFR, savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU.
stash INV. stash AL. stash KOKm.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step. fold_mkR.
unstash INV.
callS (al_lengthE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -192) _ (acc - 2) m md INV ltac:(lia) ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, arrFR j0)] (acc - 2) m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
fold LEN.
step.
destruct (Z.ltb_spec (i + 1) LEN) as [LT | GE].
- if_truex. fold_mkR. evt_done5.
eapply (IH (i + 1) acc j0 P); [lia | lia | exact HP0 | exact JT | exact Hacc | exact INV2 | exact FS' | exact FR'].
- if_falsex. fold_mkR. evt_done5.
assert (Ew : w = acc) by (eapply (jtxk_arr_done kids (Z.to_nat (i + 1))); [lia | exact JT]).
eapply arr_exitA with (e := acc - 2)
(PRE := [CB 8 j0; C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x235a0); C8 (Z_to_bv 64 0x234e0); C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.land fl 1)); C8 (Z_to_bv 64 0)]);
[exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'].
Qed.

Lemma arr_ret_kidA : forall bound, loopK bound ->
forall (i acc : Z) (j0 : list byte) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat (i + 1)) kids) (P ++ concat (skipn (Z.to_nat (i + 1)) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc -> acc <= w ->
ser_memx A FRS (usp + -192) [(usp + -192, arrFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9d098 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc Haw INV FS' FR'.
pose proof facts as (SPR & _).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & _ & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_cases NEG; fold_mkR.
- evt_done5. unstash INV.
eapply arr_failA with (e := acc - 2)
(PRE := [CB 8 j0; C8 (Z_to_bv 64 0x23540); C8 (Z_to_bv 64 0x235a0); C8 (Z_to_bv 64 0x234e0); C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.land fl 1)); C8 (Z_to_bv 64 0)]);
[exact INV | reflexivity | lia | exact FS' | exact FR'].
- step. step. if_lit. fold_mkR.
evt_done5. unstash INV.
eapply (arr_nextA bound IH i acc j0 P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
Qed.
Lemma arr_ret_nullA : forall bound, loopK bound ->
forall (i acc : Z) (j0 : list byte) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat (i + 1)) kids) (P ++ concat (skipn (Z.to_nat (i + 1)) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, arrFR j0)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9d0e4 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & _).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & _ & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit. fold_mkR.
evt_done5. unstash INV.
eapply (arr_nextA bound IH i acc j0 P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | exact INV | exact FS' | exact FR'].
Qed.

Lemma arr_elemA : forall bound, loopK bound ->
forall (i acc : Z) (j0 : list byte) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m md A,
1 <= i < LEN -> LEN - i <= bound + 1 ->
pbtail P -> jtxk_arr (skipn (Z.to_nat i) kids) (P ++ concat (skipn (Z.to_nat i) KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, arrFR j0)] acc m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md (st_loop 0x9d050 i x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m).
Proof.
intros bound IH. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold arrFR, savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
step. step. step. fold_mkR.
unstash INV.
callS (al_get_idxE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -192) _ acc m md i INV ltac:(lia) ltac:(lia) ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, arrFR j0)] acc m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
fold LEN. replace (i <? LEN) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (factsM _ _ _ _ _ _ INV2) as (_ & _ & _ & _ & _ & _ & KOK2).
pose proof (al_nth_in ps i ltac:(fold LEN; lia)) as NTHp.
destruct (nth_error kids (Z.to_nat i)) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
destruct k as [s'|].
-
destruct (kids_okp_nth asegs A4F _ _ _ _ _ _ KOK2 NTHk) as (v & bs & Hv & Hbs & _).
rewrite NTHp in Hv. injection Hv as Hv.
destruct (jtxk_arr_step_some asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ _ KOK2 NTHk NTHp Hbs HP0 JT) as (Hvnz & JV & pbk & PBSk & RESTk & wi & P' & Ebs & JN & Hwi & Haw & JTXk & HP' & JT').
rewrite Hv in *. clear Hv.
assert (INk : In (Some s') kids) by (eapply nth_error_In; exact NTHk).
assert (INCLk : incl RESTk LB).
{ intros bq Hbq. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | rewrite Ebs; apply in_or_app; left; exact Hbq]. }
pose proof (kdepth_in _ _ INk) as KDk.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & _).
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP2 ltac:(apply in_or_app; left; right; right; apply INCLk; rewrite ER; left; reflexivity)) as (_ & Hval & Hvlo & Hvhi & _).
unfold_consts.
step. if_falsex.
step. step. ubsan_align Hval. fold_mkR.
evt_done5.
eapply (kid_callA 0x9d070 0x9d098 s' v pbk RESTk); [right; split; reflexivity | exact INV2 | exact JN | exact INCLk |].
eapply (ser_childA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 (afn_of s') s' (KIDS s' INk)) with (F := F) (e := acc);
[ exact INV2 | exact JN | exact INCLk | exact JTXk | lia | lia | exact FL | lia | rewrite sdepth_arr in Hlvd; lia | exact FRSN
| unfold ser_budgetA, ASER_LEVEL, ASER_LEAF; lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in JT' by lia.
eapply (arr_ret_kidA bound IH i (acc + (2 + wi)) j0 P'); [lia | lia | exact HP' | exact JT' | lia | lia | | exact FS3 | exact FR3].
replace (acc + (2 + wi) - 2) with (acc + wi) by lia. exact INV3.
-
destruct (jtxk_arr_step_none asegs A4F _ _ _ _ _ _ _ _ _ _ KOK2 NTHk HP0 JT) as (Hv0 & Haw & JT').
rewrite NTHp in Hv0. injection Hv0 as Hv0. rewrite Hv0.
step. if_lit. step. step. step. if_lit. step. step. step. fold_mkR.
evt_done5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x233c0 4 LIT_NULL) with (F := F) (e := acc);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV2 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in JT' by lia.
eapply (arr_ret_nullA bound IH i (acc + 6) j0 P); [lia | lia | exact HP0 | exact JT' | lia | | exact FS3 | exact FR3].
replace (acc + 6 - 2) with (acc + 4) by lia. exact INV3.
Qed.

Lemma arr_iter : forall bound, loopK bound -> loopK (bound + 1).
Proof.
intros bound IH. unfold loopK. intros until A. intros Hi Hb HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
assert (Haw : acc <= w) by (eapply (jtxk_arr_acc (fun _ => True)); [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JT]).
assert (Haw2 : acc + 2 <= w).
{ destruct (nth_error kids (Z.to_nat i)) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
rewrite (skipn_nth_cons _ _ _ NTHk) in JT. cbn [jtxk_arr] in JT. destruct k as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JT). lia.
- pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JT). unfold NULL_W in *. lia. }
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_loop. unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl (@nil (Z * Z)) m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. fold_mkR.
evt_done5. unstash INV.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234a0 1 LIT_COMMA) with (F := F) (e := acc - 2);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
clear INV HP MI WM MU.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _ & CHm & _ & _ & _ & ST3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold arrFR, savedR in CHm. cbn [app] in CHm.
pose proof (wmono_refl asegs m3) as WM.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU.
stash INV3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. if_lit.
step. step.
destruct FC1 as [E1 | E1].
-
if_rw E1 true. step. if_lit. fold_mkR. evt_done5. unstash INV3.
eapply (arr_elemA bound IH i acc j0 P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
-
if_rw E1 false. step. step. step. step. fold_mkR.
evt_done5. unstash INV3.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234e0 1 LIT_SPACE) with (F := F) (e := acc - 2 + 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV3 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros A4 m4 md4 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 INV4 FS4 FR4.
clear INV3 HP3 MI3 WM MU CHm ST3.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (wmono_refl asegs m4) as WM.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU.
stash INV4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. if_lit. fold_mkR. evt_done5. unstash INV4.
eapply (arr_elemA bound IH i acc j0 P); [exact Hi | exact Hb | exact HP0 | exact JT | exact Hacc | | exact FS4 | exact FR4].
replace (acc - 2 + 1 + 1) with acc in INV4 by lia. exact INV4.
Qed.

Lemma arr_loop : forall n, loopK (Z.of_nat n).
Proof.
induction n as [|n IH].
- unfold loopK. intros. lia.
- replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. apply arr_iter. exact IH.
Qed.

Lemma arr_after0A :
forall (acc : Z) (P : list blk) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x26 t3 t4 t5 t6 : word) (j32 : list byte) F' fc' m md A,
1 <= LEN ->
pbtail P -> jtxk_arr (skipn 1 kids) (P ++ concat (skipn 1 KBS) ++ Y) acc = Some (w, R) -> 3 <= acc ->
ser_memx A FRS (usp + -192) [(usp + -192, [CB 32 j32; C8 (wz LEN); C8 (wz (2 * (lv + 1))); C8 (wz (lv + 1073741825)); C8 (wz lv); C8 (wz 0); C8 (wz (Z.land fl 1)); C8 (wz 0)] ++ savedR)] (acc - 2) m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (p + 40)) (wz 0) (wz (lv + 1)) x22 x23 x24 (wz 0) x26 (wz (p / 8 + 2147450885)) t3 t4 t5 t6)
F' (wz 0x9cf78) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros HL1 HP0 JT Hacc INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
step. step. fold_mkR.
unstash INV.
callS (al_lengthE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -192) _ (acc - 2) m md INV ltac:(lia) ltac:(lia)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
fold LEN.
step. step.
destruct (Z.ltb_spec LEN 2) as [LT | GE].
-
if_truex. fold_mkR.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -192)
[(bv_unsigned sp + -192, [CB 32 j32; C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.land fl 1)); C8 (Z_to_bv 64 0)] ++ savedR)] (acc - 2) m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI0 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
assert (Ew : w = acc) by (eapply (jtxk_arr_done kids 1%nat); [lia | exact JT]).
eapply arr_exitA with (e := acc - 2); [exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'].
- if_falsex.
step. do 6 step.
step. step. stepz. step. step. stepz. step. stepz. step.
fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
lazymatch type of CHm with rw_cells _ _ _ (CB 8 ?jj :: _) =>
assert (INV3 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, arrFR jj)] (acc - 2) m3 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI3 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.
pose proof (arr_loop (Z.to_nat LEN)) as LK. unfold loopK, st_loop in LK.
lazymatch type of INV3 with context [arrFR ?jj] =>
eapply (LK 1 acc jj P); [lia | lia | exact HP0 | exact JT | exact Hacc | exact INV3 | exact FS' | exact FR'] end.
Qed.

Lemma arr_elem0A :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x26 t3 t4 t5 t6 : word) (j32 j64 : list byte) F' fc' m md A,
1 <= LEN ->
ser_memx A FRS (usp + -192) [(usp + -192, [CB 32 j32; C8 (wz LEN); C8 (wz (2 * (lv + 1))); C8 (wz (lv + 1073741825)); C8 (wz lv); CB 8 j64; C8 (wz (Z.land fl 1)); C8 (wz 0)] ++ savedR)] 2 m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz (p + 40)) (wz 0) (wz (lv + 1)) x22 x23 x24 (wz 0) x26 (wz (p / 8 + 2147450885)) t3 t4 t5 t6)
F' (wz 0x9ce98) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros HL1 INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_lit.
step. step. rewrite (unsigned_lit fl) by lia. rewrite FL32.
step. step. fold_mkR.
unstash INV.
callS (al_get_idxE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -192) _ 2 m md 0 INV ltac:(lia) ltac:(lia) ltac:(lia)).
fold LEN. replace (0 <? LEN) with true by (symmetry; apply Z.ltb_lt; lia).
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -192)
[(bv_unsigned sp + -192, [CB 32 j32; C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.land fl 1)); C8 (Z_to_bv 64 0)] ++ savedR)] 2 m2 md).
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI2 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
pose proof (factsM _ _ _ _ _ _ INV2) as (_ & _ & _ & _ & _ & _ & KOK2).
pose proof (al_nth_in ps 0 ltac:(fold LEN; lia)) as NTHp. change (Z.to_nat 0) with 0%nat in NTHp.
assert (JT0 : jtxk_arr (skipn 0 kids) ([] ++ concat (skipn 0 KBS) ++ Y) 24 = Some (w, R)) by exact JTX.
destruct (nth_error kids 0) as [k|] eqn:NTHk; [| apply nth_error_None in NTHk; lia].
destruct k as [s'|].
-
destruct (kids_okp_nth asegs A4F _ _ _ _ _ _ KOK2 NTHk) as (v & bs & Hv & Hbs & _).
rewrite NTHp in Hv. injection Hv as Hv.
destruct (jtxk_arr_step_some asegs A4F _ _ _ _ _ _ _ _ _ _ _ _ _ KOK2 NTHk NTHp Hbs pbtail_nil JT0) as (Hvnz & JV & pbk & PBSk & RESTk & wi & P' & Ebs & JN & Hwi & Haw & JTXk & HP' & JT').
rewrite Hv in *. clear Hv.
assert (INk : In (Some s') kids) by (eapply nth_error_In; exact NTHk).
assert (INCLk : incl RESTk LB).
{ intros bq Hbq. apply INCL. right. apply in_or_app. right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | rewrite Ebs; apply in_or_app; left; exact Hbq]. }
pose proof (kdepth_in _ _ INk) as KDk.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & _).
destruct (jnode_hdr asegs A4F _ _ _ _ _ _ JN) as (n & ty & udel & ud & cs & rest & ER & Hn & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v n HP2 ltac:(apply in_or_app; left; right; right; apply INCLk; rewrite ER; left; reflexivity)) as (_ & Hval & Hvlo & Hvhi & _).
unfold_consts.
step. if_falsex.
step. step. ubsan_align Hval. fold_mkR.
evt_done5.
eapply (kid_callA 0x9cec0 0x9cee8 s' v pbk RESTk); [left; split; reflexivity | exact INV2 | exact JN | exact INCLk |].
eapply (ser_childA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED JHEX0 (afn_of s') s' (KIDS s' INk)) with (F := F) (e := 2);
[ exact INV2 | exact JN | exact INCLk | exact JTXk | lia | lia | exact FL | lia | rewrite sdepth_arr in Hlvd; lia | exact FRSN
| unfold ser_budgetA, ASER_LEVEL, ASER_LEAF; lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
clear INV INV2 HP HP2 MI2 WM MU CHm POST NODE SH5.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
pose proof (wmono_refl asegs m3) as WM.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU.
stash INV3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. if_cases NEG; fold_mkR.
+ evt_done5. unstash INV3.
eapply (arr_after0A (24 + (2 + wi)) P'); [exact HL1 | exact HP' | exact JT' | lia | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
+ evt_done5. unstash INV3.
eapply arr_failA with (e := 2 + wi)
(PRE := [CB 32 j32; C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 (2 * (lv + 1))); C8 (Z_to_bv 64 (lv + 1073741825)); C8 (Z_to_bv 64 lv); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.land fl 1)); C8 (Z_to_bv 64 0)]);
[exact INV3 | reflexivity | lia | exact FS3 | exact FR3].
-
destruct (jtxk_arr_step_none asegs A4F _ _ _ _ _ _ _ _ _ _ KOK2 NTHk pbtail_nil JT0) as (Hv0 & Haw & JT').
rewrite NTHp in Hv0. injection Hv0 as Hv0. rewrite Hv0.
step. if_lit. step. if_lit. step. step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x233c0 4 LIT_NULL) with (F := F) (e := 2);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV2 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
eapply (arr_after0A (24 + 6) []); [exact HL1 | exact pbtail_nil | exact JT' | lia | | exact FS3 | exact FR3].
eapply ser_memA_weaken_e; [| exact INV3]. lia.
Qed.

Lemma arr_startA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (j88 : list byte) F' fc' m md A,
ser_memx A FRS (usp + -192) [(usp + -192, [CB 88 j88] ++ savedR)] 1 m md ->
fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz (usp + -192)) gp (wz A_TP) t0 t1 t2 (wz pb) (wz 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
(wz fl) (wz p) (wz lv) x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz 0x9cdb8) fc' None m (seg_rom asegs)).
Proof.
intros until A. intros INV FS' FR'.
pose proof facts as (SPR & INp & Rfl & FL2 & FL8 & FL32 & FL3 & FC1 & KD & LOS' & LENk & LKBS & LENsz & Hsz1 & Hsz2).
pose proof (factsM _ _ _ _ _ _ INV) as (Hp0 & Hph & Hp8 & NODE & SH5 & _ & _).
pose proof INV as (buf & cap & bpos & content & errv & B & HP & _ & CHm & _ & _ & _ & ST & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_inv in CHm. cbn [fst snd] in CHm. unfold savedR in CHm. cbn [app] in CHm.
unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (Hw3 : 24 <= w) by (eapply (jtxk_arr_acc (fun _ => True)); [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
assert (Hlv1 : lv <= 999) by (rewrite sdepth_arr in Hlvd; lia).
unfold usp in *. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU.
stash INV.
a4l. reenterA asegs A4L HIx asegs_wx HP.
assert (Hpal : p mod 16 = 0).
{ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; right; right; exact INp)) as (_ & Hpal & _). exact Hpal. }
step. if_falsex.
step. step. ubsan_align Hpal.
stepz.
step. asan_chkA.
step.
step. rewrite (unsigned_lit fl) by lia. rewrite FL2.
step. rewrite (unsigned_lit fl) by lia. rewrite FL8.
stepz.
step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
unstash INV.
lazymatch type of CHm with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, frc)] 1 m1 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI1 | | | | exact ST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
callS (al_lengthE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (bv_unsigned sp + -192) _ 1 m1 md INV1 ltac:(lia) ltac:(lia)).
fold LEN.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
destruct (Z.eq_dec LEN 0) as [L0 | LN0].
-
rewrite L0. if_lit. fold_mkR.
lazymatch type of CHm with rw_cells _ _ _ ?frc =>
assert (INV2 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, frc)] 1 m2 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI2 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
evt_done5.

lazymatch type of CHm with rw_cells _ _ _ ?frc =>
eapply arr_exitA with (e := 1) (PRE := firstn (length frc - 13) frc); [exact INV2 | reflexivity | lia | lia | exact FS' | exact FR'] end.
- if_falsex.
step.
step. norm_w32.
step.
step.
rewrite (v_slt_0 (Z_to_bv 64 (lv + 1)) (Z_to_bv 64 lv)) by (rewrite !signed_lit by lia; lia).
step.
step. norm_w32.
rewrite (Z.shiftl_mul_pow2 (lv + 1) 1) by lia. change (2^1) with 2. rewrite (swrap32_id ((lv + 1) * 2)) by lia. replace ((lv + 1) * 2) with (2 * (lv + 1)) by lia.
stepz.
step. norm_w32.
stepz.
step. rewrite (unsigned_lit fl) by lia.
stepz.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
lazymatch type of CHm with rw_cells _ _ _ ?frc =>
assert (INV3 : ser_memx A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, frc)] 1 m3 md) end.
{ eapply (ser_memA_stackW HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w HT); [exact INV | exact MU | exact WM | exact MI3 | | | | exact POST | lia].
- constructor; [cbn [fst snd]; split; lia | constructor].
- constructor; [exact CHm | constructor].
- constructor; [left; cbn [fst]; lia | constructor]. }
assert (HL1 : 1 <= LEN) by (unfold LEN in *; lia).
assert (Hw2 : 26 <= w).
{ destruct kids as [|k0 kids']; [cbn [length] in LENk; lia|]. clear - JTX. cbn [jtxk_arr] in JTX. destruct k0 as [s'|].
- destruct (jtx s' _) as [[wi R1]|] eqn:E; [|discriminate]. pose proof (jtx_nonneg _ _ _ _ E).
pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JTX). lia.
- pose proof (jtxk_arr_acc (fun _ => True) _ (fun s0' _ bs0 w0 r0 H0 => jtx_nonneg _ _ _ _ H0) _ _ _ _ JTX). unfold NULL_W in *. lia. }
destruct FC1 as [E1 | E1].
+
if_rw E1 true. step. if_lit. fold_mkR. evt_done5.
lazymatch type of INV3 with context [[(_, [CB 32 ?ja; _; _; _; _; CB 8 ?jb; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (arr_elem0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ja jb); [exact HL1 | | exact FS' | exact FR'] end.
eapply ser_memA_weaken_e; [| exact INV3]. lia.
+
if_rw E1 false. step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_litA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 w LO HT CAP0 TXT NEED OBL_REALLOC_NF 0x234e0 1 LIT_SPACE) with (F := F) (e := 1);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV3 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS' | exact FR' | ].
intros A4 m4 md4 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 INV4 FS4 FR4.
clear INV INV1 INV3 HP MI3 WM MU CHm POST NODE SH5.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (wmono_refl asegs m4) as WM.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU.
stash INV4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. if_lit. fold_mkR. evt_done5. unstash INV4.
lazymatch type of INV4 with context [[(_, [CB 32 ?ja; _; _; _; _; CB 8 ?jb; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (arr_elem0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ja jb); [exact HL1 | exact INV4 | exact FS4 | exact FR4] end.
Qed.

End Arr.

Section Top.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Theorem ser_arrA : forall kids, (forall s', In (Some s') kids -> ser_specA HIx (afn_of s') s') -> ser_specA HIx ASER_ARR (Sarr kids).
Proof.
intros kids KIDS. unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (a & ABS & ps & KBS & EREST & NODE & AL & L1 & L2 & KOK).
pose proof AL as (arr & size & junk & EABS & _). subst ABS.
subst a0 a1 a2 a3 tp REST.
cbn [app] in JTX. rewrite jtx_arr_eq in JTX. cbn [snd] in JTX. change (48 =? 48) with true in JTX. change (32 =? 32) with true in JTX. cbn [andb] in JTX.
pose proof NODE as NODE0. pose proof JHX as JHX0. pose proof HP as HP00. pose proof PB as PB00.
assert (LOS0 : lo <= bv_unsigned sp - 192 - 4096 - 112) by (unfold ser_budgetA, ASER_LEVEL, ASER_LEAF in LOS; rewrite sdepth_arr in LOS; pose proof (kdepth_nonneg kids); lia).
stash NODE0. stash JHX0. stash AL. stash KOK. stash LOS. stash HP00. stash PB00.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold ASER_ARR. unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 192%nat ST.
do 14 step. do 3 step. do 3 step. step. do 4 step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap w A FRS (bv_unsigned sp + -192) [(bv_unsigned sp + -192, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw3 : 24 <= w) by (eapply (jtxk_arr_acc (fun _ => True)); [intros s0' _ bs0 w0 r0 H0; exact (jtx_nonneg _ _ _ _ H0) | exact JTX]).
evt_done5.
eapply (ser_litA HIx sp gp m md LB LM FRS B pb lo bpos cap w LO HT CAP TXT NEED OBL_REALLOC_NF 0x23860 1 LIT_LBRACK) with (F := F) (e := 0);
[ vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | lia | lia | lia
| exact INV1 | lia | lia | lia | clear - SPA; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A3 m3 md3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 INV3 FS3 FR3.
unstash NODE0. unstash JHX0. unstash AL. unstash KOK. unstash LOS.
lazymatch type of INV3 with context [[(_, [CB 88 ?jj; _; _; _; _; _; _; _; _; _; _; _; _; _])]] =>
eapply (arr_startA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo p rc pb0 lv fl a arr size bpos cap w
ps KBS kids T Y R KIDS FL Hlv Hlvd LO LOS SPA HT RA CAP TXT NEED JHX0 FRSN INCL NODE0 AL KOK JTX K
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jj); [exact INV3 | exact FS3 | exact FR3] end.
Qed.
End Top.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI QXUB.  Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QsKa.Mqg QpNt.Mq8 QsKa.Mqh Qw5U.Mq5 Ql4f.Mq4. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 Ql4f. Import Qwm6.Mq1. Import Q228.Mqd.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 128 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ADBL_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 9 lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation dbl_invx := (dbl_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr).

Lemma dbl_epiA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x22 x23 x24 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (e len : Z) (bufb : list byte),
dbl_invx 0 A e bufb m md -> fsaved F F' -> (frm0 fc -> frm0 fc') -> 0 <= e <= 9 ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7 (wz Fr) x19 x20 (wz len) x22 x23 x24 (wz (Fr / 8 + 2147450880)) (wz Fr) x27 t3 t4 t5 t6)
F' (wz 0x9efd0) fc' None m (seg_rom asegs)).
Proof.
intros until bufb. intros INV FS FR He.
destruct INV as (LOCc & j8 & jr & t8 & HLOC & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold dblCH in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, SAV, FFx, SHx.
unfold dblSaved in SAV. unfold dblFF in FFx. unfold dblSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_2 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_2 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_2 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 32 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
stash LOC. stash PBUF. stash HFal. stash Hq32.
remember (Fr / 8 + 2147450880) as sh eqn:Esh. stash Esh.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr, Fr + 248); (sh, sh + 32)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. do 16 stepz.
step. step. stepz.
step. if_falsex.
step. do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
match goal with H : mem_inv asegs mX |- _ => rename H into MIX end.
unstash Esh.
assert (HPX : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 2) :: FRS) B mX md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MIX].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 2. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. rewrite <- Esh. lia. }
assert (SUBX : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 2 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
assert (HPRX : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUBX ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. rewrite <- Esh. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
stash Esh.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPX | exact INF | rewrite fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m7 md7 A7 VM7 HP7 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP7. rewrite Z.eqb_refl in HP7.
assert (MUr : munch [(fp, fp + 1)] mX m7).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs mX m7) by exact Hwv.
assert (MI7 : mem_inv asegs m7).
{ intros y b Hb0. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb0. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
assert (FPpb : ~ (pb <= fp < pb + PB_SZ)) by (intros Hin; apply FPnc; right; right; exists (pb, PB_SZ); split; [exact INpbX | exact Hin]).
assert (FPbuf : ~ (buf <= fp < buf + cap)) by (intros Hin; apply FPnc; right; right; exists (buf, cap); split; [exact INbufX | exact Hin]).
unfold alloc_ceiling in FPlow.
unstash LOC. unstash PBUF. unstash Esh.
assert (HLOCz : Z.of_nat (cells_size LOCc) = 24 + d) by (rewrite HLOC; lia).
assert (TRf : forall a cs, rw_cells asegs m a cs -> (a + Z.of_nat (cells_size cs) <= fp \/ fp + 1 <= a) ->
(a + Z.of_nat (cells_size cs) <= Fr \/ Fr + 248 <= a) -> (a + Z.of_nat (cells_size cs) <= sh \/ sh + 32 <= a) -> rw_cells asegs m7 a cs).
{ intros a cs H A1 A2 A3. eapply (rw_cells_transport asegs _ mX m7); [| exact MUr | exact WMr | cbn [disjoint_from]; split; [exact A1 | exact I]].
eapply (rw_cells_transport asegs _ m mX); [exact H | exact MU | exact WM |]. cbn [disjoint_from]. split; [exact A2 | split; [exact A3 | exact I]]. }
assert (LOC7 : rw_cells asegs m7 q LOCc) by (apply TRf; [exact LOC | rewrite HLOCz; lia | rewrite HLOCz; lia | rewrite HLOCz; lia]).
assert (PBUF7 : rw_cells asegs m7 buf [CB (Z.to_nat cap) content]) by (apply TRf; [exact PBUF | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]).
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in SAV; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in ERR; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_ERRNO, A_TP in *; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in PBS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] mX m7) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
reenterA asegs A4L HIx asegs_wx HP7.
step. step. step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m7, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS | exact FR]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM7]|].
split.
{ pose proof (stk_release asegs m7 lo q _ ST LOC7 ltac:(lia)) as S1. rewrite HLOCz in S1.
replace (q + (24 + d)) with (bv_unsigned sp + -104) in S1 by lia.
pose proof (stk_release asegs m7 lo (bv_unsigned sp + -104) _ S1 SAV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S3 by lia. exact S3. }
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPRX|].
exact (pres_fp HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) fp HPX SUBX ltac:(unfold alloc_ceiling; lia) FPnc FPfr Hoff Hwv). }
split; [exact ERR|]. split; [exact HP7|].
split; [split; [exact Hbp|]; split; [exact Hcap|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF7]|].
split; [lia|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.
End Dbl.
End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QsKa.Mqg QpNt.Mq8 QsKa.Mqh Qw5U.Mq5 Ql4f.Mq4. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 Ql4f. Import Qwm6.Mq1. Import Q228.Mqd.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 128 - d.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ADBL_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.

Notation dbl_invx := (dbl_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr).

Definition dbl_apart (a k : Z) : Prop :=
(a + k <= lo \/ q <= a) /\ (a + k <= Fr \/ Fr + 248 <= a) /\ (a + k <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 32 <= a).
Definition dbl_privW (iv : Z * Z) : Prop :=
(lo <= fst iv /\ snd iv <= q) \/ (Fr <= fst iv /\ snd iv <= Fr + 248) \/ (Fr / 8 + 2147450880 <= fst iv /\ snd iv <= Fr / 8 + 2147450880 + 32).
Lemma dbl_apart_disjoint : forall W a k, Forall dbl_privW W -> dbl_apart a k -> disjoint_from W a k.
Proof.
intros W a k HW (H1 & H2 & H3). induction HW as [|[l h] W Hiv _ IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
unfold dbl_privW in Hiv. cbn [fst snd] in Hiv. lia.
Qed.

Lemma dbl_inv_privA : forall v v' (A : ASA A4L HIx) e m m' md W bufb j8' bufb' jr' t8',
dbl_invx v A e bufb m md ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall dbl_privW W ->
rw_cells asegs m' Fr (dblFF j8' bufb' jr') -> rw_cells asegs m' (Fr / 8 + 2147450880) (dblSH v' t8') -> stk asegs m' lo q ->
dbl_invx v' A e bufb' m' md.
Proof.
intros until t8'. intros (LOCc & j8 & jr & t8 & HLOC & INV) MU WM MI' HW FF' SH' ST'.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_2 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (_ & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_2 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_2 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 32 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
assert (HLOCz : Z.of_nat (cells_size LOCc) = 24 + d) by (rewrite HLOC; destruct Hd; lia).
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (TR : forall a cs, rw_cells asegs m a cs -> dbl_apart a (Z.of_nat (cells_size cs)) -> rw_cells asegs m' a cs).
{ intros a cs H AP. eapply (rw_cells_transport asegs W m m'); [exact H | exact MU | exact WM | apply dbl_apart_disjoint; [exact HW | exact AP]]. }
exists LOCc, j8', jr', t8'. split; [exact HLOC|]. exists buf, cap, bpos, content, errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold dbl_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. left. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. lia. }
split.
{ destruct PB as (P1 & P2 & P3 & PBS & PBUF). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
split; [apply TR; [exact PBS | unfold dbl_apart; cbn [cells_size csize Nat.add]; lia]
| apply TR; [exact PBUF | unfold dbl_apart; cbn [cells_size csize Nat.add]; lia]]. }
unfold dblCH in CHm |- *.
apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHm as [C2 _].
cbn [fst snd] in C1, C2.
split.
{ constructor; [cbn [fst snd]; apply TR; [exact C1 | unfold dbl_apart; rewrite HLOCz; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C2 | unfold dbl_apart, dblSaved; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; exact FF'|].
constructor; [cbn [fst snd]; exact SH' | constructor]. }
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 2 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold dblFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_2; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 2); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, dblSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 2) with 32; unfold A_SB; lia]|].
constructor. }
split; [exact FSUB|].
split; [apply TR; [exact ERR | unfold dbl_apart, A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia]|].
split; [exact ST'|].
split.
{ eapply heap_pres_trans; [exact HPR|].
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 2 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB1 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold dbl_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_2. lia.
- right; right; right. exists Fr, 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 2) with 32. unfold A_SB. lia. }
split; [exact VM|]. split; [exact Hb|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.
End Dbl.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlbl QgK0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH Q0Ek.
Import QbFI. Import Qhd4. Import Qwm6.Mq4 QgHv Q9O6.Mq5 QlKV.Mqg Qlbl QgK0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Ser.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPA A4L HIx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_LD : isnprintf_ld_stmt PFRT PFLO.
Hypothesis SNP_LU : isnprintf_lu_stmt PFRT PFLO.

Theorem ser_intA : ser_specA HIx ASER_INT Sint.
Proof.
apply ser_specA_of_al.
- exact (ser_intA_0 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_LD SNP_LU).
- exact (ser_intA_16 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_LD SNP_LU).
Qed.
End Ser.
End RC__1.
End Mq8.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jt3A (c : Z) : Z :=
match c with
| 34 | 47 | 92 => 0x97f60
| 117 => 0x98180
| 98 | 102 | 110 | 114 | 116 => 0x972cc
| _ => 0x9a068
end.

Definition pe_jtab3A : list byte := Eval vm_compute in match image_bytes asegs 0x22e18 336 with Some bs => bs | None => [] end.
Lemma pe_jtab3A_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22e18 [CB 336 pe_jtab3A].
Proof.
intros m MI. change 336%nat with (length pe_jtab3A).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab3A)) with 336%Z. lia.
Qed.
Definition pe_jtab4A : list byte := Eval vm_compute in match image_bytes asegs 0x22f68 40 with Some bs => bs | None => [] end.
Lemma pe_jtab4A_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22f68 [CB 40 pe_jtab4A].
Proof.
intros m MI. change 40%nat with (length pe_jtab4A).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab4A)) with 40%Z. lia.
Qed.

Lemma pe_jt3A_cases : forall c, (pe_jt3A c = 0x97f60 /\ (c = 34 \/ c = 47 \/ c = 92)) \/ (pe_jt3A c = 0x98180 /\ c = 117)
\/ (pe_jt3A c = 0x972cc /\ (c = 98 \/ c = 102 \/ c = 110 \/ c = 114 \/ c = 116)) \/ pe_jt3A c = 0x9a068.
Proof.
intros c. unfold pe_jt3A. destruct c as [|p|p]; [tauto | | tauto].
do 8 (try (destruct p as [p|p|]; try tauto)).
Qed.

Section PeSSescDA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Lemma sesc_dispatch_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
(forall a5' a6',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jt3A (bv_unsigned cb)) (t_co ts) gp t0 a0 (Z_to_bv 64 (bv_unsigned cb)) a2 a3 a4 a5' a6' a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_string_escape) (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). destruct INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR). pose proof REST as (HP & _).
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & FF & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (pe_jtab3A_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear TOK PB TSK REST.
reenterA asegs A4L HIx asegs_wx HP. unfold ST_string_escape. cbn [pe_jtA].
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step.
destruct (Z_lt_dec (bv_unsigned cb) 34) as [LT | GE].
- replace (Z_to_bv 64 (bv_unsigned cb + -34)) with (Z_to_bv 64 (bv_unsigned cb + -34 + 2^64)).
2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- (Z_mod_plus_full (bv_unsigned cb + -34) 1 (2^64)). f_equal. }
step. if_falsex. step. evt_done5.
replace (pe_jt3A (bv_unsigned cb)) with 0x9a068 in K.
2:{ assert (R : 0 <= bv_unsigned cb <= 33) by lia. clear - R. enum_from (bv_unsigned cb) 0%Z 34%nat; reflexivity. }
apply K.
- destruct (Z_lt_dec 117 (bv_unsigned cb)) as [GT | LE].
+ step. if_falsex. step. evt_done5.
replace (pe_jt3A (bv_unsigned cb)) with 0x9a068 in K. 2:{ assert (R : 118 <= bv_unsigned cb <= 255) by lia. clear - R. enum_from (bv_unsigned cb) 118%Z 138%nat; reflexivity. }
apply K.
+ step. if_truex. step.
rewrite (unsigned_lit (bv_unsigned cb + -34)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. step. step.
pose proof (bytes_at_read asegs m 0x22e18 pe_jtab3A ((bv_unsigned cb + -34) * 4) 4 (ro_cells_bytes_atA _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab3A) with 336%nat; lia)) as RD.
unfold wa in RD. replace (0x22e18 + (bv_unsigned cb + -34) * 4) with ((bv_unsigned cb + -34) * 4 + 142872) in RD by lia.
step. step. step.
evt_done5.
assert (R : 34 <= bv_unsigned cb <= 117) by lia.
match goal with |- AJ5 _ _ _ _ _ (MS _ _ ?pc _ _ _ _) =>
replace pc with (Z_to_bv 64 (pe_jt3A (bv_unsigned cb))); [apply K |] end.
clear - R. enum_from (bv_unsigned cb) 34%Z 84%nat; apply bv_eq; vm_compute; reflexivity.
Qed.
End PeSSescDA.
End RC__1.
