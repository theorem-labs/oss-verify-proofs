(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B Q5Rg QZDE QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QRUw QSL3 Qvbw QYIF QnCn QR2u QrIB Q7UD QXUB Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Q9O6 Qiiq Q1Ey Qvmy Qawr Q30W Q2Do Ql4f QJlD Qu4M QUr4 Q3jZ Qmd7 Q22i Qg1M QkXq Q1Y6 QvPk Qoif Qkxa QjKS QnPO QB6X QSHS Qeia QRcT QkDD Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.

Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq7 QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 QsKa.Mq3 QsKa.Mq2 QlKV.Mq7 QsKa.Mq5 QlKV.Mq5 QlKV.Mq2 QsKa Q9O6.Mq1 Qiiq.Mq0.

Import Qvmy.Mq0 Qawr.Mq0 Q30W.Mq0 Q2Do.Mq0.

Import Qu4M.Mq0.
Import QUr4.
Import Q3jZ Qmd7 Q22i.
Import Qg1M.
Import Q30W.Mq3 QkXq.Mq2 Q1Y6.Mq0 Q30W.Mq1 QvPk Qoif.Mq0.

Import Qwm6.Mq2.
Import QB6X QSHS.Mq1 Qeia.Mq4 Qoif.Mq2 QRcT.Mq1.
Import Qeia.Mq3 QkDD.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcTop.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis OBL_STRDUP_NF : strdup_nf_stmt A4L HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HD_le : 96 + 4096 + 128 + HD <= DC_C.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.

Lemma jtx_obj_kidw : forall kids m BS p pb0 PBS t TBS es KBS Y w R,
List.NoDup (map blk_addr BS) ->
obj_view asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS -> jtx (Sobj kids) (BS ++ Y) = Some (w, R) ->
exists ws, length ws = length kids /\ w = 24 + obj_wsum (map (fun e => (oe_k e, oe_kn e)) es) ws /\ Forall (fun x => 0 <= x) ws /\
(forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri)) /\
(forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W).
Proof.
intros kids m BS p pb0 PBS t TBS es KBS Y w R ND OV H.
pose proof OV as (EBS & OPB & HDR & LH & OT & LE & LK & KIDS).
destruct LH as (tbl & size & les & svs & Hkvs & ETBS & LOPEN).
assert (LKe : length les = length kids) by (apply (f_equal (@length _)) in Hkvs; rewrite !length_map in Hkvs; lia).
assert (LKm : length (map (fun e => (le_k e, le_kn e) : blk) les) = length kids) by (rewrite length_map; exact LKe).
rewrite EBS, ETBS in H. unfold lh_blocks in H. cbn [app] in H. rewrite <- !app_assoc in H. rewrite jtx_obj_eq in H. cbn [snd] in H.
change (48 =? 48) with true in H. change (56 =? 56) with true in H. cbn [andb] in H.
match type of H with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT LKe; lia] end.
rewrite (firstn_app_exact _ _ _ LKm), (skipn_app_exact _ _ _ LKm) in H.
pose proof (kids_okv_of_nth asegs A4F m kids es KBS LE LK KIDS) as OKV.
destruct (QSHS.Mq1.jtxk_obj_kidw asegs A4F m kids _ KBS OKV (map (fun e => (le_k e, le_kn e) : blk) les) [] (PBS ++ Y) 24 w R pbtail_nil H) as (ws & L & Ew & NNw & K1 & K2).
exists ws. split; [exact L|]. split; [| split; [exact NNw | split; [exact K1 | exact K2]]].
rewrite Ew. f_equal. f_equal.

destruct OT as (IB & HDo & ENT).
apply nth_error_ext. intros j. rewrite !nth_error_map.
destruct (nth_error les j) as [le|] eqn:E1; destruct (nth_error es j) as [oe|] eqn:E2; cbn [option_map].
- assert (EK : le_k le = oe_k oe).
{ apply (f_equal (fun l => nth_error l j)) in Hkvs. rewrite !nth_error_map, E1, E2 in Hkvs. cbn in Hkvs. injection Hkvs as EK _. symmetry; exact EK. }
destruct (ENT j oe E2) as (_ & _ & _ & _ & _ & INk & _).
assert (INl : In (le_k le, le_kn le) BS).
{ rewrite EBS, ETBS. apply in_or_app; left. right. apply in_or_app; left. unfold lh_blocks. right; right. apply in_map_iff. exists le. split; [reflexivity | eapply nth_error_In; exact E1]. }
assert (INk2 : In (oe_k oe, oe_kn oe) BS) by (rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact INk).
rewrite EK in INl. rewrite EK. f_equal. f_equal. exact (nodup_addr_size BS _ _ _ ND INl INk2).
- exfalso. apply nth_error_None in E2. assert (L1q : (j < length les)%nat) by (apply nth_error_Some; congruence). lia.
- exfalso. apply nth_error_None in E1. assert (L2q : (j < length es)%nat) by (apply nth_error_Some; congruence). lia.
- reflexivity.
Qed.

Lemma le8_lbw8T : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.bytes_le_to_Z_le_val. pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.le_val_range _ (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.bytes_ok_map bs)) as H. rewrite length_map, Hl in H. cbn in H. lia. }
change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
rewrite <- Hl. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.Z_to_le_bytes_to_Z.
Qed.
Lemma rw_cells_CB_wordT : forall m A k bs,
rw_cells asegs m A [CB k bs] -> (8 <= k)%nat ->
rw_cells asegs m A [C8 (le_bytes_to_word (firstn 8 bs)); CB (k - 8) (skipn 8 bs)].
Proof.
intros m A k bs H Hk.
assert (L : length bs = k) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
apply (rw_cells_recast asegs m A [CB k bs]); [exact H | | |].
- cbn. split; [exact I|]. split; [rewrite length_skipn; lia | exact I].
- cbn [cells_bytes cbytes app]. rewrite le8_lbw8T by (rewrite length_firstn; lia). rewrite ?app_nil_r. apply firstn_skipn.
- cbn. lia.
Qed.

Lemma ff_split_arr : forall m Fr (w0 w1 w2 : word) jf, rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 96 jf] ->
rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 40 (firstn 40 jf); C8 (le_bytes_to_word (firstn 8 (skipn 40 jf))); CB 48 (skipn 8 (skipn 40 jf))].
Proof.
intros m Fr w0 w1 w2 jf H. apply (proj1 (rw_cells_app asegs m Fr [_;_;_] _)) in H as X. destruct X as [H3 HB]. cbn [cells_size csize Nat.add] in HB.
destruct (rw_cells_CB_cut asegs _ _ _ _ 40 HB ltac:(lia)) as [HB1 HB2].
pose proof (rw_cells_CB_wordT _ _ _ _ HB2 ltac:(lia)) as HB3. change (96 - 40 - 8)%nat with 48%nat in HB3.
apply (proj2 (rw_cells_app asegs m Fr [_;_;_] _)). split; [exact H3|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact HB1|]. cbn [cells_size csize Nat.add]. exact HB3.
Qed.
Lemma ff_split_obj : forall m Fr (w0 w1 w2 : word) jf, rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 96 jf] ->
rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 8 (firstn 8 jf); C8 (le_bytes_to_word (firstn 8 (skipn 8 jf))); CB 80 (skipn 8 (skipn 8 jf))].
Proof.
intros m Fr w0 w1 w2 jf H. apply (proj1 (rw_cells_app asegs m Fr [_;_;_] _)) in H as X. destruct X as [H3 HB]. cbn [cells_size csize Nat.add] in HB.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 HB ltac:(lia)) as [HB1 HB2].
pose proof (rw_cells_CB_wordT _ _ _ _ HB2 ltac:(lia)) as HB3. change (96 - 8 - 8)%nat with 80%nat in HB3.
apply (proj2 (rw_cells_app asegs m Fr [_;_;_] _)). split; [exact H3|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact HB1|]. cbn [cells_size csize Nat.add]. exact HB3.
Qed.
Section TopCtx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.
Local Notation ASP := (Qoif.Mq2.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq2.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq2.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq2.dc_dst D) (only parsing).
Local Notation dc_dst_munch := (Qoif.Mq2.dc_dst_munch HIx ra sp LM FRS lo D LO DLOC DAL) (only parsing).
Local Notation dc_body := (Qoif.Mq2.dc_body HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation dc_tail0 := (Qoif.Mq2.dc_tail0 HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC DAL NN JR0 Kont) (only parsing).
Local Notation dc_inv_own := (QRcT.Mq1.dc_inv_own HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation da_src_now := (QRcT.Mq1.da_src_now HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo p D r DLOC DAL JR0) (only parsing).

Lemma body_keep : forall (Ax : ASA A4L HIx) (LBx : list blk) (Bx : bud) (m3 mc : word -> option byte) (md3 : config) (Fr : Z),
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx m3 md3 -> incl (BS ++ LB) LBx ->
dc_inv m3 md3 ->
munch [(ASP, bv_unsigned sp + -104)] m3 mc -> wmono asegs m3 mc -> mem_inv asegs mc ->
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mc md3 /\ dc_inv mc md3 /\
(forall cs, rw_cells asegs m3 Fr cs -> Z.of_nat (cells_size cs) <= 120 -> rw_cells asegs mc Fr cs) /\
(forall cs, rw_cells asegs m3 (Fr / 8 + 2147450880) cs -> Z.of_nat (cells_size cs) <= 16 -> rw_cells asegs mc (Fr / 8 + 2147450880) cs) /\
(forall a k cs, In (a, k) (LBx ++ LM) -> rw_cells asegs m3 a cs -> Z.of_nat (cells_size cs) <= k -> rw_cells asegs mc a cs) /\
agree_on asegs LBx m3 mc /\
(forall q, dc_dst m3 q -> dc_dst mc q).
Proof.
intros Ax LBx Bx m3 mc md3 Fr HP INC INV MU WM MI.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold Qoif.Mq2.ASP in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
rewrite fr_size_1 in HFal, HFc, HFimg.
assert (SUB : sub_fp [(bv_unsigned sp + -192, bv_unsigned sp + -104)]
[(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)]).
{ intros x Hx. cbn [outside fst snd] in Hx |- *. lia. }
pose proof (munch_weaken _ _ _ _ SUB MU) as MU4.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold Qoif.Mq2.dc_save in SAVEi.
assert (HPc : HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mc md3) by (eapply (Qoif.Mq2.fk1_HEAPA HIx); [exact HP | exact LO | | exact MU4 | exact WM | exact MI]; unfold Qoif.Mq2.ASP; lia).
split; [exact HPc|].
assert (STc : stk asegs mc lo (bv_unsigned sp + -192)).
{ eapply (stk_transport_disjoint asegs); [exact STi | exact MU | exact WM | cbn [disjoint_from fst snd]; lia]. }
assert (SAVEc : dc_save mc).
{ unfold Qoif.Mq2.dc_save. eapply (rw_cells_transport asegs _ m3 mc); [exact SAVEi | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add fst snd]; lia]. }
split; [exact (dc_inv_own Ax LBx Bx m3 md3 Fr mc HP INC MU4 WM INV STc SAVEc)|].
split; [| split; [| split; [| split]]].
- intros cs H SZ. eapply (rw_cells_transport asegs _ m3 mc); [exact H | exact MU | exact WM | cbn [disjoint_from fst snd]; lia].
- intros cs H SZ. eapply (rw_cells_transport asegs _ m3 mc); [exact H | exact MU | exact WM | cbn [disjoint_from fst snd]].
split; [| exact I]. left. clear - SZ HF0 HFc ACR LOSu LO RD0. Z.div_mod_to_equations. lia.
- intros a k cs Hin H SZ. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP Hin) as (_ & _ & Hlo & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
eapply (rw_cells_transport asegs _ m3 mc); [exact H | exact MU | exact WM | cbn [disjoint_from fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. cbn [fst snd].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & Hlo & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *. split; [lia | exact I].
- intros q DD. exact (dc_dst_munch Ax LBx Bx m3 md3 Fr m3 mc q HP DD MU4 WM).
Qed.

Lemma dc_leafA :
forall (Fr q : Z) (CBS : list blk) (m3 : word -> option byte) (md3 : config) (A3 : ASA A4L HIx) (B3 : bud) (j40 j16 jf : list byte) (F3 : bvmap 5 word) (fc3 : bv 32)
(x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' : word) (n : Z),
match r with JRtree (Sobj _) | JRtree (Sarr _) | JRnull => False | _ => True end ->
match r with JRtree s => exists Y R, jtx s (BS ++ Y) = Some (w, R) | JRdblx _ => 9 <= w | JRstrx => 6 * Z.max n 8 + 2 <= w | JRnull => False end ->
match r with JRtree (Sstr _) => 6 * Z.max n 8 + 2 <= w | _ => True end ->
sh_okB r n + 512 <= DC_KB * w -> DC_KB * w <= bB B0 -> w <= bD B0 ->
dc_inv m3 md3 -> fsaved F F3 -> frm0 fc3 ->
HEAPAx A3 (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) B3 m3 md3 ->
rw_cells asegs m3 ASP [C8 (wz 0); CB 40 j40; C8 (wz SH_A); C8 (wz D); CB 16 j16; C8 (wz Fr)] ->
rw_cells asegs m3 Fr [C8 (wz 1102416563); C8 (wz 139913); C8 (wz 653196); CB 96 jf] ->
rw_cells asegs m3 (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
jroot_repA r m3 BS p ->
q <> 0 -> dc_dst m3 q -> QrIB.Mq0.scopy A4H A4F r m3 CBS q -> sh_shapeA r n CBS ->
bB B0 - sh_okB r n <= bB B3 -> bD B0 - 1 <= bD B3 ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3' t4' t5' t6')
F3 (wz 0x9f8d8) fc3 None m3 (seg_rom asegs)).
Proof.
intros until n. intros LEAF WT SW OKW BBW BDW INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND3.
assert (ND : List.NoDup (map blk_addr BS)) by (pose proof ND3 as X; rewrite !map_app in X; apply NoDup_app_remove_r in X; apply NoDup_app_remove_r in X; exact X).
assert (HiB : incl (BS ++ LB) (BS ++ CBS ++ LB)) by (intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; exact Hb]).
assert (W8 : 8 <= w).
{ destruct r as [|s|?|]; [exact (False_ind _ WT) | | lia | lia]. destruct WT as (Y & R & J). exact (QSHS.Mq1.jtx_ge8 _ _ _ _ J). }

assert (GO : forall (ty tojs pb : Z) (d : jroot) (np : Z),
rw_cells asegs m3 p (jhdr_cells ty 1 tojs pb 0 0) -> (ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 6) -> In (p, np) BS -> 48 <= np ->
copy_of r d -> jroot_repA d m3 CBS q -> dc_cwA d CBS w -> length CBS = 1%nat ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3' t4' t5' t6')
F3 (wz 0x9f8d8) fc3 None m3 (seg_rom asegs))).
{ intros ty tojs pb d np HDR TY INp Hnp CO JD CW L1.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. apply (proj1 (rw_cells_app asegs _ p [_] _)) in HDR as [TYC _].
eapply (dc_body Fr q CBS m3 md3 A3 B3 j40 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ ty np);
[exact HP3 | exact SCR3 | exact INp | exact Hnp | exact TYC | lia |].
intros mc j24 y10 y11 y12 MU WM MI SCRc.
replace (if ty =? 5 then 654044 else if ty =? 4 then 653580 else 654248) with 654248 by (destruct TY as [-> | [-> | [-> | ->]]]; reflexivity).
destruct (body_keep A3 _ B3 m3 mc md3 Fr HP3 HiB INV3 MU WM MI) as (HPc & INVc & KF & KSH & KB & AG & KD).
assert (INp3 : In (p, np) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INp).
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mc md3 A3 B3 Fr (wz 0) (CB 8 j24) j16 _ _
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d q np ty tojs pb CBS []);
[ exact INVc | exact FS3 | exact FRM3 | exact HPc | exact SCRc | reflexivity
| apply KF; [exact FF3 | cbn; lia] | reflexivity | apply KSH; [exact FSH3 | cbn; lia]
| exact (da_src_now A3 _ B3 mc md3 Fr mc md3 HPc ltac:(intros b Hb; apply in_or_app; left; exact Hb) INVc)
| exact INp | exact Hnp
| apply (KB p np); [exact INp3 | exact HDR0 | cbn; lia]
| exact CO | exact CW | exact Hq | apply KD; exact DD3
| eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JD | exact AG | intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb]
| lia | rewrite L1; cbn [Z.of_nat Pos.of_succ_nat]; unfold DC_KB in *; lia ]. }
idtac.

assert (ONE : forall (REST PBSq : list blk) (b : blk), CBS = REST ++ PBSq -> REST = [b] -> length CBS = 1%nat -> PBSq = [] /\ CBS = [b]).
{ intros REST PBSq b E1 E2 L1. subst REST. rewrite E1 in L1. cbn in L1. destruct PBSq; [| cbn in L1; lia]. split; [reflexivity | rewrite E1; reflexivity]. }

assert (GOUD : forall (pb0 ud udn : Z) (uds : list byte) (bits bits' : word),
r = JRtree (Sdouble true) -> In (p, 48) BS -> In (ud, udn) BS -> udn <= 2^31 ->
rw_cells asegs m3 p (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) pb0 (fn_free_userdata A4F) ud ++ [C8 bits]) ->
cstr asegs m3 ud udn uds -> CBS = [(q, 48)] ->
rw_cells asegs m3 q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) 0 0 0 ++ [C8 bits']) ->
w = 16 + Z.max 0 (udn - 1) ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3' t4' t5' t6')
F3 (wz 0x9f8d8) fc3 None m3 (seg_rom asegs))).
{ intros pb0 ud udn uds bits bits' Er INp INu HU H0 HC ECBS QX EW.
pose proof H0 as H. unfold jhdr_cells in H. apply (proj1 (rw_cells_app asegs _ p [_] _)) in H as [TYC _].
eapply (dc_body Fr q CBS m3 md3 A3 B3 j40 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ JT_DOUBLE 48);
[exact HP3 | exact SCR3 | exact INp | lia | exact TYC | unfold JT_DOUBLE; lia |].
intros mc j24 y10 y11 y12 MU WM MI SCRc. change (if JT_DOUBLE =? 5 then 654044 else if JT_DOUBLE =? 4 then 653580 else 654248) with 654248.
destruct (body_keep A3 _ B3 m3 mc md3 Fr HP3 HiB INV3 MU WM MI) as (HPc & INVc & KF & KSH & KB & AG & KD).
assert (INp3 : In (p, 48) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INp).
assert (INq3 : In (q, 48) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; rewrite ECBS; left; reflexivity).
assert (HPc' : HEAPAx A3 (BS ++ [(q, 48)] ++ [] ++ LB) LM ((Fr, 1) :: FRS) B3 mc md3) by (rewrite ECBS in HPc; exact HPc).
pose proof (proj1 HC) as UL. assert (BB3q : bB B0 - (16 * 48 + 512) <= bB B3) by (revert BB3; rewrite ?Er; intros BB3; exact BB3).
eapply (Qeia.Mq3.dc_tail_ud HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS SPA HT DLOC DAL NN JR0 Kont OBL_STRDUP_NF
_ _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mc md3 A3 B3 Fr (wz 0) (CB 8 j24) j16 _ _
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q pb0 ud udn uds bits bits' []);
[ exact INVc | exact FS3 | exact FRM3 | exact HPc' | exact SCRc | reflexivity
| apply KF; [exact FF3 | cbn; lia] | reflexivity | apply KSH; [exact FSH3 | cbn; lia]
| exact (da_src_now A3 _ B3 mc md3 Fr mc md3 HPc ltac:(intros b Hb; apply in_or_app; left; exact Hb) INVc)
| exact INp | exact INu | exact HU
| apply (KB p 48); [exact INp3 | exact H0 | cbn; lia]
| eapply (cstr_agree asegs); [exact HC | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; left; exact Hb] | exact INu | lia]
| exact Er | exact Hq | apply KD; exact DD3
| apply (KB q 48); [exact INq3 | exact QX | cbn; lia]
| clear - UL EW; lia | clear - UL EW BB3q BBW; unfold DC_KB in *; lia | clear - BD3 BDW EW; lia | clear - BD3 BDW EW; lia
| clear - UL EW BB3q BBW; unfold DC_KB in *; lia ]. }
cbn [QrIB.Mq0.scopy] in SC3.
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [jroot_rep] in JR3.
- destruct JR3 as [Hp J]. destruct WT as (Y & R & WT).
destruct sh as [|[|]| |h|kids|kids]; try (exfalso; exact LEAF); destruct J as (pb0 & PBS & REST & EBS & OPB & J).
+
destruct J as (b & junk & ER & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3.
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & bq & junkq & ERq & _).
destruct (ONE _ _ _ ECBS ERq SHP3) as [-> ECBS1].
eapply (GO JT_BOOLEAN) with (d := JRtree Sbool) (np := 48);
[exact H6 | unfold JT_BOOLEAN; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | exact SHP3].
* cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* cbn [dc_cwA]. rewrite ECBS1. exists 8. split; [reflexivity | exact W8].
+
destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST.
cbn [sh_shapeA] in SHP3. destruct SC3 as [ECBS [bits' QX]].
assert (EW : w = 16 + Z.max 0 (udn - 1)).
{ rewrite EBS in WT. cbn [app jtx] in WT. change (48 =? 48) with true in WT. cbn in WT. injection WT as E _. symmetry; exact E. }
eapply (GOUD pb0 ud udn uds bits bits'); [reflexivity | rewrite EBS; left; reflexivity | rewrite EBS; right; left; reflexivity | exact HU | exact H | exact HC | exact ECBS | exact QX | exact EW].
+
destruct J as (bits & ER & HS & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3.
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & bq & ERq & _).
destruct (ONE _ _ _ ECBS ERq SHP3) as [-> ECBS1].
assert (EW : w = 9).
{ rewrite EBS in WT. cbn [app jtx] in WT. change (48 =? 48) with true in WT. cbn in WT. injection WT as E _. symmetry; exact E. }
eapply (GO JT_DOUBLE) with (d := JRtree (Sdouble false)) (np := 48);
[exact H6 | unfold JT_DOUBLE; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | exact SHP3].
* cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* cbn [dc_cwA]. rewrite ECBS1. exists 9. split; [reflexivity | lia].
+
destruct J as (cty & v & junk & ER & CTY & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3.
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & ctyq & vq & junkq & ERq & _).
destruct (ONE _ _ _ ECBS ERq SHP3) as [-> ECBS1].
assert (EW : w = 20).
{ rewrite EBS in WT. cbn [app jtx] in WT. change (56 =? 56) with true in WT. cbn in WT. injection WT as E _. symmetry; exact E. }
eapply (GO JT_INT) with (d := JRtree Sint) (np := 56);
[exact H6 | unfold JT_INT; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | exact SHP3].
* cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* cbn [dc_cwA]. rewrite ECBS1. exists 20. split; [reflexivity | lia].
+
cbn [sh_shapeA] in SHP3. destruct SHP3 as (q' & z & ECBSz & Hz).
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & lenq & strq & junkq & ERq & LENq & _).
destruct (ONE _ _ _ ECBS ERq ltac:(rewrite ECBSz; reflexivity)) as [-> ECBS1].
assert (Ez : z = str_objsize lenq) by (rewrite ECBS1 in ECBSz; injection ECBSz as _ E; symmetry; exact E).
assert (CW : dc_cwA (JRtree (Sstr false)) CBS w).
{ cbn [dc_cwA]. rewrite ECBS1. exists (6 * Z.max lenq 8 + 2). split; [apply jtx_str; lia | unfold str_objsize in Ez; lia]. }
assert (H6 : exists np, In (p, np) BS /\ 56 <= np /\ rw_cells asegs m3 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb0 0 0)).
{ destruct h.
- destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HDq). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
exists 56. split; [rewrite EBS; left; reflexivity|]. split; [lia | exact H6].
- destruct J as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
exists (str_objsize len). split; [rewrite EBS; left; reflexivity|]. split; [unfold str_objsize; lia | exact H6]. }
destruct H6 as (np & INp & Hnp & H6).
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := np);
[exact H6 | unfold JT_STRING; lia | exact INp | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | exact CW | rewrite ECBS1; reflexivity].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
-
destruct JR3 as (Hp & Htojs & pb0 & PBS & bits & EBS & OPB & H).
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3. destruct SC3 as [ECBS XD].
eapply (GO JT_DOUBLE) with (d := JRdblx tojsx) (np := 48);
[exact H6 | unfold JT_DOUBLE; lia | rewrite EBS; left; reflexivity | lia | reflexivity | cbn [jroot_rep]; split; [exact Hq | split; [exact Htojs | exact XD]] | exact I | exact SHP3].
-
destruct JR3 as (Hp & pb0 & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & ALT).
assert (H6 : rw_cells asegs m3 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb0 0 0)).
{ destruct ALT as [(_ & _ & _ & junk & H) | (_ & pd & pdn & junk & junk2 & _ & _ & H & _)];
(apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X; destruct X as [H6 _]; exact H6). }
cbn [sh_shapeA] in SHP3. destruct SHP3 as (q' & z & ECBSz & Hz).
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & lenq & strq & junkq & ERq & LENq & _).
destruct (ONE _ _ _ ECBS ERq ltac:(rewrite ECBSz; reflexivity)) as [-> ECBS1].
assert (Ez : z = str_objsize lenq) by (rewrite ECBS1 in ECBSz; injection ECBSz as _ E; symmetry; exact E).
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := 48 + cap);
[exact H6 | unfold JT_STRING; lia | rewrite EBS; left; reflexivity | lia | reflexivity | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | rewrite ECBS1; reflexivity].
cbn [dc_cwA]. rewrite ECBS1. exists (6 * Z.max lenq 8 + 2). split; [apply jtx_str; lia | unfold str_objsize in Ez; lia].
Qed.
End TopCtx.

Lemma dcopy_step : forall r,
(forall kids s', r = JRtree (Sobj kids) \/ r = JRtree (Sarr kids) -> In (Some s') kids -> DCOPY HIx (JRtree s')) ->
r <> JRnull -> DCOPY HIx r.
Proof.
intros r IH NN. unfold DCOPY. intros until errv. intros HP JR _ G DC DLOC DU DAL ST LO LOS SPA HT ERR TP RA FRM FRN WT WLT BBW BDW A0 A4 A5 K.
subst a0 a4 a5 tp.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by (pose proof ND0 as X; rewrite !map_app in X; apply NoDup_app_remove_r in X; apply NoDup_app_remove_r in X; exact X).
assert (HiB : forall CBS, incl (BS ++ LB) (BS ++ CBS ++ LB)) by (intros CBS b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; exact Hb]).
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
assert (FRN' : Z.of_nat (length FRS) < 4096) by (clear - FRN RD0; lia).

assert (LEAFGO : forall n,
match r with JRtree (Sobj _) | JRtree (Sarr _) | JRnull => False | _ => True end ->
match r with JRtree s => exists Y R, jtx s (BS ++ Y) = Some (w, R) | JRdblx _ => 9 <= w | JRstrx => 6 * Z.max n 8 + 2 <= w | JRnull => False end ->
match r with JRtree (Sstr _) => 6 * Z.max n 8 + 2 <= w | _ => True end ->
sh_lenA r m p n -> sh_okB r n + 512 <= DC_KB * w -> 2 <= w ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) (wz SH_A) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz DCR_A) fc None m (seg_rom asegs))).
{ intros n LEAF WT' SW LEN OKW W2.
assert (NEEDB : sh_needB r n = sh_okB r n) by (destruct r as [|[| | | | |]| |]; try reflexivity; exfalso; exact LEAF).
eapply (Qoif.Mq2.dc_pro HIx SHALLOW ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w r T LO LOS SPA HT FRM DLOC DAL NN JR K) with (n := n);
[exact HP | exact ST | exact G | exact DC | exact DU | exact FRN' | exact LEN | rewrite NEEDB; clear - OKW BBW; lia | clear - W2 BDW; lia | exact BBW | exact BDW | rewrite NEEDB; clear - OKW; lia | exact W2 |].
intros Fr q CBS m3 md3 A3 B3 j40 j16 jf F3 fc3 x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.
eapply (dc_leafA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w r T LO LOS SPA HT DLOC DAL NN JR K Fr q CBS m3 md3 A3 B3 j40 j16 jf F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ n);
[exact LEAF | exact WT' | exact SW | exact OKW | exact BBW | exact BDW | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact SCR3 | exact FF3 | exact FSH3 | exact JR3 | exact Hq | exact DD3 | exact SC3 | exact SHP3 | exact BB3 | exact BD3]. }
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [dc_wtA] in WT.
2:{  apply (LEAFGO 0); [exact I | exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - WT; lia | clear - WT; lia]. }
2:{  destruct WT as (L & SL & WL).
apply (LEAFGO L); [exact I | exact WL | exact I | exact SL | cbn [sh_okB]; unfold DC_KB; clear - WL; lia | clear - WL; lia]. }
destruct JR as [Hp J]. destruct WT as (Y & R & WT). pose proof (QSHS.Mq1.jtx_ge8 _ _ _ _ WT) as W8.
destruct sh as [|u| |h|kids|kids].
- apply (LEAFGO 0); [exact I | exists Y, R; exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - W8; lia | clear - W8; lia].
- apply (LEAFGO 0); [exact I | exists Y, R; exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - W8; lia | clear - W8; lia].
- apply (LEAFGO 0); [exact I | exists Y, R; exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - W8; lia | clear - W8; lia].
-
pose proof J as (pb0 & PBS & REST & EBS & OPB & JS).
assert (SL : exists len, rw_cells asegs m (p + 40) [C8 (wz len)] /\ - 2^31 < len < 2^31 /\ 6 * Z.max (Z.abs len) 8 + 2 <= w).
{ destruct h.
- destruct JS as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HD'). subst REST.
pose proof WT as X. rewrite EBS in X. cbn [app jtx] in X. change (56 =? 56) with true in X. cbn [negb andb] in X. injection X as EW _.
unfold jhdr_cells in H. apply (proj1 (rw_cells_app asegs _ p [_;_;_;_;_;_] _)) in H as X2. destruct X2 as [_ H2]. cbn [cells_size csize Nat.add] in H2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H2 as X3. destruct X3 as [H2a _]. replace (p + Z.of_nat 40) with (p + 40) in H2a by lia.
exists len. split; [exact H2a|]. split; [lia | clear - EW Hlen Hpdn Hsl; lia].
- destruct JS as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
pose proof WT as X. rewrite EBS in X. cbn [app jtx] in X. unfold str_objsize in X.
replace (57 <=? 49 + Z.max len 8) with true in X by (symmetry; apply Z.leb_le; lia). injection X as EW _.
unfold jhdr_cells in H. apply (proj1 (rw_cells_app asegs _ p [_;_;_;_;_;_] _)) in H as X2. destruct X2 as [_ H2]. cbn [cells_size csize Nat.add] in H2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H2 as X3. destruct X3 as [H2a _]. replace (p + Z.of_nat 40) with (p + 40) in H2a by lia.
exists len. split; [exact H2a|]. split; [lia | unfold str_w in EW; clear - EW Hlen; lia]. }
destruct SL as (len & H40 & RL & WL).
apply (LEAFGO (Z.abs len)); [exact I | exists Y, R; exact WT | exact WL | | cbn [sh_okB]; unfold DC_KB; clear - WL; lia | clear - WL; lia].
cbn [sh_lenA]. exists len. split; [| split; [exact RL | lia]].
pose proof (Qfw3_c1.Mq2.rw_cells_bytes_at asegs _ _ _ H40) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
-
idtac.
assert (POS : forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0).
{ intros b n Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & Hal & Hlo & _). split; assumption. }
destruct (jval_obj_view asegs A4F kids m BS p 1 J POS) as (opb & OPBS & ot & OTBS & oes & OKBS & OV).
destruct (jtx_obj_kidw kids m BS p opb OPBS ot OTBS oes OKBS Y w R ND OV WT) as (ows & LWo & EWo & NNWo & KW1o & KW2o).
pose proof (QSHS.Mq1.obj_wsum_nonneg (map (fun e => (oe_k e, oe_kn e)) oes) ows NNWo) as WS0.
assert (IHo : forall s', In (Some s') kids -> DCOPY HIx (JRtree s')) by (intros s' Hin; eapply IH; [left; reflexivity | exact Hin]).
eapply (Qoif.Mq2.dc_pro HIx SHALLOW ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT FRM DLOC DAL NN (conj Hp J) K) with (n := 0);
[exact HP | exact ST | exact G | exact DC | exact DU | exact FRN' | exact I
| change (sh_needB (JRtree (Sobj kids)) 0) with 14464; unfold DC_KB in *; clear - BBW EWo WS0; lia | clear - BDW EWo WS0; lia | exact BBW | exact BDW
| change (sh_needB (JRtree (Sobj kids)) 0) with 14464; unfold DC_KB in *; clear - EWo WS0; lia | clear - EWo WS0; lia |].
intros Fr q CBS m3 md3 A3 B3 j40 j16 jf F3 fc3 x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.

pose proof OV as (_ & _ & HDR & _).
pose proof (QRcT.Mq1.da_src_agree HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB BS LM FRS lo D DLOC DAL A3 _ B3 m3 md3 Fr m3 md3 HP3 ltac:(intros b Hb; apply in_or_app; left; exact Hb) INV3) as AG3.
assert (INp : In (p, 48) BS) by (destruct OV as (EBSo & _); rewrite EBSo; apply in_or_app; left; left; reflexivity).
pose proof HDR as TYC0. unfold jhdr_cells in TYC0. apply (proj1 (rw_cells_app asegs _ p [_] _)) in TYC0 as X. destruct X as [TYC _]. clear TYC0.
apply (rw_cells_agree asegs BS m m3) in TYC; [| exact AG3 | exists p, 48; split; [exact INp | cbn; lia]].
eapply (Qoif.Mq2.dc_body HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS NN (conj Hp J) K
Fr q CBS m3 md3 A3 B3 j40 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ JT_OBJECT 48);
[exact HP3 | exact SCR3 | exact INp | lia | exact TYC | unfold JT_OBJECT; lia |].
intros mc j24 y10 y11 y12 MU WM MI SCRc. change (if JT_OBJECT =? 5 then 654044 else if JT_OBJECT =? 4 then 653580 else 654248) with 653580.
destruct (body_keep ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS HT DLOC DAL NN (conj Hp J) K A3 _ B3 m3 mc md3 Fr HP3 (HiB CBS) INV3 MU WM MI)
as (HPc & INVc & KF & KSH & KB & AG & KD).
cbn [sh_shapeA] in SHP3. destruct SHP3 as [LCBS CAPQ]. cbn [QrIB.Mq0.scopy] in SC3.
assert (JQ : jval asegs A4F (Sobj []) mc CBS q 1).
{ eapply (jval_agree asegs A4F); [exact SC3 | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] | apply incl_refl]. }
pose proof (QkDD.Mq0.jtx_empty_obj ra sp FRS D kids ows LWo mc CBS q JQ LCBS) as JTXQ.
eapply (QkDD.Mq0.dc_obj HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS HT DLOC DAL NN (conj Hp J) K
kids eq_refl FRN opb ot OPBS OTBS oes OKBS ows OV LWo EWo NNWo _ _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ F3 fc3 mc md3 A3 B3 Fr q _ CBS j24 j16 _ _ _ _);
[exact INVc | exact FS3 | exact FRM3 | exact HPc | exact SCRc | apply KF; [exact (ff_split_obj _ _ _ _ _ _ FF3) | cbn; lia] | apply KSH; [exact FSH3 | cbn; lia]
| exact Hq | apply KD; exact DD3 | exact JQ | exact LCBS | exact CAPQ | exact JTXQ | exact BD3 | exact BB3 |].
intros e0 He0 mc' c0 c1 INV' HP' OWN' COPY'.
eapply (QkDD.Mq0.dc_obj_loop HIx PUT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT DLOC DAL NN (conj Hp J) K
kids eq_refl FRN IHo opb ot OPBS OTBS oes OKBS ows OV LWo NNWo KW1o KW2o WLT BBW BDW LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HD_le HASH OBL_STRDUP_NF
(length oes - 0)%nat 0%nat e0 _ _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ _ _ _ _ _ F3 fc3 mc' md3 A3 B3 Fr q 24 _ CBS []);
[reflexivity | exact He0 | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | cbn [skipn]; exact (eq_sym EWo)].
-
idtac.
destruct (sarr_open asegs A4F kids m BS p 1 J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & junkA & EAL & _).
assert (WT2 : jtx (Sarr kids) ((((p, 48) :: [(a, AL_SZ); (arr, 8 * size)] ++ concat KBS) ++ PBS) ++ Y) = Some (w, R)) by (rewrite EBS, EAL in WT; exact WT).
destruct (QSHS.Mq1.jtx_arr_kidw asegs A4F m kids ps KBS PBS (p, 48) (a, AL_SZ) (arr, 8 * size) Y w R (akids_okp _ _ _ _ _ _ KIDS) WT2) as (ws & LW & EW & NNW & KW1 & KW2).
pose proof (QSHS.Mq1.arr_wsum_nonneg ws NNW) as WS0.
assert (IHa : forall s', In (Some s') kids -> DCOPY HIx (JRtree s')) by (intros s' Hin; eapply IH; [right; reflexivity | exact Hin]).
eapply (Qoif.Mq2.dc_pro HIx SHALLOW ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT FRM DLOC DAL NN (conj Hp J) K) with (n := 0);
[exact HP | exact ST | exact G | exact DC | exact DU | exact FRN' | exact I
| change (sh_needB (JRtree (Sarr kids)) 0) with 7936; unfold DC_KB in *; clear - BBW EW WS0; lia | clear - BDW EW WS0; lia | exact BBW | exact BDW
| change (sh_needB (JRtree (Sarr kids)) 0) with 7936; unfold DC_KB in *; clear - EW WS0; lia | clear - EW WS0; lia |].
intros Fr q CBS m3 md3 A3 B3 j40 j16 jf F3 fc3 x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x19 t3' t4' t5' t6' INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.
pose proof (QRcT.Mq1.da_src_agree HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB BS LM FRS lo D DLOC DAL A3 _ B3 m3 md3 Fr m3 md3 HP3 ltac:(intros b Hb; apply in_or_app; left; exact Hb) INV3) as AG3.
assert (INp : In (p, 48) BS) by (rewrite EBS; apply in_or_app; left; left; reflexivity).
pose proof HDR as TYC0. unfold jhdr_cells in TYC0. apply (proj1 (rw_cells_app asegs _ p [_] _)) in TYC0 as X. destruct X as [TYC _]. clear TYC0.
apply (rw_cells_agree asegs BS m m3) in TYC; [| exact AG3 | exists p, 48; split; [exact INp | cbn; lia]].
eapply (Qoif.Mq2.dc_body HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS NN (conj Hp J) K
Fr q CBS m3 md3 A3 B3 j40 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ JT_ARRAY 48);
[exact HP3 | exact SCR3 | exact INp | lia | exact TYC | unfold JT_ARRAY; lia |].
intros mc j24 y10 y11 y12 MU WM MI SCRc. change (if JT_ARRAY =? 5 then 654044 else if JT_ARRAY =? 4 then 653580 else 654248) with 654044.
destruct (body_keep ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS HT DLOC DAL NN (conj Hp J) K A3 _ B3 m3 mc md3 Fr HP3 (HiB CBS) INV3 MU WM MI)
as (HPc & INVc & KF & KSH & KB & AG & KD).
cbn [sh_shapeA] in SHP3. destruct SHP3 as [LCBS CAPQ]. cbn [QrIB.Mq0.scopy] in SC3.
assert (JQ : jval asegs A4F (Sarr []) mc CBS q 1).
{ eapply (jval_agree asegs A4F); [exact SC3 | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] | apply incl_refl]. }
eapply (QRcT.Mq1.dc_arr HIx PUT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT DLOC DAL NN (conj Hp J) K
kids eq_refl FRN IHa pb a PBS AL ps KBS ws EBS HDR HAL L1 L2 KIDS LW EW NNW KW1 KW2 WLT BBW BDW
_ _ _ _ _ _ _ _ _ _ _ _ x19 _ _ _ _ F3 fc3 mc md3 A3 B3 Fr q _ CBS);
[exact INVc | exact FS3 | exact FRM3 | exact HPc | | exact Hq | apply KD; exact DD3 | exact JQ | exact LCBS | exact CAPQ | exact BD3 | exact BB3].
unfold QRcT.Mq1.da_own. exists j24, j16, (firstn 40 jf), (skipn 8 (skipn 40 jf)), (wz 139913), (wz 653196).
split; [exact SCRc|]. split; [apply KF; [exact (ff_split_arr _ _ _ _ _ _ FF3) | cbn; lia] | apply KSH; [exact FSH3 | cbn; lia]].
Qed.

Theorem dcopy_A : forall r, r <> JRnull -> DCOPY HIx r.
Proof.
assert (TREE : forall s, DCOPY HIx (JRtree s)).
{ induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; apply dcopy_step; try discriminate;
intros kids0 s' [E|E] Hin; try discriminate; injection E as <-; apply IHk; exact Hin. }
intros r NN. destruct r as [|s|t|].
- exfalso; exact (NN eq_refl).
- apply TREE.
- apply dcopy_step; [intros kids s' [E|E]; discriminate | exact NN].
- apply dcopy_step; [intros kids s' [E|E]; discriminate | exact NN].
Qed.
End MDcTop.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qawr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qawr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Do.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJlD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUr4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmd7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q22i.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg1M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkXq.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvPk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvPk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qm5W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjKS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnPO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB6X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB6X.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRcT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRcT.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC0u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC0u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkDD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkDD.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcTop.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis OBL_STRDUP_NF : strdup_nf_stmt A4L HIx.
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= DC_C.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.

Lemma jtx_obj_kidw : forall kids m BS p pb0 PBS t TBS es KBS Y w R,
List.NoDup (map blk_addr BS) ->
obj_view asegs A4F kids m BS p 1 pb0 PBS t TBS es KBS -> jtx (Sobj kids) (BS ++ Y) = Some (w, R) ->
exists ws, length ws = length kids /\ w = 24 + obj_wsum (map (fun e => (oe_k e, oe_kn e)) es) ws /\ Forall (fun x => 0 <= x) ws /\
(forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri)) /\
(forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W).
Proof.
intros kids m BS p pb0 PBS t TBS es KBS Y w R ND OV H.
pose proof OV as (EBS & OPB & HDR & LH & OT & LE & LK & KIDS).
destruct LH as (tbl & size & les & svs & Hkvs & ETBS & LOPEN).
assert (LKe : length les = length kids) by (apply (f_equal (@length _)) in Hkvs; rewrite !length_map in Hkvs; lia).
assert (LKm : length (map (fun e => (le_k e, le_kn e) : blk) les) = length kids) by (rewrite length_map; exact LKe).
rewrite EBS, ETBS in H. unfold lh_blocks in H. cbn [app] in H. rewrite <- !app_assoc in H. rewrite jtx_obj_eq in H. cbn [snd] in H.
change (48 =? 48) with true in H. change (56 =? 56) with true in H. cbn [andb] in H.
match type of H with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT LKe; lia] end.
rewrite (firstn_app_exact _ _ _ LKm), (skipn_app_exact _ _ _ LKm) in H.
pose proof (kids_okv_of_nth asegs A4F m kids es KBS LE LK KIDS) as OKV.
destruct (QSHS.Mq1.jtxk_obj_kidw asegs A4F m kids _ KBS OKV (map (fun e => (le_k e, le_kn e) : blk) les) [] (PBS ++ Y) 24 w R pbtail_nil H) as (ws & L & Ew & NNw & K1 & K2).
exists ws. split; [exact L|]. split; [| split; [exact NNw | split; [exact K1 | exact K2]]].
rewrite Ew. f_equal. f_equal.

destruct OT as (IB & HDo & ENT).
apply nth_error_ext. intros j. rewrite !nth_error_map.
destruct (nth_error les j) as [le|] eqn:E1; destruct (nth_error es j) as [oe|] eqn:E2; cbn [option_map].
- assert (EK : le_k le = oe_k oe).
{ apply (f_equal (fun l => nth_error l j)) in Hkvs. rewrite !nth_error_map, E1, E2 in Hkvs. cbn in Hkvs. injection Hkvs as EK _. symmetry; exact EK. }
destruct (ENT j oe E2) as (_ & _ & _ & _ & _ & INk & _).
assert (INl : In (le_k le, le_kn le) BS).
{ rewrite EBS, ETBS. apply in_or_app; left. right. apply in_or_app; left. unfold lh_blocks. right; right. apply in_map_iff. exists le. split; [reflexivity | eapply nth_error_In; exact E1]. }
assert (INk2 : In (oe_k oe, oe_kn oe) BS) by (rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact INk).
rewrite EK in INl. rewrite EK. f_equal. f_equal. exact (nodup_addr_size BS _ _ _ ND INl INk2).
- exfalso. apply nth_error_None in E2. assert (L1q : (j < length les)%nat) by (apply nth_error_Some; congruence). lia.
- exfalso. apply nth_error_None in E1. assert (L2q : (j < length es)%nat) by (apply nth_error_Some; congruence). lia.
- reflexivity.
Qed.

Lemma le8_lbw8T : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.bytes_le_to_Z_le_val. pose proof (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.le_val_range _ (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.bytes_ok_map bs)) as H. rewrite length_map, Hl in H. cbn in H. lia. }
change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
rewrite <- Hl. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.Z_to_le_bytes_to_Z.
Qed.
Lemma rw_cells_CB_wordT : forall m A k bs,
rw_cells asegs m A [CB k bs] -> (8 <= k)%nat ->
rw_cells asegs m A [C8 (le_bytes_to_word (firstn 8 bs)); CB (k - 8) (skipn 8 bs)].
Proof.
intros m A k bs H Hk.
assert (L : length bs = k) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
apply (rw_cells_recast asegs m A [CB k bs]); [exact H | | |].
- cbn. split; [exact I|]. split; [rewrite length_skipn; lia | exact I].
- cbn [cells_bytes cbytes app]. rewrite le8_lbw8T by (rewrite length_firstn; lia). rewrite ?app_nil_r. apply firstn_skipn.
- cbn. lia.
Qed.

Lemma ff_split_arr : forall m Fr (w0 w1 w2 : word) jf, rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 96 jf] ->
rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 40 (firstn 40 jf); C8 (le_bytes_to_word (firstn 8 (skipn 40 jf))); CB 48 (skipn 8 (skipn 40 jf))].
Proof.
intros m Fr w0 w1 w2 jf H. apply (proj1 (rw_cells_app asegs m Fr [_;_;_] _)) in H as X. destruct X as [H3 HB]. cbn [cells_size csize Nat.add] in HB.
destruct (rw_cells_CB_cut asegs _ _ _ _ 40 HB ltac:(lia)) as [HB1 HB2].
pose proof (rw_cells_CB_wordT _ _ _ _ HB2 ltac:(lia)) as HB3. change (96 - 40 - 8)%nat with 48%nat in HB3.
apply (proj2 (rw_cells_app asegs m Fr [_;_;_] _)). split; [exact H3|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact HB1|]. cbn [cells_size csize Nat.add]. exact HB3.
Qed.
Lemma ff_split_obj : forall m Fr (w0 w1 w2 : word) jf, rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 96 jf] ->
rw_cells asegs m Fr [C8 w0; C8 w1; C8 w2; CB 8 (firstn 8 jf); C8 (le_bytes_to_word (firstn 8 (skipn 8 jf))); CB 80 (skipn 8 (skipn 8 jf))].
Proof.
intros m Fr w0 w1 w2 jf H. apply (proj1 (rw_cells_app asegs m Fr [_;_;_] _)) in H as X. destruct X as [H3 HB]. cbn [cells_size csize Nat.add] in HB.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 HB ltac:(lia)) as [HB1 HB2].
pose proof (rw_cells_CB_wordT _ _ _ _ HB2 ltac:(lia)) as HB3. change (96 - 8 - 8)%nat with 80%nat in HB3.
apply (proj2 (rw_cells_app asegs m Fr [_;_;_] _)). split; [exact H3|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact HB1|]. cbn [cells_size csize Nat.add]. exact HB3.
Qed.
Section TopCtx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D w : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stkA (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 32 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> dc_resA HIx r BS LB LM FRS D w B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.
Local Notation ASP := (Qoif.Mq6.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq6.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq6.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq6.dc_dst D) (only parsing).
Local Notation dc_dst_munch := (Qoif.Mq6.dc_dst_munch HIx ra sp LM FRS lo D LO DLOC DAL) (only parsing).

Local Notation dc_body := (Qoif.Mq6.dc_body HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation dc_tail0 := (Qoif.Mq6.dc_tail0 HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS SPA HT RA DLOC DAL NN JR0 Kont) (only parsing).
Local Notation dc_inv_own := (QRcT.Mq3.dc_inv_own HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation da_src_now := (QRcT.Mq3.da_src_now HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo p D r DLOC DAL JR0) (only parsing).

Lemma body_keep : forall (Ax : ASA A4L HIx) (LBx : list blk) (Bx : bud) (m3 mc : word -> option byte) (md3 : config) (Fr : Z),
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx m3 md3 -> incl (BS ++ LB) LBx ->
dc_inv m3 md3 ->
munch [(ASP, bv_unsigned sp + -104)] m3 mc -> wmono asegs m3 mc -> mem_inv asegs mc ->
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mc md3 /\ dc_inv mc md3 /\
(forall cs, rw_cells asegs m3 Fr cs -> Z.of_nat (cells_size cs) <= 120 -> rw_cells asegs mc Fr cs) /\
(forall cs, rw_cells asegs m3 (Fr / 8 + 2147450880) cs -> Z.of_nat (cells_size cs) <= 16 -> rw_cells asegs mc (Fr / 8 + 2147450880) cs) /\
(forall a k cs, In (a, k) (LBx ++ LM) -> rw_cells asegs m3 a cs -> Z.of_nat (cells_size cs) <= k -> rw_cells asegs mc a cs) /\
agree_on asegs LBx m3 mc /\
(forall q, dc_dst m3 q -> dc_dst mc q).
Proof.
intros Ax LBx Bx m3 mc md3 Fr HP INC INV MU WM MI.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold Qoif.Mq6.ASP in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INF : In (Fr, 1) ((Fr, 1) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & HFimg & _ & _ & _).
rewrite fr_size_1 in HFal, HFc, HFimg.
assert (SUB : sub_fp [(bv_unsigned sp + -192, bv_unsigned sp + -104)]
[(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)]).
{ intros x Hx. cbn [outside fst snd] in Hx |- *. lia. }
pose proof (munch_weaken _ _ _ _ SUB MU) as MU4.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold Qoif.Mq6.dc_save in SAVEi.
assert (HPc : HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mc md3) by (eapply (Qoif.Mq6.fk1_HEAPA HIx); [exact HP | exact LO | | exact MU4 | exact WM | exact MI]; unfold Qoif.Mq6.ASP; lia).
split; [exact HPc|].
assert (STc : stk asegs mc lo (bv_unsigned sp + -192)).
{ eapply (stk_transport_disjoint asegs); [exact STi | exact MU | exact WM | cbn [disjoint_from fst snd]; lia]. }
assert (SAVEc : dc_save mc).
{ unfold Qoif.Mq6.dc_save. eapply (rw_cells_transport asegs _ m3 mc); [exact SAVEi | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add fst snd]; lia]. }
split; [exact (dc_inv_own Ax LBx Bx m3 md3 Fr mc HP INC MU4 WM INV STc SAVEc)|].
split; [| split; [| split; [| split]]].
- intros cs H SZ. eapply (rw_cells_transport asegs _ m3 mc); [exact H | exact MU | exact WM | cbn [disjoint_from fst snd]; lia].
- intros cs H SZ. eapply (rw_cells_transport asegs _ m3 mc); [exact H | exact MU | exact WM | cbn [disjoint_from fst snd]].
split; [| exact I]. left. clear - SZ HF0 HFc ACR LOSu LO RD0. Z.div_mod_to_equations. lia.
- intros a k cs Hin H SZ. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP Hin) as (_ & _ & Hlo & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
eapply (rw_cells_transport asegs _ m3 mc); [exact H | exact MU | exact WM | cbn [disjoint_from fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. cbn [fst snd].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & Hlo & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *. split; [lia | exact I].
- intros q DD. exact (dc_dst_munch Ax LBx Bx m3 md3 Fr m3 mc q HP DD MU4 WM).
Qed.

Lemma dc_leafA :
forall (Fr q : Z) (CBS : list blk) (m3 : word -> option byte) (md3 : config) (A3 : ASA A4L HIx) (B3 : bud) (j48 j16 jf : list byte) (F3 : bvmap 5 word) (fc3 : bv 32)
(x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x21 t3' t4' t5' t6' : word) (n : Z),
match r with JRtree (Sobj _) | JRtree (Sarr _) | JRnull => False | _ => True end ->
match r with JRtree s => exists Y R, jtx s (BS ++ Y) = Some (w, R) | JRdblx _ => 9 <= w | JRstrx => 6 * Z.max n 8 + 2 <= w | JRnull => False end ->
match r with JRtree (Sstr _) => 6 * Z.max n 8 + 2 <= w | _ => True end ->
sh_okB r n + 512 <= DC_KB * w -> DC_KB * w <= bB B0 -> w <= bD B0 ->
dc_inv m3 md3 -> fsaved F F3 -> frm0 fc3 ->
HEAPAx A3 (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) B3 m3 md3 ->
rw_cells asegs m3 ASP [C8 (wz 0); CB 48 j48; C8 (wz SH_A); CB 16 j16; C8 (wz Fr)] ->
rw_cells asegs m3 Fr [C8 (wz 1102416563); C8 (wz 108820); C8 (wz 660968); CB 96 jf] ->
rw_cells asegs m3 (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
jroot_repA r m3 BS p ->
q <> 0 -> dc_dst m3 q -> QrIB.Mq0.scopy A4H A4F r m3 CBS q -> sh_shapeA r n CBS ->
bB B0 - sh_okB r n <= bB B3 -> bD B0 - 1 <= bD B3 ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3' t4' t5' t6')
F3 (wz 0xa1734) fc3 None m3 (seg_rom asegs)).
Proof.
intros until n. intros LEAF WT SW OKW BBW BDW INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND3.
assert (ND : List.NoDup (map blk_addr BS)) by (pose proof ND3 as X; rewrite !map_app in X; apply NoDup_app_remove_r in X; apply NoDup_app_remove_r in X; exact X).
assert (HiB : incl (BS ++ LB) (BS ++ CBS ++ LB)) by (intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; exact Hb]).
assert (W8 : 8 <= w).
{ destruct r as [|s|?|]; [exact (False_ind _ WT) | | lia | lia]. destruct WT as (Y & R & J). exact (QSHS.Mq1.jtx_ge8 _ _ _ _ J). }

assert (GO : forall (ty tojs pb : Z) (d : jroot) (np : Z),
rw_cells asegs m3 p (jhdr_cells ty 1 tojs pb 0 0) -> (ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 6) -> In (p, np) BS -> 48 <= np ->
copy_of r d -> jroot_repA d m3 CBS q -> dc_cwA d CBS w -> length CBS = 1%nat ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3' t4' t5' t6')
F3 (wz 0xa1734) fc3 None m3 (seg_rom asegs))).
{ intros ty tojs pb d np HDR TY INp Hnp CO JD CW L1.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. apply (proj1 (rw_cells_app asegs _ p [_] _)) in HDR as [TYC _].
eapply (dc_body Fr q CBS m3 md3 A3 B3 j48 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ ty np);
[exact HP3 | exact SCR3 | exact INp | exact Hnp | exact TYC | lia |].
intros mc j16a j8 y11 y12 MU WM MI SCRc.
replace (if ty =? 5 then 661672 else if ty =? 4 then 661360 else 661892) with 661892 by (destruct TY as [-> | [-> | [-> | ->]]]; reflexivity).
destruct (body_keep A3 _ B3 m3 mc md3 Fr HP3 HiB INV3 MU WM MI) as (HPc & INVc & KF & KSH & KB & AG & KD).
assert (INp3 : In (p, np) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INp).
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mc md3 A3 B3 Fr (wz 0) j16a (CB 8 j8) j16 _ _
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d q np ty tojs pb CBS []);
[ exact INVc | exact FS3 | exact FRM3 | exact HPc | exact SCRc | reflexivity
| apply KF; [exact FF3 | cbn; lia] | reflexivity | apply KSH; [exact FSH3 | cbn; lia]
| exact (da_src_now A3 _ B3 mc md3 Fr mc md3 HPc ltac:(intros b Hb; apply in_or_app; left; exact Hb) INVc)
| exact INp | exact Hnp
| apply (KB p np); [exact INp3 | exact HDR0 | cbn; lia]
| exact CO | exact CW | exact Hq | apply KD; exact DD3
| eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JD | exact AG | intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb]
| lia | rewrite L1; cbn [Z.of_nat Pos.of_succ_nat]; unfold DC_KB in *; lia ]. }
idtac.

assert (ONE : forall (REST PBSq : list blk) (b : blk), CBS = REST ++ PBSq -> REST = [b] -> length CBS = 1%nat -> PBSq = [] /\ CBS = [b]).
{ intros REST PBSq b E1 E2 L1. subst REST. rewrite E1 in L1. cbn in L1. destruct PBSq; [| cbn in L1; lia]. split; [reflexivity | rewrite E1; reflexivity]. }

assert (GOUD : forall (pb0 ud udn : Z) (uds : list byte) (bits bits' : word),
r = JRtree (Sdouble true) -> In (p, 48) BS -> In (ud, udn) BS -> udn <= 2^31 ->
rw_cells asegs m3 p (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) pb0 (fn_free_userdata A4F) ud ++ [C8 bits]) ->
cstr asegs m3 ud udn uds -> CBS = [(q, 48)] ->
rw_cells asegs m3 q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string A4F) 0 0 0 ++ [C8 bits']) ->
w = 16 + Z.max 0 (udn - 1) ->
AJ5 A4L HIx A3 T md3
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0' t1' t2' sp (wz ASP) (wz 1) a1' a2' a3' a4' a5' a6' a7'
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3' t4' t5' t6')
F3 (wz 0xa1734) fc3 None m3 (seg_rom asegs))).
{ intros pb0 ud udn uds bits bits' Er INp INu HU H0 HC ECBS QX EW.
pose proof H0 as H. unfold jhdr_cells in H. apply (proj1 (rw_cells_app asegs _ p [_] _)) in H as [TYC _].
eapply (dc_body Fr q CBS m3 md3 A3 B3 j48 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ JT_DOUBLE 48);
[exact HP3 | exact SCR3 | exact INp | lia | exact TYC | unfold JT_DOUBLE; lia |].
intros mc j16a j8 y11 y12 MU WM MI SCRc. change (if JT_DOUBLE =? 5 then 661672 else if JT_DOUBLE =? 4 then 661360 else 661892) with 661892.
destruct (body_keep A3 _ B3 m3 mc md3 Fr HP3 HiB INV3 MU WM MI) as (HPc & INVc & KF & KSH & KB & AG & KD).
assert (INp3 : In (p, 48) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INp).
assert (INq3 : In (q, 48) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; rewrite ECBS; left; reflexivity).
assert (HPc' : HEAPAx A3 (BS ++ [(q, 48)] ++ [] ++ LB) LM ((Fr, 1) :: FRS) B3 mc md3) by (rewrite ECBS in HPc; exact HPc).
pose proof (proj1 HC) as UL. assert (BB3q : bB B0 - (16 * 48 + 512) <= bB B3) by (revert BB3; rewrite ?Er; intros BB3; exact BB3).
eapply (Qeia.Mq9.dc_tail_ud HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS SPA HT RA DLOC DAL NN JR0 Kont OBL_STRDUP_NF
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mc md3 A3 B3 Fr (wz 0) j16a (CB 8 j8) j16 _ _
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q pb0 ud udn uds bits bits' []);
[ exact INVc | exact FS3 | exact FRM3 | exact HPc' | exact SCRc | reflexivity
| apply KF; [exact FF3 | cbn; lia] | reflexivity | apply KSH; [exact FSH3 | cbn; lia]
| exact (da_src_now A3 _ B3 mc md3 Fr mc md3 HPc ltac:(intros b Hb; apply in_or_app; left; exact Hb) INVc)
| exact INp | exact INu | exact HU
| apply (KB p 48); [exact INp3 | exact H0 | cbn; lia]
| eapply (cstr_agree asegs); [exact HC | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; left; exact Hb] | exact INu | lia]
| exact Er | exact Hq | apply KD; exact DD3
| apply (KB q 48); [exact INq3 | exact QX | cbn; lia]
| clear - UL EW; lia | clear - UL EW BB3q BBW; unfold DC_KB in *; lia | clear - BD3 BDW EW; lia | clear - BD3 BDW EW; lia
| clear - UL EW BB3q BBW; unfold DC_KB in *; lia ]. }
cbn [QrIB.Mq0.scopy] in SC3.
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [jroot_rep] in JR3.
- destruct JR3 as [Hp J]. destruct WT as (Y & R & WT).
destruct sh as [|[|]| |h|kids|kids]; try (exfalso; exact LEAF); destruct J as (pb0 & PBS & REST & EBS & OPB & J).
+
destruct J as (b & junk & ER & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3.
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & bq & junkq & ERq & _).
destruct (ONE _ _ _ ECBS ERq SHP3) as [-> ECBS1].
eapply (GO JT_BOOLEAN) with (d := JRtree Sbool) (np := 48);
[exact H6 | unfold JT_BOOLEAN; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | exact SHP3].
* cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* cbn [dc_cwA]. rewrite ECBS1. exists 8. split; [reflexivity | exact W8].
+
destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST.
cbn [sh_shapeA] in SHP3. destruct SC3 as [ECBS [bits' QX]].
assert (EW : w = 16 + Z.max 0 (udn - 1)).
{ rewrite EBS in WT. cbn [app jtx] in WT. change (48 =? 48) with true in WT. cbn in WT. injection WT as E _. symmetry; exact E. }
eapply (GOUD pb0 ud udn uds bits bits'); [reflexivity | rewrite EBS; left; reflexivity | rewrite EBS; right; left; reflexivity | exact HU | exact H | exact HC | exact ECBS | exact QX | exact EW].
+
destruct J as (bits & ER & HS & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3.
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & bq & ERq & _).
destruct (ONE _ _ _ ECBS ERq SHP3) as [-> ECBS1].
assert (EW : w = 9).
{ rewrite EBS in WT. cbn [app jtx] in WT. change (48 =? 48) with true in WT. cbn in WT. injection WT as E _. symmetry; exact E. }
eapply (GO JT_DOUBLE) with (d := JRtree (Sdouble false)) (np := 48);
[exact H6 | unfold JT_DOUBLE; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | exact SHP3].
* cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* cbn [dc_cwA]. rewrite ECBS1. exists 9. split; [reflexivity | lia].
+
destruct J as (cty & v & junk & ER & CTY & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3.
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & ctyq & vq & junkq & ERq & _).
destruct (ONE _ _ _ ECBS ERq SHP3) as [-> ECBS1].
assert (EW : w = 20).
{ rewrite EBS in WT. cbn [app jtx] in WT. change (56 =? 56) with true in WT. cbn in WT. injection WT as E _. symmetry; exact E. }
eapply (GO JT_INT) with (d := JRtree Sint) (np := 56);
[exact H6 | unfold JT_INT; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | exact SHP3].
* cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* cbn [dc_cwA]. rewrite ECBS1. exists 20. split; [reflexivity | lia].
+
cbn [sh_shapeA] in SHP3. destruct SHP3 as (q' & z & ECBSz & Hz).
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & lenq & strq & junkq & ERq & LENq & _).
destruct (ONE _ _ _ ECBS ERq ltac:(rewrite ECBSz; reflexivity)) as [-> ECBS1].
assert (Ez : z = str_objsize lenq) by (rewrite ECBS1 in ECBSz; injection ECBSz as _ E; symmetry; exact E).
assert (CW : dc_cwA (JRtree (Sstr false)) CBS w).
{ cbn [dc_cwA]. rewrite ECBS1. exists (6 * Z.max lenq 8 + 2). split; [apply jtx_str; lia | unfold str_objsize in Ez; lia]. }
assert (H6 : exists np, In (p, np) BS /\ 56 <= np /\ rw_cells asegs m3 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb0 0 0)).
{ destruct h.
- destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HDq). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
exists 56. split; [rewrite EBS; left; reflexivity|]. split; [lia | exact H6].
- destruct J as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
exists (str_objsize len). split; [rewrite EBS; left; reflexivity|]. split; [unfold str_objsize; lia | exact H6]. }
destruct H6 as (np & INp & Hnp & H6).
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := np);
[exact H6 | unfold JT_STRING; lia | exact INp | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC3] | exact CW | rewrite ECBS1; reflexivity].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
-
destruct JR3 as (Hp & Htojs & pb0 & PBS & bits & EBS & OPB & H).
apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
cbn [sh_shapeA] in SHP3. destruct SC3 as [ECBS XD].
eapply (GO JT_DOUBLE) with (d := JRdblx tojsx) (np := 48);
[exact H6 | unfold JT_DOUBLE; lia | rewrite EBS; left; reflexivity | lia | reflexivity | cbn [jroot_rep]; split; [exact Hq | split; [exact Htojs | exact XD]] | exact I | exact SHP3].
-
destruct JR3 as (Hp & pb0 & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & ALT).
assert (H6 : rw_cells asegs m3 p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb0 0 0)).
{ destruct ALT as [(_ & _ & _ & junk & H) | (_ & pd & pdn & junk & junk2 & _ & _ & H & _)];
(apply (proj1 (rw_cells_app asegs _ p [_; _; _; _; _; _] _)) in H as X; destruct X as [H6 _]; exact H6). }
cbn [sh_shapeA] in SHP3. destruct SHP3 as (q' & z & ECBSz & Hz).
pose proof SC3 as (pbq & PBSq & RESTq & ECBS & OPBq & lenq & strq & junkq & ERq & LENq & _).
destruct (ONE _ _ _ ECBS ERq ltac:(rewrite ECBSz; reflexivity)) as [-> ECBS1].
assert (Ez : z = str_objsize lenq) by (rewrite ECBS1 in ECBSz; injection ECBSz as _ E; symmetry; exact E).
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := 48 + cap);
[exact H6 | unfold JT_STRING; lia | rewrite EBS; left; reflexivity | lia | reflexivity | cbn [jroot_rep]; split; [exact Hq | exact SC3] | | rewrite ECBS1; reflexivity].
cbn [dc_cwA]. rewrite ECBS1. exists (6 * Z.max lenq 8 + 2). split; [apply jtx_str; lia | unfold str_objsize in Ez; lia].
Qed.
End TopCtx.

Lemma dcopy_step : forall r,
(forall kids s', r = JRtree (Sobj kids) \/ r = JRtree (Sarr kids) -> In (Some s') kids -> DCOPY HIx (JRtree s')) ->
r <> JRnull -> DCOPY HIx r.
Proof.
intros r IH NN. unfold DCOPY. intros until errv. intros HP JR _ G DC DLOC DU DAL ST LO LOS SPA HT ERR TP RA FRM FRN WT WLT BBW BDW A0 A4 A5 K.
subst a0 a4 a5 tp.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by (pose proof ND0 as X; rewrite !map_app in X; apply NoDup_app_remove_r in X; apply NoDup_app_remove_r in X; exact X).
assert (HiB : forall CBS, incl (BS ++ LB) (BS ++ CBS ++ LB)) by (intros CBS b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; exact Hb]).
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
assert (FRN' : Z.of_nat (length FRS) < 4096) by (clear - FRN RD0; lia).

assert (LEAFGO : forall n,
match r with JRtree (Sobj _) | JRtree (Sarr _) | JRnull => False | _ => True end ->
match r with JRtree s => exists Y R, jtx s (BS ++ Y) = Some (w, R) | JRdblx _ => 9 <= w | JRstrx => 6 * Z.max n 8 + 2 <= w | JRnull => False end ->
match r with JRtree (Sstr _) => 6 * Z.max n 8 + 2 <= w | _ => True end ->
sh_lenA r m p n -> sh_okB r n + 512 <= DC_KB * w -> 2 <= w ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) (wz SH_A) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz DCR_A) fc None m (seg_rom asegs))).
{ intros n LEAF WT' SW LEN OKW W2.
assert (NEEDB : sh_needB r n = sh_okB r n) by (destruct r as [|[| | | | |]| |]; try reflexivity; exfalso; exact LEAF).
eapply (Qoif.Mq6.dc_pro HIx SHALLOW ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w r T LO LOS SPA HT FRM DLOC DAL NN JR K) with (n := n);
[exact HP | exact ST | exact G | exact DC | exact DU | exact FRN' | exact LEN | rewrite NEEDB; clear - OKW BBW; lia | clear - W2 BDW; lia | exact BBW | exact BDW | rewrite NEEDB; clear - OKW; lia | exact W2 |].
intros Fr q CBS m3 md3 A3 B3 j48 j16 jf F3 fc3 x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x21 t3' t4' t5' t6' INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.
eapply (dc_leafA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w r T LO LOS SPA HT RA DLOC DAL NN JR K Fr q CBS m3 md3 A3 B3 j48 j16 jf F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ n);
[exact LEAF | exact WT' | exact SW | exact OKW | exact BBW | exact BDW | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact SCR3 | exact FF3 | exact FSH3 | exact JR3 | exact Hq | exact DD3 | exact SC3 | exact SHP3 | exact BB3 | exact BD3]. }
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [dc_wtA] in WT.
2:{  apply (LEAFGO 0); [exact I | exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - WT; lia | clear - WT; lia]. }
2:{  destruct WT as (L & SL & WL).
apply (LEAFGO L); [exact I | exact WL | exact I | exact SL | cbn [sh_okB]; unfold DC_KB; clear - WL; lia | clear - WL; lia]. }
destruct JR as [Hp J]. destruct WT as (Y & R & WT). pose proof (QSHS.Mq1.jtx_ge8 _ _ _ _ WT) as W8.
destruct sh as [|u| |h|kids|kids].
- apply (LEAFGO 0); [exact I | exists Y, R; exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - W8; lia | clear - W8; lia].
- apply (LEAFGO 0); [exact I | exists Y, R; exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - W8; lia | clear - W8; lia].
- apply (LEAFGO 0); [exact I | exists Y, R; exact WT | exact I | exact I | cbn [sh_okB]; unfold DC_KB; clear - W8; lia | clear - W8; lia].
-
pose proof J as (pb0 & PBS & REST & EBS & OPB & JS).
assert (SL : exists len, rw_cells asegs m (p + 40) [C8 (wz len)] /\ - 2^31 < len < 2^31 /\ 6 * Z.max (Z.abs len) 8 + 2 <= w).
{ destruct h.
- destruct JS as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HD'). subst REST.
pose proof WT as X. rewrite EBS in X. cbn [app jtx] in X. change (56 =? 56) with true in X. cbn [negb andb] in X. injection X as EW _.
unfold jhdr_cells in H. apply (proj1 (rw_cells_app asegs _ p [_;_;_;_;_;_] _)) in H as X2. destruct X2 as [_ H2]. cbn [cells_size csize Nat.add] in H2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H2 as X3. destruct X3 as [H2a _]. replace (p + Z.of_nat 40) with (p + 40) in H2a by lia.
exists len. split; [exact H2a|]. split; [lia | clear - EW Hlen Hpdn Hsl; lia].
- destruct JS as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
pose proof WT as X. rewrite EBS in X. cbn [app jtx] in X. unfold str_objsize in X.
replace (57 <=? 49 + Z.max len 8) with true in X by (symmetry; apply Z.leb_le; lia). injection X as EW _.
unfold jhdr_cells in H. apply (proj1 (rw_cells_app asegs _ p [_;_;_;_;_;_] _)) in H as X2. destruct X2 as [_ H2]. cbn [cells_size csize Nat.add] in H2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H2 as X3. destruct X3 as [H2a _]. replace (p + Z.of_nat 40) with (p + 40) in H2a by lia.
exists len. split; [exact H2a|]. split; [lia | unfold str_w in EW; clear - EW Hlen; lia]. }
destruct SL as (len & H40 & RL & WL).
apply (LEAFGO (Z.abs len)); [exact I | exists Y, R; exact WT | exact WL | | cbn [sh_okB]; unfold DC_KB; clear - WL; lia | clear - WL; lia].
cbn [sh_lenA]. exists len. split; [| split; [exact RL | lia]].
pose proof (Qfw3_c1.Mq2.rw_cells_bytes_at asegs _ _ _ H40) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
-
idtac.
assert (POS : forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0).
{ intros b n Hb. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & Hal & Hlo & _). split; assumption. }
destruct (jval_obj_view asegs A4F kids m BS p 1 J POS) as (opb & OPBS & ot & OTBS & oes & OKBS & OV).
destruct (jtx_obj_kidw kids m BS p opb OPBS ot OTBS oes OKBS Y w R ND OV WT) as (ows & LWo & EWo & NNWo & KW1o & KW2o).
pose proof (QSHS.Mq1.obj_wsum_nonneg (map (fun e => (oe_k e, oe_kn e)) oes) ows NNWo) as WS0.
assert (IHo : forall s', In (Some s') kids -> DCOPY HIx (JRtree s')) by (intros s' Hin; eapply IH; [left; reflexivity | exact Hin]).
eapply (Qoif.Mq6.dc_pro HIx SHALLOW ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT FRM DLOC DAL NN (conj Hp J) K) with (n := 0);
[exact HP | exact ST | exact G | exact DC | exact DU | exact FRN' | exact I
| change (sh_needB (JRtree (Sobj kids)) 0) with 15488; unfold DC_KB in *; clear - BBW EWo WS0; lia | clear - BDW EWo WS0; lia | exact BBW | exact BDW
| change (sh_needB (JRtree (Sobj kids)) 0) with 15488; unfold DC_KB in *; clear - EWo WS0; lia | clear - EWo WS0; lia |].
intros Fr q CBS m3 md3 A3 B3 j48 j16 jf F3 fc3 x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x21 t3' t4' t5' t6' INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.

pose proof OV as (_ & _ & HDR & _).
pose proof (QRcT.Mq3.da_src_agree HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB BS LM FRS lo D DLOC DAL A3 _ B3 m3 md3 Fr m3 md3 HP3 ltac:(intros b Hb; apply in_or_app; left; exact Hb) INV3) as AG3.
assert (INp : In (p, 48) BS) by (destruct OV as (EBSo & _); rewrite EBSo; apply in_or_app; left; left; reflexivity).
pose proof HDR as TYC0. unfold jhdr_cells in TYC0. apply (proj1 (rw_cells_app asegs _ p [_] _)) in TYC0 as X. destruct X as [TYC _]. clear TYC0.
apply (rw_cells_agree asegs BS m m3) in TYC; [| exact AG3 | exists p, 48; split; [exact INp | cbn; lia]].
eapply (Qoif.Mq6.dc_body HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS NN (conj Hp J) K
Fr q CBS m3 md3 A3 B3 j48 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ JT_OBJECT 48);
[exact HP3 | exact SCR3 | exact INp | lia | exact TYC | unfold JT_OBJECT; lia |].
intros mc j16a j8 y11 y12 MU WM MI SCRc. change (if JT_OBJECT =? 5 then 661672 else if JT_OBJECT =? 4 then 661360 else 661892) with 661360.
destruct (body_keep ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS HT DLOC DAL NN (conj Hp J) K A3 _ B3 m3 mc md3 Fr HP3 (HiB CBS) INV3 MU WM MI)
as (HPc & INVc & KF & KSH & KB & AG & KD).
cbn [sh_shapeA] in SHP3. destruct SHP3 as [LCBS CAPQ]. cbn [QrIB.Mq0.scopy] in SC3.
assert (JQ : jval asegs A4F (Sobj []) mc CBS q 1).
{ eapply (jval_agree asegs A4F); [exact SC3 | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] | apply incl_refl]. }
pose proof (QkDD.jtx_empty_obj ra sp FRS D kids ows LWo mc CBS q JQ LCBS) as JTXQ.
eapply (QkDD.dc_obj HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT RA DLOC DAL NN (conj Hp J) K
kids eq_refl FRN opb ot OPBS OTBS oes OKBS ows OV LWo EWo NNWo _ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ F3 fc3 mc md3 A3 B3 Fr q _ CBS j16a j8 j16 _ _ _ _);
[exact INVc | exact FS3 | exact FRM3 | exact HPc | exact SCRc | apply KF; [exact (ff_split_obj _ _ _ _ _ _ FF3) | cbn; lia] | apply KSH; [exact FSH3 | cbn; lia]
| exact Hq | apply KD; exact DD3 | exact JQ | exact LCBS | exact CAPQ | exact JTXQ | exact BD3 | exact BB3 |].
intros e0 He0 mc' c0 c1 INV' HP' OWN' COPY'.
eapply (QkDD.dc_obj_loop HIx PUT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT RA DLOC DAL NN (conj Hp J) K
kids eq_refl FRN IHo opb ot OPBS OTBS oes OKBS ows OV LWo NNWo KW1o KW2o WLT BBW BDW LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HD_le HASH
(length oes - 0)%nat 0%nat e0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mc' md3 A3 B3 Fr q 24 _ CBS []);
[reflexivity | exact He0 | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | cbn [skipn]; exact (eq_sym EWo)].
-
idtac.
destruct (sarr_open asegs A4F kids m BS p 1 J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & junkA & EAL & _).
assert (WT2 : jtx (Sarr kids) ((((p, 48) :: [(a, AL_SZ); (arr, 8 * size)] ++ concat KBS) ++ PBS) ++ Y) = Some (w, R)) by (rewrite EBS, EAL in WT; exact WT).
destruct (QSHS.Mq1.jtx_arr_kidw asegs A4F m kids ps KBS PBS (p, 48) (a, AL_SZ) (arr, 8 * size) Y w R (akids_okp _ _ _ _ _ _ KIDS) WT2) as (ws & LW & EW & NNW & KW1 & KW2).
pose proof (QSHS.Mq1.arr_wsum_nonneg ws NNW) as WS0.
assert (IHa : forall s', In (Some s') kids -> DCOPY HIx (JRtree s')) by (intros s' Hin; eapply IH; [right; reflexivity | exact Hin]).
eapply (Qoif.Mq6.dc_pro HIx SHALLOW ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT FRM DLOC DAL NN (conj Hp J) K) with (n := 0);
[exact HP | exact ST | exact G | exact DC | exact DU | exact FRN' | exact I
| change (sh_needB (JRtree (Sarr kids)) 0) with 7936; unfold DC_KB in *; clear - BBW EW WS0; lia | clear - BDW EW WS0; lia | exact BBW | exact BDW
| change (sh_needB (JRtree (Sarr kids)) 0) with 7936; unfold DC_KB in *; clear - EW WS0; lia | clear - EW WS0; lia |].
intros Fr q CBS m3 md3 A3 B3 j48 j16 jf F3 fc3 x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x21 t3' t4' t5' t6' INV3 FS3 FRM3 HP3 SCR3 FF3 FSH3 JR3 Hq DD3 SC3 SHP3 BB3 BD3.
pose proof (QRcT.Mq3.da_src_agree HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB BS LM FRS lo D DLOC DAL A3 _ B3 m3 md3 Fr m3 md3 HP3 ltac:(intros b Hb; apply in_or_app; left; exact Hb) INV3) as AG3.
assert (INp : In (p, 48) BS) by (rewrite EBS; apply in_or_app; left; left; reflexivity).
pose proof HDR as TYC0. unfold jhdr_cells in TYC0. apply (proj1 (rw_cells_app asegs _ p [_] _)) in TYC0 as X. destruct X as [TYC _]. clear TYC0.
apply (rw_cells_agree asegs BS m m3) in TYC; [| exact AG3 | exists p, 48; split; [exact INp | cbn; lia]].
eapply (Qoif.Mq6.dc_body HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS NN (conj Hp J) K
Fr q CBS m3 md3 A3 B3 j48 j16 F3 fc3 _ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ JT_ARRAY 48);
[exact HP3 | exact SCR3 | exact INp | lia | exact TYC | unfold JT_ARRAY; lia |].
intros mc j16a j8 y11 y12 MU WM MI SCRc. change (if JT_ARRAY =? 5 then 661672 else if JT_ARRAY =? 4 then 661360 else 661892) with 661672.
destruct (body_keep ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS HT DLOC DAL NN (conj Hp J) K A3 _ B3 m3 mc md3 Fr HP3 (HiB CBS) INV3 MU WM MI)
as (HPc & INVc & KF & KSH & KB & AG & KD).
cbn [sh_shapeA] in SHP3. destruct SHP3 as [LCBS CAPQ]. cbn [QrIB.Mq0.scopy] in SC3.
assert (JQ : jval asegs A4F (Sarr []) mc CBS q 1).
{ eapply (jval_agree asegs A4F); [exact SC3 | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] | apply incl_refl]. }
eapply (QRcT.Mq3.dc_arr HIx PUT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B lo p D w _ T LO LOS SPA HT RA DLOC DAL NN (conj Hp J) K
kids eq_refl FRN IHa pb a PBS AL ps KBS ws EBS HDR HAL L1 L2 KIDS LW EW NNW KW1 KW2 WLT BBW BDW
_ _ _ _ _ _ _ _ _ _ _ x21 _ _ _ _ F3 fc3 mc md3 A3 B3 Fr q _ CBS j16a j8 j16 _ _ _ _);
[exact INVc | exact FS3 | exact FRM3 | exact HPc | exact SCRc | apply KF; [exact (ff_split_arr _ _ _ _ _ _ FF3) | cbn; lia] | apply KSH; [exact FSH3 | cbn; lia]
| exact Hq | apply KD; exact DD3 | exact JQ | exact LCBS | exact CAPQ | exact BD3 | exact BB3].
Qed.

Theorem dcopy_A : forall r, r <> JRnull -> DCOPY HIx r.
Proof.
assert (TREE : forall s, DCOPY HIx (JRtree s)).
{ induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; apply dcopy_step; try discriminate;
intros kids0 s' [E|E] Hin; try discriminate; injection E as <-; apply IHk; exact Hin. }
intros r NN. destruct r as [|s|t|].
- exfalso; exact (NN eq_refl).
- apply TREE.
- apply dcopy_step; [intros kids s' [E|E]; discriminate | exact NN].
- apply dcopy_step; [intros kids s' [E|E]; discriminate | exact NN].
Qed.
End MDcTop.
End RC__1.
