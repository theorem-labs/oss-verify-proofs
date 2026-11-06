(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKY2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXDj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXDj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q25t. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNDM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7DP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7DP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHqi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHqi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi08.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6w1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6w1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWwJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWwJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4I1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4I1.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import QWRO(aentry, mkAE, ae_L) QFQR(rlay, mkRL, rl_T, ghost, tag_at, A_INSTANCE, ptrarr_lo).
Set Default Proof Using "All".
Local Ltac inw := (apply OBJS_common; first [solve [cbn; repeat first [left; reflexivity | right]] | cbn; tauto]).

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma cells_size_map_C8' : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn [map cells_size csize length]; [reflexivity| rewrite IH; lia]. Qed.
Lemma cells_bytes_map_C8' : forall ws : list word, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. Qed.
Lemma RSec_cells_u64arr : forall m A ws, rw_cells asegs m A (map C8 ws) -> u64arr asegs m A ws.
Proof.
intros m A ws [[_ BA] WR]. split; [rewrite <- cells_bytes_map_C8'; exact BA|].
rewrite cells_size_map_C8', Nat2Z.inj_mul in WR. exact WR.
Qed.

Definition IA_LO : Z := 0x0f33c0.
Definition IA_HI : Z := 0x1743f0.
Definition IA_IMG_LO : Z := 0x0f33bc.
Definition IA_IMG_HI : Z := 0x174408.

Definition rsq_checks (k : list kentry) : bool :=

kn_rw_cells k QjgW.SEC_NRES [C8 (wz 0); C8 (wz 0)]

&& kn_rw_cells k QjgW.SEC_JUNK (repeat (C8 (wz 0)) 69)
&& kn_rw_cells k QjgW.SEC_MUT [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)]
&& kn_rw_cells k QjgW.SEC_GST (repeat (C8 (wz 0)) 5)

&& kn_rw_cells k QXcn.QMUT [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)]
&& kn_rw_cells k QXcn.GQ [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]

&& kn_rw_cells k QXcn.IA_FLAG [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)]
&& kn_has (KImg IA_IMG_LO IA_IMG_HI) k && img_zero IA_LO (IA_HI - IA_LO)

&& kn_has (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 237)) 80) (ELit 3088)) k
&& kn_has (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 237)) 0) (ELit 4096)) k
&& kn_has (KRange (EVar 237) 1 34359736319) k.

Lemma RSQ_CHECKS : forall w ch, HSCLASS_S w ch -> rsq_checks (kn_view ch) = true.  Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section OfKn.
Context {BAND : Band}.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Hypothesis HB : band_lo = atopE E.
#[local] Notation m := (view (LV_J E) mo FULL).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB) (only parsing).

Let KO : know_ok asegs E m (kn_view ch) := MV4 main_know_view.

Let T : Z := pg E 237.
Let parr : Z := pg E 236.

Lemma ch_split :
kn_rw_cells (kn_view ch) QjgW.SEC_NRES [C8 (wz 0); C8 (wz 0)] = true
/\ kn_rw_cells (kn_view ch) QjgW.SEC_JUNK (repeat (C8 (wz 0)) 69) = true
/\ kn_rw_cells (kn_view ch) QjgW.SEC_MUT [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)] = true
/\ kn_rw_cells (kn_view ch) QjgW.SEC_GST (repeat (C8 (wz 0)) 5) = true
/\ kn_rw_cells (kn_view ch) QXcn.QMUT [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)] = true
/\ kn_rw_cells (kn_view ch) QXcn.GQ [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] = true
/\ kn_rw_cells (kn_view ch) QXcn.IA_FLAG [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)] = true
/\ kn_has (KImg IA_IMG_LO IA_IMG_HI) (kn_view ch) = true /\ img_zero IA_LO (IA_HI - IA_LO) = true
/\ kn_has (KZero (SA (EMd Instr.M_MUL (ELit 4096) (EVar 237)) 80) (ELit 3088)) (kn_view ch) = true
/\ kn_has (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar 237)) 0) (ELit 4096)) (kn_view ch) = true
/\ kn_has (KRange (EVar 237) 1 34359736319) (kn_view ch) = true.
Proof.
pose proof (RSQ_CHECKS w ch HCL) as CH. unfold rsq_checks in CH. do 11 (apply andb_prop in CH as [CH ?X]). repeat split; assumption.
Qed.

Lemma T_val : zden E (EMd Instr.M_MUL (ELit 4096) (EVar 237)) = Some T.
Proof. reflexivity. Qed.

Lemma T_range : 4096 <= T /\ T + 4096 <= 2^47 /\ (T + 4096 <= 0x10000 \/ 0x647000 <= T).
Proof.
destruct ch_split as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R240).
pose proof (kn_range_var E m (kn_view ch) KO 237 _ _ R240).
pose proof ((LA obj_facts) (237%nat, 4096) ltac:(inw)) as (_ & _ & _ & _ & OH & TOP). cbn [fst snd] in OH, TOP.
pose proof (MA main_atop_bounds) as AB. subst T. unfold pg. lia.
Qed.

Lemma parr_range : 0x647000 <= parr /\ parr + 0x800000 <= band_lo.
Proof.
pose proof (LA sb_facts) as (_ & _ & _ & _ & _ & P1 & P2 & P3 & P4 & _). rewrite HB. subst parr. unfold pg, PARR in *. lia.
Qed.

Lemma TQ_cells : rw_cells asegs m (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Proof.
destruct ch_split as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KZ & _ & _). pose proof T_range as TR.
apply (kn_zero_rw E m (kn_view ch) KO _ 80 3088 T KZ T_val ltac:(lia) ltac:(lia)); [reflexivity| cbn [cells_size csize Nat.add]; lia| lia| cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma IA_zbytes : forall a n, IA_LO <= a -> a + n <= IA_HI -> 0 <= n -> QXcn.zbytes m a n.
Proof.
intros a n H1 H2 H3. destruct ch_split as (_ & _ & _ & _ & _ & _ & _ & KI & IZ & _).
destruct (kimg_zero_bytes E m (kn_view ch) KO IA_IMG_LO IA_IMG_HI IA_LO (IA_HI - IA_LO) KI ltac:(unfold IA_IMG_LO, IA_LO; lia)
ltac:(unfold IA_IMG_HI, IA_HI, IA_LO; lia) IZ) as [WR BY].
split.
- destruct WR as (W1 & W2 & W3). split; [unfold IA_LO in *; lia|]. split; [unfold IA_HI in *; lia|].
intros i Hi. replace (a + i) with (IA_LO + (a - IA_LO + i)) by lia. apply W3. lia.
- intros i Hi. replace (a + i) with (IA_LO + (a - IA_LO + i)) by lia. apply BY. lia.
Qed.

Theorem RSec_main : QjgW.RSec Q6sh.astate0 [] (RE_main sp w E) (X_main E) m.
Proof.
destruct ch_split as (C1 & C2 & C3 & C4 & _). pose proof parr_range as PR. pose proof band_lo_range as BR.
unfold QjgW.RSec, QjgW.RSec_mem. cbn [Q6sh.as_reg Q6sh.as_nres Q6sh.astate0 length Z.of_nat map].
change (ptrarr_lo (RE_main sp w E)) with parr.
split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C1)|].
split; [exists (repeat (wz 0) 69); split; [reflexivity|]; apply RSec_cells_u64arr; rewrite map_repeat; exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C2)|].
split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C3)|].
split; [exists (repeat (wz 0) 5); split; [reflexivity|]; apply RSec_cells_u64arr; rewrite map_repeat; exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C4)|].
split.
{ split.
- unfold bytes_at. cbn [u64s length Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
- unfold wr_at. cbn [length Z.of_nat Z.mul]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
split; [rewrite ?Z.mul_0_r, ?Z.add_0_r; apply QKBN.hjunk_nil; lia|].
split; [intros i e Hi; destruct i; discriminate|].
unfold Q6sh.kMaxNumChunks, Q6sh.kPtrArrBlock. split; [lia|]. split; [lia|]. reflexivity.
Qed.

Theorem RQuar_main : QXcn.RQuar Q6sh.astate0 [] G_main (RE_main sp w E) (X_main E) m.
Proof.
destruct ch_split as (_ & _ & _ & _ & C5 & C6 & C7 & _).
unfold QXcn.RQuar, QXcn.RQuarM. exists [], [], (fun _ => 0).
cbn [Q6sh.as_tq Q6sh.as_gq Q6sh.astate0 app].
split.
{  unfold QXcn.qrep. cbn [Q6sh.q_list Q6sh.q_bytes Q6sh.q0 length Z.of_nat QXcn.q_first QXcn.q_last].
split; [unfold QXcn.TQ; change (rl_T (X_main E)) with T; exact TQ_cells|].
split; [exact I|]. split; [constructor|]. split; [constructor| reflexivity]. }
split.
{  unfold QXcn.qrep. cbn [Q6sh.q_list Q6sh.q_bytes Q6sh.q0 length Z.of_nat QXcn.q_first QXcn.q_last].
split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C6)|].
split; [exact I|]. split; [constructor|]. split; [constructor| reflexivity]. }
split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C5)|].
split.
{  exists 0. split; [exact (kn_rw_cells_sound E m (kn_view ch) _ _ KO C7)|]. split; [left; reflexivity|].
split; [apply IA_zbytes; unfold QXcn.IA_MAP1, IA_LO, IA_HI; lia|].
right. split; [apply IA_zbytes; unfold QXcn.IA, IA_LO, IA_HI; lia|].
split; [apply IA_zbytes; unfold IA_LO, IA_HI; lia|].
split; apply IA_zbytes; unfold IA_LO, IA_HI; lia. }
split; [constructor|].
split; [intros j Hj; rewrite G_main_tag in Hj; discriminate|].
split; [intros c j Hj; rewrite G_main_tag in Hj; discriminate|].
unfold QXcn.qall. cbn [Q6sh.as_tq Q6sh.as_gq Q6sh.astate0 QXcn.qptrs Q6sh.q_list Q6sh.q0 map concat app Q6sh.q_bytes].
split; [constructor|].
split; [intros p Hp; destruct Hp|].
split; [intros c i p Hp; rewrite G_main_tag in Hp; discriminate|].
split; [constructor|].
unfold QXcn.QB. lia.
Qed.
End OfKn.

Theorem RSec_at_main : at_main_stmt (fun BAND sp w E m => QjgW.RSec Q6sh.astate0 [] (RE_main sp w E) (X_main E) m).
Proof.
intros sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BAND HB HG.
exact (RSec_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB).
Qed.
Theorem RQuar_at_main : at_main_stmt (fun BAND sp w E m => @QXcn.RQuar BAND Q6sh.astate0 [] G_main (RE_main sp w E) (X_main E) m).
Proof.
intros sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BAND HB HG.
exact (RQuar_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HB).
Qed.
