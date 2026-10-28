(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujal U9PQ U2Ei.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKdB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKdB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUr4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uyk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uyk8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrIB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udgq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udgq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uzop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uzop. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJlD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJlD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZYZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZYZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrIB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJlD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJlD.Mq1.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition OVw (kids : list (option jshape)) (BS : list blk) (p pb0 : Z) (PBS0 : list blk) (ts : Z) (TBS0 : list blk) (es0 : list oent) (KBS0 : list (list blk))
(m : word -> option byte) : Prop :=
obj_view rsegs S4F kids m BS p 1 pb0 PBS0 ts TBS0 es0 KBS0.

Section DcObj.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis OADDX : jo_object_add_ex_P HIx 0.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (T : TSet).
Variable kids : list (option jshape).
Let r : jroot := JRtree (Sobj kids).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stk (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Hypothesis IH : forall s', In (Some s') kids -> dcopy_spec HIx (JRtree s').

Notation dc_inv := (dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 m0 md0 LB BS lo D).
Notation dc_cell := (dc_cell sp).
Ltac dc_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact FRM0 | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact PUTX | exact PUT | clia ].

Variables (pb0 ts : Z) (PBS0 TBS0 : list blk) (es0 : list oent) (KBS0 : list (list blk)).
Notation OV := (OVw kids BS p pb0 PBS0 ts TBS0 es0 KBS0).

#[using="PUT PUTX OADDX fc r LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont IH"] Lemma dc_obj_loop :
forall (n j : nat) (e : oent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (kidsq : list (option jshape)) (CBS REM : list blk) (cj : list byte) (ee : word) (q : Z),
n = (length es0 - j)%nat -> nth_error es0 j = Some e ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj -> rw_cells rsegs mc (0x77c00 - 164) [C4 ee] ->
HEAPx A (BS ++ CBS ++ REM ++ LB) mc mdc -> OV mc ->
q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> jval rsegs S4F (Sobj kidsq) mc CBS q 1 -> okmax kidsq <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) x21 (wz (oe_a e)) (wz 0) s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26dec) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
induction n as [|n IHn]; intros until q; intros Hn Hj INV FS FRM1 CELL ERR HP OVc Hq DC JQ OK;
[pose proof (nth_error_lt _ _ _ Hj); lia|].
pose proof INV as (VM & PRES & ST & FR & G).
unfold Uzop.dc_frame in FR. unfold Uzop.dc_cell in CELL. pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu.
rewrite sdepth_Sobj in LOSu. pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.

destruct (obj_view_entry rsegs S4F kids mc BS p 1 pb0 PBS0 ts TBS0 es0 KBS0 j e OVc Hj) as (EA0 & EA8 & EIB & [pad ENT] & kj & bs & Hkj & Hbs & KOK).
pose proof OVc as (EBS & _ & HDR & _ & OT & LE1 & LE2 & _).
destruct OT as (_ & _ & OTE). destruct (OTE j e Hj) as (_ & _ & _ & _ & CSk & INk & KNk). clear OTE.
assert (INK : In (oe_k e, oe_kn e) BS) by (rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact INk).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INp1 : In (p, 48) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
destruct EIB as (ba & bn & Hbin & Hb1 & Hb2).
assert (INb : In (ba, bn) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hbin).
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP INb) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hbhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp - 72)] mc) as MU.

assert (CELLW : forall (A' : AS S4L HIx) L' ma mda mx, HEAPx A' (BS ++ L') ma mda -> jc_glob_P ma -> heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 ma ->
incl LB L' -> munch [(bv_unsigned sp - 80, bv_unsigned sp - 72)] ma mx -> wmono rsegs ma mx -> mem_inv rsegs mx ->
HEAPx A' (BS ++ L') mx mda /\ jc_glob_P mx /\ heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mx /\ agree_on rsegs (BS ++ L') ma mx).
{ intros A' L' ma mda mx HPx Gx PRx HiL MUx WMx MIx. split; [| split; [| split]].
- eapply (heap_frame S4L HIx); [exact HPx | | exact WMx | exact MIx]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HPx MUx). solve_frameW_with HPx.
- eapply jc_glob_P_outside; [exact Gx | exact MUx | exact WMx |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
- eapply presxD_trans; [exact PRx|]. eapply presxD_of_munch; [exact MUx | exact WMx |]. intros b Hb Hc Hd.
eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HPx | | clia | solve_clientW S4L HIx HPx | exact Hb | exact Hc].
intros bb Hbb. apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [apply in_or_app; left; exact Hbb | apply in_or_app; right; apply HiL; exact Hbb].
- eapply (agree_of_munch rsegs); [exact MUx | exact WMx |]. intros b bk Hb. cbn.
pose proof (heap_blk S4L HIx _ _ _ _ b bk HPx Hb) as (_ & _ & _ & Hbhi' & _). unfold_consts. lia. }

assert (NEXT : forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' t3' t4' t5' t6' : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : Model) (A2 : AS S4L HIx) (kids2 : list (option jshape)) (CBS2 REM2 : list blk) (cj2 : list byte) (e2 : word),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
dc_cell m2 cj2 -> rw_cells rsegs m2 (0x77c00 - 164) [C4 e2] ->
HEAPx A2 (BS ++ CBS2 ++ REM2 ++ LB) m2 md2 -> OV m2 ->
rw_cells rsegs m2 D [C8 (wz q)] -> jval rsegs S4F (Sobj kids2) m2 CBS2 q 1 -> okmax kids2 <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1' (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0' t1' t2' (wz p) (wz D) a0' a1' a2' a3' a4' a5' a6' a7'
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) x21' (wz (oe_a e)) (wz 0) s8 s9 s10 s11 t3' t4' t5' t6')
F2 (wz 0x26e3c) fc2 None m2 (seg_rom rsegs)) md2) T).
{ intros until e2. intros INV2 FS2 FRM2 CELL2 ERR2 HP2 OV2 DC2 JQ2 OK2.
pose proof INV2 as (VM2 & PRES2 & ST2 & FR2 & G2). unfold Uzop.dc_frame in FR2. unfold Uzop.dc_cell in CELL2.
destruct (obj_view_entry rsegs S4F kids m2 BS p 1 pb0 PBS0 ts TBS0 es0 KBS0 j e OV2 Hj) as (_ & _ & _ & [pad2 ENT2] & _).
pose proof OV2 as (_ & _ & HDR2 & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [] m2) as MU2.
stash OV2. stash JQ2. stash G2.
apply rz_evt; [exact MOK2|].
bstep. bstep.
destruct (nth_error es0 (S j)) as [e'|] eqn:Hj'.
-
destruct (obj_view_entry rsegs S4F kids m2 BS p 1 pb0 PBS0 ts TBS0 es0 KBS0 (S j) e' ltac:(unstash OV2; exact OV2) Hj') as (EA0' & _ & (ba' & bn' & Hbin' & Hb1' & Hb2') & _).
pose proof (heap_blk S4L HIx _ _ _ _ ba' bn' HP2 ltac:(apply in_or_app; left; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hbin')) as (_ & _ & _ & Hbhi2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi2.
rewrite (ohd_skipn es0 (S j)), Hj'. if_truex.
unstash OV2. unstash JQ2. unstash G2.
apply evt_RZ_done.
eapply (IHn (S j) e') with (kidsq := kids2) (CBS := CBS2) (REM := REM2);
first [ exact Hj' | exact INV2 | exact FS2 | exact FRM2 | exact CELL2 | exact ERR2 | exact HP2 | exact OV2 | exact Hq | exact DC2 | exact JQ2 | exact OK2
| pose proof (nth_error_lt _ _ _ Hj'); lia ].
-
rewrite (ohd_skipn es0 (S j)), Hj'. if_false. bstep.
unstash OV2. unstash JQ2. unstash G2.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in HDR2 as X. destruct X as [HDR6 _].
apply evt_RZ_done.
eapply (dc_tail0 HIx) with (d := JRtree (Sobj kids2)) (CBS := CBS2) (REM := REM2) (np := 48); dc_hyps.
all: first [ exact CELL2 | exact ERR2 | exact HP2 | exact INp | exact HDR6 | exact DC2 | exact Hq | exact FS2 | exact FRM2 | exact INV2 | idtac ].
+ cbn [copy_of]. eexists. split; [reflexivity|]. rewrite !sdepth_Sobj. lia.
+ cbn [jroot_rep]. split; [exact Hq | exact JQ2]. }

assert (ADD : forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : Model) (A2 : AS S4L HIx) (jso : Z) (vs : option jshape) (VBS REM2 : list blk) (e2 : word),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs m2 (bv_unsigned sp + -80) [C8 (wz jso)] -> rw_cells rsegs m2 490332 [C4 e2] ->
HEAPx A2 (VBS ++ BS ++ CBS ++ REM2 ++ LB) m2 md2 -> OV m2 ->
rw_cells rsegs m2 D [C8 (wz q)] -> jval rsegs S4F (Sobj kidsq) m2 CBS q 1 ->
jopt rsegs S4F vs m2 VBS jso -> odep vs <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1' (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0' t1' t2' (wz p) (wz D) a0' a1' a2' a3' a4' a5' a6' a7'
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) (wz (oe_k e)) (wz (oe_a e)) (wz 0) s8 s9 s10 s11 t3' t4' t5' t6')
F2 (wz 0x26e20) fc2 None m2 (seg_rom rsegs)) md2) T).
{ intros until e2. intros INV2 FS2 FRM2 CELL2 ERR2 HP2 OV2 DC2 JQ2 JOB2 ODEP.
pose proof INV2 as (VM2 & PRES2 & ST2 & FR2 & G2). unfold Uzop.dc_frame in FR2.
pose proof OV2 as (_ & _ & _ & _ & OT2 & _). destruct OT2 as (_ & _ & OTE2). destruct (OTE2 j e Hj) as (_ & _ & _ & _ & CSk2 & _). clear OTE2.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [] m2) as MU2.
stash OV2. stash JQ2. stash JOB2. stash G2. stash CSk2.
apply rz_evt; [exact MOK2|].
bstep. bstep. bstep. bstep. bstep.
unstash OV2. unstash JQ2. unstash JOB2. unstash G2. unstash CSk2.
apply evt_RZ_done.
pose proof OADDX as OA. unfold jo_object_add_ex_P, jo_object_add_ex_stmt in OA.
eapply OA with (OBS := CBS) (VBS := VBS) (LB := BS ++ REM2 ++ LB) (lo := lo) (kids := kidsq) (vs := vs) (ks := oe_ks e) (kn := oe_kn e); clear OA;
[ | exact G2 | exact JQ2 | exact JOB2 | apply in_or_app; left; exact INK | exact CSk2 | exact KNk | exact FRM2 | reflexivity | reflexivity | reflexivity | reflexivity | ].
{ unfold jo_pre. cbn [hl_segs hl_tp S4L]. rewrite !(unsigned_lit (bv_unsigned sp + -80)) by lia.
split; [eapply (heap_perm S4L HIx); [exact HP2 | perm] |]. split; [exact ST2|]. split; [clia|]. split; [lia|].
split; [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity|]. split; [clia|].
split; [exact ERR2|]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
intros ms3 md3 m3 r3 (RS3 & VM3 & ST3 & HPR3 & [e3 ERR3]) G3 RES3.
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp hl_volatile S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
change (490496 - 164) with 490332 in ERR3.
apply (heap_presx_rw_cells _ _ _ _ _ _ _ _ HPR3) in FR2; [| left; cbn; lia].
apply (heap_presx_rw_cells _ _ _ _ _ _ _ _ HPR3) in CELL2; [| left; cbn; lia].
apply (heap_presx_rw_cells _ _ _ _ _ _ _ _ HPR3) in DC2; [| left; cbn; lia].
cbn [hl_segs S4L] in FR2, CELL2, DC2.
pose proof (obj_view_agree rsegs S4F _ _ _ _ _ _ _ _ _ _ _ _ OV2 ltac:(eapply (agree_of_heap_presx rsegs S4L); [exact HPR3 | reflexivity | incl_tac]) : OV m3) as OV3.
assert (PRES3 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m3).
{ eapply presxD_trans; [exact PRES2|]. apply presx_presxD. eapply heap_presx_weaken; [exact HPR3 | lia | incl_tac | intros a Xa; exact Xa]. }
pose proof (wmono_refl rsegs m3) as WM3. pose proof (munch_refl [] m3) as MU3.
destruct RES3 as [(-> & A3 & OBS3 & kids3 & JQ3 & HP3 & LEN3 & OK3) | (-> & A3 & REM3 & JQ3 & JOB3 & HP3)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
stash JQ3. stash OV3. stash G3.
reenter MOK3.
bstep. if_false.
unstash JQ3. unstash OV3. unstash G3.
apply evt_RZ_done.
eapply (NEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 kids3 OBS3 REM2 _ e3);
[ split; [eapply model_vm_only_trans; [exact VM2 | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR2 | exact G3]]]]
| eapply fsaved_trans; [exact FS2 | exact FS3] | apply FRM3; exact FRM2
| unfold Uzop.dc_cell; apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL2; [exact CELL2 | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity]
| exact ERR3 | eapply (heap_perm S4L HIx); [exact HP3 | perm] | exact OV3 | exact DC2 | exact JQ3 | lia ].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
stash JQ3. stash JOB3. stash G3.
reenter MOK3.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bstep. if_true. bstep.
unstash JQ3. unstash JOB3. unstash G3.
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := Sobj kidsq) (CBS := CBS) (CBSc := VBS) (REM := REM3 ++ REM2); dc_hyps.
all: first [ exact ERR3 | exact DC2 | exact Hq | exact JQ3
| eapply fsaved_trans; [exact FS2 | exact FS3] | apply FRM3; exact FRM2
| eapply (heap_perm S4L HIx); [exact HP3 | perm]
| split; [eapply model_vm_only_trans; [exact VM2 | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR2 | exact G3]]]]
| idtac ].
+ unfold Uzop.dc_cell. apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL2; [exact CELL2 | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
+ destruct vs as [s''|]; cbn [jopt] in JOB3.
* right; left. destruct JOB3 as [Hj3 J3]. split; [exact Hj3 | exists s''; exact J3].
* left. exact JOB3. }

stash G. stash OVc. stash JQ. stash KOK. stash CSk.
apply rz_evt; [exact MOK|].
bstep. bstep. bstepz. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
unstash G. unstash OVc. unstash JQ. unstash KOK.
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ m1 HP G PRES ltac:(incl_tac) MU WM MI) as (HP1 & G1 & PRES1 & AG1).
pose proof (obj_view_agree rsegs S4F _ _ _ _ _ _ _ _ _ _ _ _ OVc ltac:(eapply agree_on_incl; [exact AG1 | incl_tac]) : OV m1) as OV1.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ JQ AG1 ltac:(incl_tac)) as JQ1.
assert (Hibs : incl bs BS).
{ rewrite EBS. intros b Hb. apply in_or_app; left. right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb]. }
destruct kj as [s'|].
-
destruct KOK as [Hv J'].
destruct (jval_root_in rsegs S4F _ _ _ _ _ J') as (nv & INv & Hnv).
assert (INv1 : In (oe_v e, nv) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; apply Hibs; exact INv).
pose proof (heap_blk S4L HIx _ _ _ _ (oe_v e) nv HP INv1) as (_ & Hval & Hvlo & Hvhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi.
if_falsex. bstep. bstep. bstep. bstep. bstep. bstep.

pose proof (concat_nth_split KBS0 j bs Hbs) as EK.
set (LBc := ((p, 48) :: TBS0 ++ concat (firstn j KBS0) ++ concat (skipn (S j) KBS0)) ++ PBS0 ++ CBS ++ REM ++ LB).
assert (PERMc : Permutation (BS ++ CBS ++ REM ++ LB) (bs ++ LBc)) by (unfold LBc; rewrite EBS, EK; perm).
pose proof (kdepth_in kids s' (nth_error_In _ _ Hkj)) as DEP.
assert (OKK : okmax kids = kdepth kids) by (pose proof (sdepth_Sobj kids); pose proof (sdepth_obj kids); lia).
apply evt_RZ_done.
pose proof (IH s' (nth_error_In _ _ Hkj)) as REC. unfold dcopy_spec in REC.
eapply REC with (BS := bs) (LB := LBc) (lo := lo) (p := oe_v e) (D := bv_unsigned sp + -80); clear REC;
[ eapply (heap_perm S4L HIx); [exact HP1 | exact PERMc]
| cbn [jroot_rep]; split; [exact Hv | eapply (jval_agree rsegs S4F); [exact J' | exact AG1 | intros b Hb; apply in_or_app; left; apply Hibs; exact Hb]]
| discriminate | exact G1 | exact CELL
| rewrite unsigned_lit by lia; lia | lia | apply mod16_mod8; [exact SPA | reflexivity]
| rewrite unsigned_lit by lia; exact ST | clia
| rewrite unsigned_lit by lia; cbn [rdepth]; unfold dc_stk, REC_P, DC_C; pose proof (sdepth_nonneg s'); nia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | exact FRM1 | reflexivity | reflexivity | reflexivity | ].
intros ms3 md3 m3 rv3 (RS3 & VM3 & ST3 & HPR3 & [e3 ERR3]) G3 JR3 RES3.
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp hl_volatile S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.

assert (PRES3 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m3).
{ eapply presxD_trans; [exact PRES1|]. apply presx_presxD.
eapply heap_presx_weaken; [eapply (presxD_presx S4L HIx) with (SP' := bv_unsigned sp); [exact HPR3 | eapply (heap_perm S4L HIx); [exact HP1 | exact PERMc] | apply incl_refl | lia | lia | clia] | lia | | intros b Xb; exact Xb].
intros b Hb. apply (Permutation_in _ PERMc). apply in_app_or in Hb; destruct Hb as [Hb|Hb]; in_find Hb. }
assert (AG3 : agree_on rsegs (BS ++ CBS ++ REM ++ LB) m1 m3).
{ eapply (presxD_agree S4L HIx); [exact HPR3 | eapply (heap_perm S4L HIx); [exact HP1 | exact PERMc] | | apply incl_refl | clia].
intros b Hb. apply (Permutation_in _ PERMc). exact Hb. }
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia | cbn; lia].
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia | cbn; lia].
cbn [hl_segs S4L] in FR, DC.
pose proof (obj_view_agree rsegs S4F _ _ _ _ _ _ _ _ _ _ _ _ OV1 ltac:(eapply agree_on_incl; [exact AG3 | incl_tac]) : OV m3) as OV3.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ JQ1 AG3 ltac:(incl_tac)) as JQ3.
clear CELL MU WM MI MOK HP1 G1 PRES1 AG1 J' OV1 JQ1 OVc JQ HP G PRES.
pose proof (wmono_refl rsegs m3) as WM. pose proof (munch_refl [] m3) as MU.
stash JR3. stash OV3. stash JQ3. stash G3.
destruct RES3 as [(-> & A3 & d3 & q3 & CBS3 & REM3 & CO3 & Hq3 & CELL3 & JD3 & HP3) | (-> & A3 & q3 & CBS3 & REM3 & CELL3 & FRES3 & HP3)]; cbn [hl_segs S4L] in CELL3.
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
stash JD3. stash CO3.
reenter MOK3.
bstep. if_false.
unstash JD3. unstash CO3. unstash JR3. unstash OV3. unstash JQ3. unstash G3.
destruct CO3 as (s3' & -> & DEP3). cbn [jroot_rep] in JD3. destruct JD3 as [_ JD3].
apply evt_RZ_done.
eapply (ADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 q3 (Some s3') CBS3 (REM3 ++ REM) e3);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]]
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1
| exact CELL3 | exact ERR3 | eapply (heap_perm S4L HIx); [exact HP3 | unfold LBc; rewrite EBS, EK; perm]
| exact OV3 | exact DC | exact JQ3 | cbn [jopt]; split; [exact Hq3 | exact JD3] | cbn [odep]; lia ].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
stash FRES3.
reenter MOK3.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bstep. if_true. bstep.
unstash FRES3. unstash JR3. unstash JQ3. unstash G3.
apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz q3))]) in CELL3; [| cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := Sobj kidsq) (CBS := CBS) (CBSc := CBS3) (REM := REM3 ++ REM); dc_hyps.
all: first [ exact CELL3 | exact ERR3 | exact DC | exact Hq | exact JQ3 | exact FRES3
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1
| eapply (heap_perm S4L HIx); [exact HP3 | unfold LBc; rewrite EBS, EK; perm]
| split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]] ].
-
destruct KOK as [Ev Ebs]. rewrite Ev. if_true.
apply evt_RZ_done.
eapply (ADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 mdc A 0 None [] REM ee);
[ split; [exact VM | split; [exact PRES1 | split; [exact ST | split; [exact FR | exact G1]]]] | exact FS | exact FRM1
| exact CELL | exact ERR | cbn [app]; exact HP1 | exact OV1 | exact DC | exact JQ1 | split; reflexivity | cbn; exact OK0 ].
Qed.
End DcObj.

Section DcObj2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis OADDX : jo_object_add_ex_P HIx 0.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (T : TSet).
Variable kids : list (option jshape).
Let r : jroot := JRtree (Sobj kids).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stk (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.
Hypothesis IH : forall s', In (Some s') kids -> dcopy_spec HIx (JRtree s').

Notation dc_inv := (dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 m0 md0 LB BS lo D).
Notation dc_cell := (dc_cell sp).
Ltac dc_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact FRM0 | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact PUTX | exact PUT | exact OADDX | exact IH | clia ].

#[using="PUT PUTX OADDX fc LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont IH"] Lemma dc_obj :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q : Z) (CBS : list blk) (cj : list byte) (e : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj -> rw_cells rsegs mc (0x77c00 - 164) [C4 e] ->
HEAPx A (BS ++ CBS ++ LB) mc mdc -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> scopy S4L S4F r mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) (wz 0) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26db4) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until e. intros INV FS FRM1 CELL ERR HP Hq DC SC. pose proof INV as (VM & PRES & ST & FR & G).
unfold Uzop.dc_frame in FR. unfold Uzop.dc_cell in CELL. pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu.
rewrite sdepth_Sobj in LOSu. pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
cbn [scopy r] in SC.

destruct JR0 as [Hp J0].
assert (J : jval rsegs S4F (Sobj kids) mc BS p 1).
{ eapply (jval_agree rsegs S4F); [exact J0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [exact PRES | exact HP | incl_tac | incl_tac | clia]. }
clear J0.
assert (POS : forall a n, In (a, n) BS -> 0 < a /\ a mod 16 = 0).
{ intros a n Hin. pose proof (heap_blk S4L HIx _ _ _ _ a n HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & Hlo & _). split; [exact Hlo | exact Hal]. }
destruct (jval_obj_view rsegs S4F kids mc BS p 1 J POS) as (pb0 & PBS0 & ts & TBS0 & es0 & KBS0 & OV).
pose proof OV as (EBS & _ & HDR & _ & _ & LE1 & LE2 & _).
destruct (obj_view_tbl rsegs S4F _ _ _ _ _ _ _ _ _ _ _ OV) as [_ INt].
pose proof (obj_view_head rsegs S4F _ _ _ _ _ _ _ _ _ _ _ OV) as HEAD.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INp1 : In (p, 48) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ ts 56 HP ltac:(apply in_or_app; left; exact INt)) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash OV. stash SC. stash G.
apply rz_evt; [exact MOK|].
bstep. bstep. bstep. if_false. bstep. bstep. if_false.
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x26dc8) _ _ _ _) => idtac end.
bstep. bstep. bstep.
replace (ohd es0) with (ohd (skipn 0 es0)) by reflexivity. rewrite (ohd_skipn es0 0).
destruct (nth_error es0 0%nat) as [e0|] eqn:He0.
-
destruct (obj_view_entry rsegs S4F kids mc BS p 1 pb0 PBS0 ts TBS0 es0 KBS0 0 e0 ltac:(unstash OV; exact OV) He0) as (EA0 & _ & (ba & bn & Hbin & Hb1 & Hb2) & _).
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(apply in_or_app; left; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hbin)) as (_ & _ & _ & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
if_falsex. bstep. bstep. bstep.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB. rewrite (unsigned_lit D) by lia. rewrite (ub_land7 D DAL).
unstash OV. unstash SC. unstash G.
apply evt_RZ_done.
eapply (dc_obj_loop HIx PUT PUTX OADDX) with (kids := kids) (n := length es0) (j := 0%nat) (e := e0) (kidsq := []) (CBS := CBS) (REM := []) (es0 := es0) (m0 := m0) (md0 := md0) (F := F) (fc := fc); dc_hyps.
all: try first [ exact CELL | exact ERR | exact DC | exact Hq | exact FS | exact FRM1 | exact INV | exact OV | exact SC | exact He0
| eapply (heap_perm S4L HIx); [exact HP | perm] ].
all: first [ cbn [jroot_rep]; split; [exact Hp | eapply obj_view_jval; exact OV] | lia | cbn; exact OK0 ].
-
if_true.
unstash OV. unstash SC. unstash G.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in HDR as X. destruct X as [HDR6 _].
apply evt_RZ_done.
eapply (dc_tail0 HIx) with (d := JRtree (Sobj [])) (CBS := CBS) (REM := []) (np := 48); dc_hyps.
all: first [ exact CELL | exact ERR | exact INp | exact HDR6 | exact DC | exact Hq | exact FS | exact FRM1 | exact INV
| eapply (heap_perm S4L HIx); [exact HP | perm]
| idtac ].
all: first [ cbn [jroot_rep]; split; [exact Hq | exact SC]
| cbn [jroot_rep]; split; [exact Hp | eapply obj_view_jval; exact OV]
| cbn [copy_of]; eexists; split; [reflexivity|]; rewrite !sdepth_Sobj; cbn; lia ].
Qed.
End DcObj2.

#[using="Type"] Lemma dc_arm_obj : forall HIx, put_stmt_P HIx -> jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P -> jo_object_add_ex_P HIx 0 -> dc_arm HIx Sobj.
Proof.
intros HIx PUT PUTX OADDX. unfold dc_arm.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS lo p D T kids LO LOS SPA HT RA FRM SPD DHI DAL JR Kont IH. intros.
eapply (dc_obj HIx PUT PUTX OADDX ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS lo p D T kids); try eassumption. discriminate.
Qed.

Section DcInst.
Let NEWOBJ_P : forall HIx : heap_iface S4L, jo_new_object_P HIx := fun HIx => Ujal.json_object_new_object_cps HIx.
Let OADDX_P : forall HIx : heap_iface S4L, jo_object_add_ex_P HIx 0 :=
fun HIx => U9PQ.json_object_object_add_ex_cps HIx (json_object_put_P HIx) (U2Ei.hash_ok HIx).

#[using="NEWOBJ_P OADDX_P"] Theorem deep_copy_P_closed : forall HIx : heap_iface S4L,
hi_top S4L HIx < 2^63 -> jo_deep_copy_stmt S4L HIx S4F jc_glob_P DEEP_COPY_P SH_ENTRY_P DEEP_COPY_STK0 REC_P.
Proof.
intros HIx HT63.
exact (deep_copy_P HIx (json_object_put_P HIx) (put_xleaf_P HIx) set_last_err_P HT63 (NEWOBJ_P HIx)
(dc_arm_obj HIx (json_object_put_P HIx) (put_xleaf_P HIx) (OADDX_P HIx))).
Qed.

#[using="NEWOBJ_P OADDX_P"] Theorem deep_copy_P_inst : forall HIx : heap_iface S4L,
hi_top S4L HIx < 2^62 -> jo_deep_copy_stmt S4L HIx S4F jc_glob_P 0x26cd0 0x26968 (16 + 112 + 10528) 112.
Proof. intros HIx H62. apply deep_copy_P_closed. lia. Qed.
End DcInst.

End RC__1.
