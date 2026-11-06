(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QEQM QRjH QzWc QfOM Qc8V QgTW Qy2A QPC3 QHnV QCcH QfLs Q0Ek Qtgi QC8c QPZI Qu4M QkMG QG8z QLbz Qa8x Q2Sr Qzoi Qb4w QTd1 Qyk8 Q5CI QWt1 QuXw Qjal Q9PQ QD6K QtfO QLAQ QXKA QU48 Q2Ei QGEL QFw3 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QEQM.
Import QRjH.
Import QzWc QfOM Qc8V.
Import QgTW.Mq1.
Import Qy2A QPC3.
Import QHnV QCcH QfLs Q0Ek Qtgi.
Import QC8c.Mq0 QPZI.Mq0 QPZI.Mq4 Qu4M.Mq0.
Import QkMG.
Import QG8z QLbz Qa8x.Mq3 Q2Sr Qzoi.Mq0 Qb4w Qzoi QTd1 QTd1.Mq0.
Import Qyk8.
Import Q5CI QWt1 QuXw Qjal Q9PQ.
Import QD6K.
Import QtfO QLAQ QXKA QU48.
Import Q2Ei.
Import QGEL QFw3.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Theorem json_tokener_parse_P : forall HIx : heap_iface S4L, tokparse_stmt_P HIx.
Proof.
intros HIx.
exact (tokparse_P_cps HIx uselocale_ok errno_location_ok (duplocale_ok HIx) (newlocale_ok HIx) (freelocale_ok HIx)
memmove_spec (strdup_cps HIx)
(json_object_array_add_cps HIx) (json_object_array_shrink_cps HIx) (oadd_ok HIx)
(json_object_new_object_cps HIx) (json_object_new_array_cps HIx)
(HC_null HIx) (HC_bool HIx) (HC_number HIx) (HC_inf HIx)).
Qed.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrIB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdgq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJlD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJlD.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition dc_arm (HIx : heap_iface S4L) (sh : list (option jshape) -> jshape) : Prop :=
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (T : TSet) (kids : list (option jshape)),
alloc_ceiling <= lo -> lo <= bv_unsigned sp - dc_stk (rdepth (JRtree (sh kids))) -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= hi_top S4L HIx -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
bv_unsigned sp <= D -> D + 8 <= hi_top S4L HIx -> D mod 8 = 0 ->
jroot_rep S4L S4F (JRtree (sh kids)) m0 BS p ->
(forall ms' md' m' rv,
jf_postD S4L D ra sp gp (Z_to_bv 64 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F (JRtree (sh kids)) m' BS p -> dc_res HIx (JRtree (sh kids)) BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T) ->
(forall s', In (Some s') kids -> dcopy_spec HIx (JRtree s')) ->
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q : Z) (CBS : list blk) (jk cj : list byte) (e : word),
dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 md0 LB BS lo D mc mdc -> fsaved F F1 -> frm0 fc1 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell sp mc cj -> rw_cells rsegs mc (0x75e70 - 164) [C4 e] ->
HEAP S4L HIx A (BS ++ CBS ++ LB) mc mdc -> q <> 0 -> rw_cells rsegs mc D [C8 (Z_to_bv 64 q)] -> scopy S4L S4F (JRtree (sh kids)) mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x75e70) t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 D) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SH_ENTRY_P) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x25970) fc1 None mc (seg_rom rsegs)) mdc) T.

#[using="Type"] Lemma dc_arm_arr : forall HIx, put_stmt_P HIx -> jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P -> dc_arm HIx Sarr.
Proof.
intros HIx PUT PUTX. unfold dc_arm.
intros ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS lo p D T kids LO LOS SPA HT RA FRM SPD DHI DAL JR Kont IH. intros.
eapply (dc_arr HIx PUT PUTX ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS lo p D T kids LO LOS SPA HT SPD DAL ltac:(discriminate) JR Kont IH); eassumption.
Qed.

Section DcLeaf.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis LASTERR : set_last_err_spec_P.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
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
jf_postD S4L D ra sp gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Hypothesis LEAF : match r with JRtree (Sobj _) | JRtree (Sarr _) | JRnull => False | _ => True end.

Ltac dc_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact FRM0 | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact HT63 | exact LASTERR | exact PUTX | exact PUT | clia ].

#[using="LASTERR HT63 fc LO LOS SPA HT SPD DHI DAL NN JR0 Kont LEAF"] Lemma dc_leaf :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q : Z) (CBS : list blk) (jk cj : list byte) (e : word),
dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 md0 LB BS lo D mc mdc -> fsaved F F1 -> frm0 fc1 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell sp mc cj -> rw_cells rsegs mc (0x75e70 - 164) [C4 e] ->
HEAPx A (BS ++ CBS ++ LB) mc mdc -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> scopy S4L S4F r mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) (wz 1) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x25970) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until e. intros INV FS FRM1 FRJ CELL ERR HP Hq DC SC. pose proof INV as (VM & PRES & ST & FR & G).
pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg). unfold_consts. word_range sp SPR.
change (0x75e70 - 164) with 482764 in ERR.
assert (JR : jroot_rep S4L S4F r mc BS p).
{ eapply jroot_rep_agree; [exact JR0 | | apply incl_refl]. eapply (presxD_agree S4L HIx); [exact PRES | exact HP | incl_tac | incl_tac | clia]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.

assert (GO : forall (ty tojs pb : Z) (d : jroot) (np : Z),
rw_cells rsegs mc p (jhdr_cells ty 1 tojs pb 0 0) -> (ty = 1 \/ ty = 2 \/ ty = 3 \/ ty = 6) -> In (p, np) BS -> 48 <= np ->
copy_of r d -> jroot_rep S4L S4F d mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) (wz 1) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x25970) fc1 None mc (seg_rom rsegs)) mdc) T).
{ intros ty tojs pb d np HDR TY INp Hnp CO JD.
pose proof (heap_blk S4L HIx _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof HDR as HDR0. unfold jhdr_cells in HDR.
stash JD. stash CO. stash G. stash JR.
apply rz_evt; [exact MOK|].
step. rewrite (sx32_small ty) by lia. step. step. if_falsex. step. step. if_truex.
unstash JD. unstash CO. unstash G. unstash JR.
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |].
- destruct sh as [|[|]| |h|kids|kids]; try (exfalso; exact LEAF).
+ apply evt_RZ_done. eapply (dc_tail0 HIx) with (np := np) (REM := []) (CBS := CBS) (d := d) (q := q) (A := A); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact INp | exact Hnp | exact HDR0 | exact CO | exact Hq | exact DC | exact JD
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV ].
+
cbn [jroot_rep] in JR. destruct JR as [Hp J]. destruct J as (pb0 & PBS & REST & EBS & OPB & bits & ud & udn & uds & ER & HU & H & HC). subst REST.
cbn [scopy] in SC. destruct SC as [-> [bits' QX]].
apply evt_RZ_done. eapply (dc_tail_ud HIx) with (REM := []) (udn := udn) (uds := uds) (q := q) (A := A) (ud := ud); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact H | exact HC | exact HU | exact Hq | exact DC | exact QX | reflexivity
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV
| rewrite EBS; left; reflexivity
| rewrite EBS; right; left; reflexivity ].
+ apply evt_RZ_done. eapply (dc_tail0 HIx) with (np := np) (REM := []) (CBS := CBS) (d := d) (q := q) (A := A); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact INp | exact Hnp | exact HDR0 | exact CO | exact Hq | exact DC | exact JD
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV ].
+ apply evt_RZ_done. eapply (dc_tail0 HIx) with (np := np) (REM := []) (CBS := CBS) (d := d) (q := q) (A := A); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact INp | exact Hnp | exact HDR0 | exact CO | exact Hq | exact DC | exact JD
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV ].
+ apply evt_RZ_done. eapply (dc_tail0 HIx) with (np := np) (REM := []) (CBS := CBS) (d := d) (q := q) (A := A); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact INp | exact Hnp | exact HDR0 | exact CO | exact Hq | exact DC | exact JD
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV ].
- apply evt_RZ_done. eapply (dc_tail0 HIx) with (np := np) (REM := []) (CBS := CBS) (d := d) (q := q) (A := A); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact INp | exact Hnp | exact HDR0 | exact CO | exact Hq | exact DC | exact JD
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV ].
- apply evt_RZ_done. eapply (dc_tail0 HIx) with (np := np) (REM := []) (CBS := CBS) (d := d) (q := q) (A := A); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact INp | exact Hnp | exact HDR0 | exact CO | exact Hq | exact DC | exact JD
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV ]. }

cbn [scopy] in SC.
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |]; cbn [jroot_rep] in JR.
- destruct JR as [Hp J]. destruct sh as [|[|]| |h|kids|kids]; try (exfalso; exact LEAF); destruct J as (pb0 & PBS & REST & EBS & OPB & J).
+ destruct J as (b & junk & ER & H). subst REST.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
eapply (GO JT_BOOLEAN) with (d := JRtree Sbool) (np := 48); [exact H6 | unfold JT_BOOLEAN; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC]].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
+ destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].

pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; rewrite EBS; left; reflexivity)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
destruct SC as [-> [bits' QX]].
stash G. stash HC. stash QX.
apply rz_evt; [exact MOK|].
step. rewrite (sx32_small JT_DOUBLE) by (unfold JT_DOUBLE; lia). step. step. unfold JT_DOUBLE. if_false. step. step. if_true.
unstash G. unstash HC. unstash QX.
apply evt_RZ_done. eapply (dc_tail_ud HIx) with (REM := []) (udn := udn) (uds := uds) (q := q) (A := A) (ud := ud); dc_hyps.
all: first [ exact FS | exact FRM1 | exact CELL | exact FRJ | exact ERR | exact H | exact HC | exact HU | exact Hq | exact DC | exact QX | reflexivity
| eapply (heap_perm S4L HIx); [exact HP | perm] | exact INV
| rewrite EBS; left; reflexivity
| rewrite EBS; right; left; reflexivity ].
+ destruct J as (bits & ER & HS & H). subst REST.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
eapply (GO JT_DOUBLE) with (d := JRtree (Sdouble false)) (np := 48); [exact H6 | unfold JT_DOUBLE; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC]].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
+ destruct J as (cty & v & junk & ER & CTY & H). subst REST.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
eapply (GO JT_INT) with (d := JRtree Sint) (np := 56); [exact H6 | unfold JT_INT; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC]].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
+ destruct h.
* destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HD). subst REST.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := 56); [exact H6 | unfold JT_STRING; lia | rewrite EBS; left; reflexivity | lia | | cbn [jroot_rep]; split; [exact Hq | exact SC]].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
* destruct J as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := str_objsize len); [exact H6 | unfold JT_STRING; lia | rewrite EBS; left; reflexivity | unfold str_objsize; lia | | cbn [jroot_rep]; split; [exact Hq | exact SC]].
cbn [copy_of]. eexists. split; [reflexivity | cbn; lia].
- destruct JR as (Hp & Htojs & pb0 & PBS & bits & EBS & OPB & H).
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X. destruct X as [H6 _].
destruct SC as [ECBS XD].
eapply (GO JT_DOUBLE) with (d := JRdblx tojsx) (np := 48); [exact H6 | unfold JT_DOUBLE; lia | rewrite EBS; left; reflexivity | lia | reflexivity | cbn [jroot_rep]; split; [exact Hq | split; [exact Htojs | exact XD]]].
- destruct JR as (Hp & pb0 & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & ALT).
assert (H6 : rw_cells rsegs mc p (jhdr_cells JT_STRING 1 (fn_str_to_json_string S4F) pb0 0 0)).
{ destruct ALT as [(_ & _ & _ & junk & H) | (_ & pd & pdn & junk & junk2 & _ & _ & H & _)];
(apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in H as X; destruct X as [H6 _]; exact H6). }
eapply (GO JT_STRING) with (d := JRtree (Sstr false)) (np := 48 + cap); [exact H6 | unfold JT_STRING; lia | rewrite EBS; left; reflexivity | lia | reflexivity | cbn [jroot_rep]; split; [exact Hq | exact SC]].
Qed.
End DcLeaf.

Section DcAll.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis LASTERR : set_last_err_spec_P.
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis DCOBJ : dc_arm HIx Sobj.

#[using="PUT PUTX LASTERR HT63 DCOBJ"] Lemma dcopy_step : forall r,
(forall kids s', r = JRtree (Sobj kids) \/ r = JRtree (Sarr kids) -> In (Some s') kids -> dcopy_spec HIx (JRtree s')) ->
r <> JRnull -> dcopy_spec HIx r.
Proof.
intros r IH NN. unfold dcopy_spec. intros until errv. intros HP JR _ G DC SPD DHI DAL ST LO LOS SPA HT ERR TP RA FRM A0 A4 A5 K.
subst a0 a4 a5 tp.
eapply (dc_b0 HIx) with (r := r) (BS := BS) (LB := LB) (lo := lo) (D := D) (m0 := m) (md0 := md);
try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact HP | exact G | exact DC | exact ST | exact ERR | exact K | exact JR | exact NN | exact LO | exact LOS | exact SPA | exact HT | exact RA | exact FRM | exact SPD | exact DHI | exact DAL ].
intros until e. intros INV FS FRM1 FRJ CELL ERR1 HP1 Hq DC1 SC.
destruct r as [|sh|tojsx|]; [exfalso; exact (NN eq_refl) | | |].
- destruct sh as [|u| |h|kids|kids].
+ eapply (dc_leaf HIx) with (r := JRtree Sbool); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | exact I | eassumption | discriminate ].
+ eapply (dc_leaf HIx) with (r := JRtree (Sdouble u)); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | exact I | eassumption | discriminate ].
+ eapply (dc_leaf HIx) with (r := JRtree Sint); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | exact I | eassumption | discriminate ].
+ eapply (dc_leaf HIx) with (r := JRtree (Sstr h)); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | exact I | eassumption | discriminate ].
+ pose proof DCOBJ as OB. unfold dc_arm in OB.
eapply OB with (kids := kids); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | eassumption ].
intros s' Hin. eapply IH; [left; reflexivity | exact Hin].
+ eapply (dc_arm_arr HIx PUT PUTX) with (kids := kids); try first [ exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | eassumption ].
intros s' Hin. eapply IH; [right; reflexivity | exact Hin].
- eapply (dc_leaf HIx) with (r := JRdblx tojsx); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | exact I | eassumption | discriminate ].
- eapply (dc_leaf HIx) with (r := JRstrx); try first [ exact PUT | exact PUTX | exact LASTERR | exact HT63 | exact INV | exact FRM | exact FS | exact FRM1 | exact FRJ | exact CELL | exact ERR1 | exact HP1 | exact Hq | exact DC1 | exact SC | exact K | exact JR | exact I | eassumption | discriminate ].
Qed.

#[using="PUT PUTX LASTERR HT63 DCOBJ"] Theorem dcopy_all : forall r, r <> JRnull -> dcopy_spec HIx r.
Proof.
assert (TREE : forall s, dcopy_spec HIx (JRtree s)).
{ induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; apply dcopy_step; try discriminate;
intros kids0 s' [E|E] Hin; try discriminate; injection E as <-; apply IHk; exact Hin. }
intros r NN. destruct r as [|s|t|].
- exfalso; exact (NN eq_refl).
- apply TREE.
- apply dcopy_step; [intros kids s' [E|E]; discriminate | exact NN].
- apply dcopy_step; [intros kids s' [E|E]; discriminate | exact NN].
Qed.
End DcAll.

Definition DEEP_COPY_P : Z := 0x258a0.
Definition DEEP_COPY_STK0 : Z := 16 + REC_P + DC_C.

Section DeepCopyTop.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis LASTERR : set_last_err_spec_P.
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis DCOBJ : dc_arm HIx Sobj.

#[using="PUT PUTX LASTERR HT63 DCOBJ"] Lemma deep_copy_P_main :
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (lo p D : Z) (r : jroot) (errv : word) (m1 : word -> option byte),
HEAPx A (BS ++ LB) m md -> stk rsegs m1 lo (bv_unsigned sp + -16) -> alloc_ceiling <= lo ->
lo <= bv_unsigned sp - (16 + 112 + 10528 + 112 * rdepth r) -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m1 482764 [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
jc_glob_P m -> jroot_rep S4L S4F r m BS p -> r <> JRnull ->
rw_cells rsegs m1 D [C8 (wz 0)] -> bv_unsigned sp <= D -> D + 8 < 2^63 -> D + 8 <= hi_top S4L HIx -> D mod 8 = 0 -> frm0 fc ->
(forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p ->
( (rv = 0 /\ exists A' (d : jroot) (q : Z) CBS REM,
copy_of r d /\ q <> 0 /\ rw_cells rsegs m' D [C8 (Z_to_bv 64 q)] /\ jroot_rep S4L S4F d m' CBS q /\
HEAPx A' (BS ++ CBS ++ REM ++ LB) m' md')
\/ (rv = 2^64 - 1 /\ exists A' REM, rw_cells rsegs m' D [C8 (Z_to_bv 64 0)] /\ HEAPx A' (BS ++ REM ++ LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
mem_inv rsegs m1 -> wmono rsegs m m1 -> munch [(bv_unsigned sp - 16, bv_unsigned sp); (482764, 482768)] m m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
evt rsegs (RZ rsegs md T)
(MS (mkR ra (wz (bv_unsigned sp + -16)) gp (wz 0x75e70) t0 t1 t2 s0 s1 (wz p) (wz D) (wz SH_ENTRY_P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (if bv_eqb (wz p) (wz 0) then wz 0x258c0 else wz 0x258b0) fc None m1 (seg_rom rsegs)).
Proof.
intros until m1. intros HP ST LO LOS SPA HT ERR RA G JR NN DC SPD D63 DHI DAL FRM K MI WM MU FR.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
unfold_consts. word_range sp SPR.
destruct (jroot_rep_root_in S4L S4F r m BS p JR NN) as (np & INp & Hnp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
if_falsex. step. if_falsex. step. step. step. if_true. step. step. unfold SH_ENTRY_P at 1. if_true. step. step. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (HP2 : HEAPx A (BS ++ LB) m2 md) by heap_now S4L HIx HP MU WM MI.
assert (G2 : jc_glob_P m2) by (eapply jc_glob_P_munch; [exact G | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia).
assert (PRES2 : heap_presxD S4L D LB (bv_unsigned sp) m m2).
{ eapply presxD_of_munch; [exact MU | exact WM |]. intros a Ha Hc Hd.
eapply (client_outside S4L HIx) with (LB0 := LB) (SP := bv_unsigned sp); [exact HP | incl_tac | clia | solve_clientW S4L HIx HP | exact Ha | exact Hc]. }
assert (JR2 : jroot_rep S4L S4F r m2 BS p).
{ eapply jroot_rep_agree; [exact JR | | apply incl_refl]. eapply (agree_of_munch rsegs); [exact MU | exact WM |].
intros b k Hb. cbn. pose proof (heap_blk S4L HIx _ _ _ _ b k HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ b k HP ltac:(apply in_or_app; left; exact Hb)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg. unfold_consts. lia. }
apply evt_RZ_done.
pose proof (dcopy_all HIx PUT PUTX LASTERR HT63 DCOBJ r NN) as REC. unfold dcopy_spec in REC.
eapply REC with (BS := BS) (LB := LB) (lo := lo) (D := D); clear REC;
[ exact HP2 | exact JR2 | exact NN | exact G2 | exact DC | rewrite unsigned_lit by lia; lia | exact DHI | exact DAL
| rewrite unsigned_lit by lia; exact ST | clia | rewrite unsigned_lit by lia; unfold dc_stk, REC_P, DC_C; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | exact FRM | reflexivity | reflexivity | reflexivity | ].
intros ms3 md3 m3 rv (RS3 & VM3 & ST3 & HPR3 & [e3 ERR3]) G3 JR3 RES3.
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp hl_volatile S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR3 by lia.
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia | cbn; lia]. cbn [hl_segs S4L] in FR.
change (482928 - 164) with 482764 in ERR3.
assert (PRES3 : heap_presxD S4L D LB (bv_unsigned sp) m m3).
{ eapply presxD_trans; [exact PRES2|]. eapply presxD_weaken; [exact HPR3 | lia | incl_tac]. }
destruct RES3 as [(-> & A3 & d & q & CBS & REM & CO & Hq & DC3 & JD & HP3) | (-> & A3 & q & CBS & REM & DC3 & FRES & HP3)]; cbn [hl_segs S4L] in DC3.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
pose proof (wmono_refl rsegs m3) as WM3. pose proof (munch_refl [] m3) as MU3.
stash JD. stash CO. stash JR3. stash G3. clear MI.
reenter MOK3.
step. step. step. if_true. step. step. step. step.
unstash JD. unstash CO. unstash JR3. unstash G3.
apply evt_RZ_done. eapply (K _ md3 m3 0).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [exact FS3 | exact FRM3] |]. split; [exact VM3|].
split; [release_frame FR ST3 (bv_unsigned sp); exact ST3|].
split; [exact PRES3 | exists e3; exact ERR3].
+ exact G3.
+ exact JR3.
+ left. split; [reflexivity|]. exists A3, d, q, CBS, REM. repeat (split; [assumption|]). exact HP3.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
pose proof (wmono_refl rsegs m3) as WM3. pose proof (munch_refl [] m3) as MU3.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP3) as HTB.
stash FRES. stash JR3. stash G3. clear MI.
reenter MOK3.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step. step. if_false. step. step.
unstash FRES. unstash JR3. unstash G3.

assert (AFTER : forall ms4 md4 m4 (A4 : AS S4L HIx) (rr : word),
ret_statew S4L (wz 0x2591c) (wz (bv_unsigned sp + -16)) gp (wz 0x75e70) (wz D) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F3 fc3 rr m4 ms4 ->
model_vm_only md3 md4 -> stk rsegs m4 lo (bv_unsigned sp + -16) ->
heap_pres S4L (BS ++ REM ++ LB) (bv_unsigned sp + -16) m3 m4 ->
rw_cells rsegs m4 (0x75e70 - 164) [C4 e3] ->
HEAPx A4 (BS ++ REM ++ LB) m4 md4 ->
realizes rsegs (mkCfg ms4 md4) T).
{ intros ms4 md4 m4 A4 rr RS4 VM4 ST4 HPR4 ERR4 HP4.
destruct RS4 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in DC3; [| left; cbn; lia]. cbn [hl_segs S4L] in DC3.
change (0x75e70 - 164) with 482764 in ERR4.
pose proof (jc_glob_P_pres _ _ _ _ HPR4 G3) as G4.
assert (JR4 : jroot_rep S4L S4F r m4 BS p).
{ eapply jroot_rep_agree; [exact JR3 | | apply incl_refl]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | incl_tac]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m4) as WM4. pose proof (munch_refl [(D, D + 8)] m4) as MU4.
stash JR4. stash G4.
apply rz_evt; [exact MOK4|].
replace (ret_pc (wz 0x2591c)) with (wz 0x2591c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
stepz. step. step. step. step. step. step.
unstash JR4. unstash G4.
apply evt_RZ_done.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m5 end.
assert (HP5 : HEAPx A4 (BS ++ REM ++ LB) m5 md4).
{ eapply (heap_frame S4L HIx); [exact HP4 | | exact WM4 | exact MI]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP4 MU4).
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil]. }
eapply (K _ md4 m5 (2^64 - 1)).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS3 | exact FS4] | intros Hf; apply FRM4; apply FRM3; exact Hf] |].
split; [eapply model_vm_only_trans; [exact VM3 | exact VM4] |].
split; [release_frame FR ST4 (bv_unsigned sp); exact ST4|].
split; [| eexists; eassumption].
eapply presxD_trans; [exact PRES3|]. eapply presxD_trans.
* apply pres_presxD. eapply heap_pres_weaken; [exact HPR4 | lia | incl_tac].
* eapply presxD_of_munch; [exact MU4 | exact WM4 |]. intros a Ha Hc Hd. cbn. split; [exact Hd | exact I].
+ eapply jc_glob_P_outside; [exact G4 | exact MU4 | exact WM4 |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply jroot_rep_agree; [exact JR4 | | apply incl_refl]. eapply (agree_of_munch rsegs); [exact MU4 | exact WM4 |].
intros b k Hb. cbn. pose proof (heap_blk S4L HIx _ _ _ _ b k HP4 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hbhi & _). unfold_consts. lia.
+ right. split; [reflexivity|]. exists A4, REM. split; [eassumption | exact HP5]. }
apply evt_RZ_done.
destruct FRES as [(-> & ->) | [(Hqc & sc & JC) | XD]].
+
eapply PUT with (s := None) (BS := []) (p := 0) (rc := 1) (LB := BS ++ REM ++ LB) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP3 | perm] | split; reflexivity | reflexivity | .. ]; try alloc_side.
{ unfold put_stk_P. rewrite ?unsigned_lit by lia. lia. }
intros ms4 md4 (m4 & A4 & rr & RS4 & VM4 & ST4 & HPR4 & ERR4 & OUT4). cbn [hl_segs hl_tp S4L] in *.
destruct OUT4 as [[_ HP4] | (s' & ES & _)]; [| discriminate ES].
eapply AFTER; [exact RS4 | exact VM4 | rewrite unsigned_lit in ST4 by lia; exact ST4 | rewrite unsigned_lit in HPR4 by lia; exact HPR4 | exact ERR4 | exact HP4].
+
eapply PUT with (s := Some sc) (BS := CBS) (p := q) (rc := 1) (LB := BS ++ REM ++ LB) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP3 | perm] | split; [exact Hqc | split; [lia | exact JC]] | reflexivity | .. ]; try alloc_side.
{ unfold put_stk_P. rewrite ?unsigned_lit by lia. lia. }
intros ms4 md4 (m4 & A4 & rr & RS4 & VM4 & ST4 & HPR4 & ERR4 & OUT4). cbn [hl_segs hl_tp S4L] in *.
destruct OUT4 as [[_ HP4] | (s' & _ & R2 & _)]; [| lia].
eapply AFTER; [exact RS4 | exact VM4 | rewrite unsigned_lit in ST4 by lia; exact ST4 | rewrite unsigned_lit in HPR4 by lia; exact HPR4 | exact ERR4 | exact HP4].
+
pose proof PUTX as PX. unfold jo_put_xleaf_stmt in PX.
eapply PX with (BS := CBS) (LB := BS ++ REM ++ LB) (lo := lo) (r := JRdblx (fn_ud_to_json_string S4F)); clear PX;
[ | exact XD | exact I | reflexivity | ].
{ unfold jf_pre. cbn [hl_segs hl_tp S4L]. rewrite !(unsigned_lit (bv_unsigned sp + -16)) by lia.
split; [eapply (heap_perm S4L HIx); [exact HP3 | perm] |]. split; [exact ST3|]. split; [clia|]. split; [unfold put_stk_P; lia|].
split; [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity|]. split; [clia|].
split; [exact ERR3|]. split; [reflexivity|]. rewrite unsigned_lit by lia. reflexivity. }
intros ms4 md4 m4 rv4 (RS4 & VM4 & ST4 & HPR4 & ERR4') RV ERR4 [A4 HP4]. cbn [hl_segs hl_tp S4L] in *.
eapply AFTER; [exact RS4 | exact VM4 | rewrite unsigned_lit in ST4 by lia; exact ST4 | rewrite unsigned_lit in HPR4 by lia; exact HPR4 | exact ERR4 | exact HP4].
Qed.

#[using="PUT PUTX LASTERR HT63 DCOBJ"] Theorem deep_copy_P : jo_deep_copy_stmt S4L HIx S4F jc_glob_P DEEP_COPY_P SH_ENTRY_P DEEP_COPY_STK0 REC_P.
Proof.
unfold jo_deep_copy_stmt. intros until errv. intros PRE G JR DC SPD D63 DHI DAL FRM A0 A1 A2 K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp hl_volatile S4L] in *.
subst a0 a1 a2 tp. unfold DEEP_COPY_STK0, REC_P, DC_C in LOS.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
unfold_consts. word_range sp SPR.
change (0x75e70 - 164) with 482764 in ERR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (482764, 482768)] m) as MU.
apply rz_evt; [exact MOK|]. unfold DEEP_COPY_P.
carve_frame 16%nat ST.
step. step. step.
step.
destruct r as [|s|tojsx|] eqn:ER.
-
cbn [jroot_rep] in JR. destruct JR as [-> ->].
if_true. step. step. step. step. step. stepz. step. step. step. step. step.
apply evt_RZ_done.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP2 : HEAPx A ([] ++ LB) mx md) by heap_now S4L HIx HP MU WM MI end.
eapply (K _ md _ (2^64 - 1)).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; eassumption].
eapply presxD_of_munch; [exact MU | exact WM |]. intros a Ha Hc Hd.
eapply (client_outside S4L HIx) with (LB0 := LB) (SP := bv_unsigned sp); [exact HP | intros b Hb; exact Hb | clia | solve_clientW S4L HIx HP | exact Ha | exact Hc].
+ eapply jc_glob_P_munch; [exact G | exact MU | exact WM |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ cbn [jroot_rep]. split; reflexivity.
+ right. split; [reflexivity|]. exists A, []. split; [exact DC | cbn [app] in *; exact HP2].
- assert (NN : r <> JRnull) by (rewrite ER; discriminate). rewrite <- ER in *. clear s ER.
eapply deep_copy_P_main; eassumption.
- assert (NN : r <> JRnull) by (rewrite ER; discriminate). rewrite <- ER in *. clear tojsx ER.
eapply deep_copy_P_main; eassumption.
- assert (NN : r <> JRnull) by (rewrite ER; discriminate). rewrite <- ER in *. clear ER.
eapply deep_copy_P_main; eassumption.
Qed.
End DeepCopyTop.

End RC__1.
