(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QRUw QSL3 Qvbw QYIF QnCn QR2u QrIB Q7UD QXUB Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Q9O6 Qiiq Q1Ey Qvmy Qawr Q30W Q2Do Ql4f QJlD Qu4M QUr4 Q3jZ Qmd7 Q22i Qg1M QkXq Q1Y6 QvPk Qoif Qkxa QjKS QnPO QB6X QSHS Qeia QRcT Q6q3.
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
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcObj.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

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
Local Notation fk1_HEAPA := (Qoif.Mq2.fk1_HEAPA HIx) (only parsing).
Local Notation fk1_pres := (Qoif.Mq2.fk1_pres HIx) (only parsing).
Local Notation fk1_HEAPA_W := (Qoif.Mq2.fk1_HEAPA_W HIx) (only parsing).
Local Notation fk1_pres_W := (Qoif.Mq2.fk1_pres_W HIx) (only parsing).
Local Notation dc_blk_notfr := (Qoif.Mq2.dc_blk_notfr HIx) (only parsing).
Local Notation ASP := (Qoif.Mq2.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq2.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq2.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq2.dc_dst D) (only parsing).
Local Notation dc_dfacts := (Qoif.Mq2.dc_dfacts HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_munch := (Qoif.Mq2.dc_dst_munch HIx ra sp LM FRS lo D LO DLOC DAL) (only parsing).
Local Notation dc_dst_presx := (Qoif.Mq2.dc_dst_presx HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_dst_pres := (Qoif.Mq2.dc_dst_pres HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_blkW_disj := (Qoif.Mq2.dc_blkW_disj HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_blkW := (Qoif.Mq2.dc_dst_blkW HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_epi := (Qoif.Mq2.dc_epi HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC NN JR0 Kont) (only parsing).
Local Notation dc_scr := (Qoif.Mq2.dc_scr p D) (only parsing).
Local Notation dc_tail0 := (Qoif.Mq2.dc_tail0 HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC DAL NN JR0 Kont) (only parsing).
Local Notation da_src_agree := (QRcT.Mq1.da_src_agree HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D DLOC DAL) (only parsing).
Local Notation da_src_now := (QRcT.Mq1.da_src_now HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo p D r DLOC DAL JR0) (only parsing).
Local Notation dc_inv_own := (QRcT.Mq1.dc_inv_own HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation da_own_outside := (QRcT.Mq1.da_own_outside HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation dc_dst_presxD := (QRcT.Mq1.dc_dst_presxD HIx ra sp LM FRS D DLOC DAL) (only parsing).

Definition do_own (mc : word -> option byte) (Fr : Z) (v1 : word) (b4 : Z) : Prop :=
exists (j16 jf1 jf2 : list byte) (w1 w2 : word),
rw_cells asegs mc ASP (dc_scr Fr (wz 4294967295) (C8 (wz (D / 8 + 2147450880))) j16) /\
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 8 jf1; C8 v1; CB 80 jf2] /\
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 b4); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Variable skids : list (option jshape).
Hypothesis Ero : r = JRtree (Sobj skids).
Hypothesis FRNo : Z.of_nat (length FRS) + (1 + rdepth r) < 4096.
Hypothesis IHo : forall s', In (Some s') skids -> DCOPY HIx (JRtree s').
Variables (opb ot : Z) (OPBS OTBS : list blk) (oes : list oent) (OKBS : list (list blk)) (ows : list Z).
Hypothesis OV0 : obj_view asegs A4F skids m0 BS p 1 opb OPBS ot OTBS oes OKBS.
Hypothesis LWo : length ows = length skids.
Hypothesis EWo : w = 24 + obj_wsum (map (fun e => (oe_k e, oe_kn e)) oes) ows.
Hypothesis NNWo : Forall (fun x => 0 <= x) ows.
Hypothesis KW1o : forall i s bs, nth_error skids i = Some (Some s) -> nth_error OKBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ows 0, Ri).
Hypothesis KW2o : forall i, nth_error skids i = Some None -> nth i ows 0 = NULL_W.
Hypothesis WLTo : w < 2^28.
Hypothesis BBWo : DC_KB * w <= bB B0.
Hypothesis BDWo : w <= bD B0.

Lemma dc_obj_fail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v1 q : Z) (VBS CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
do_own mc Fr (wz v1) 0 -> fresA mc VBS v1 -> jroot_repA r mc BS p ->
dc_dst mc q -> fresA mc CBS q ->
bD B0 - w <= bD Bc -> bB B0 - DC_KB * w + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 (wz (Fr + 32)) x24 x25 x26 x27 t3 t4 t5 t6)
F1 (wz 0x9fcb4) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP (j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH) FRV JRc DD FRC BDc BBc.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.

assert (PP : exists so, QPZI.Mq4.put_pre A4H A4F so mc VBS v1 1).
{ destruct FRV as [[-> ->] | (Hv & s & JV)]; [exists None; split; reflexivity | exists (Some s); split; [exact Hv | split; [lia | exact JV]]]. }
destruct PP as (so & PP).
assert (HPp : HEAPAx A (VBS ++ (BS ++ CBS ++ REM ++ LB)) LM ((Fr, 1) :: FRS) Bc mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
assert (V2R : 0 <= v1 < 2^64).
{ destruct FRV as [[-> _] | (Hv & s & JV)]; [lia|]. destruct (jval_root_in asegs A4F _ _ _ _ _ JV) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v1 n HPp ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & Hlo & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
stash PRESi. stash Gi. stash FRC. stash JRc. stash DD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

assert (PC : put_costA so 1 VBS <= bB Bc).
{ unfold put_costA. destruct so; [change (1 =? 1) with true; cbv iota|]; unfold DC_KB in *; lia. }
evt_done5.
eapply PUT with (LB := BS ++ CBS ++ REM ++ LB) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (errv := errs) (s := so) (BS := VBS) (p := v1) (rc := 1);
[ exact HPp | exact PP | reflexivity | rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERRs | reflexivity | reflexivity | exact PC | ].
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
destruct OUT2 as [[_ HP2] | (s' & _ & Habs & _)]; [| exfalso; lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in HPR2 by lia.
change (hl_segs A4L) with asegs in *.
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2 H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
unstash DD. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP2 DD HPR2) as DD2. clear DD HPRX. stash DD2.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m2) as MU2.
replace (ret_pc (wz 654524)) with (wz 654524) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
stash SAVEi.
reenterA asegs A4L HIx asegs_wx HP2.
step. stepz. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2 MI2) as HPY.
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2) as HPR2X.
unstash SAVEi. apply (rw_cells_transport asegs [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] _ mX) in SAVEi; [| exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; lia].
unstash DD2. pose proof (dc_dst_munch _ _ _ _ _ _ _ _ _ HP2 DD2 MU2 WM2) as [DCX DSHX].
assert (HPRcX : heap_pres A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mX).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia |] | eapply heap_pres_weaken; [exact HPR2X | lia | intros b Hb; exact Hb]].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (AGX : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mc mX).
{ intros BSx Hi. eapply (agree_of_heap_pres asegs A4H); [exact HPRcX | reflexivity | intros b Hb; apply in_or_app; left; apply Hi; exact Hb]. }
unstash JRc. unstash PRESi. unstash Gi. unstash FRC.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 (BS ++ CBS ++ REM ++ LB) Fr (2^64 - 1)).
- split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPRcX | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
split; [exact ST2 |].
split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPRcX | exact Gi].
- eapply fsaved_trans; [exact FS | exact FS2].
- apply FRM2. exact FRM1.
- exact HPY.
- exact SCR.
- reflexivity.
- exact FF.
- reflexivity.
- exact FSH.
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRc | apply (AGX BS); apply incl_appl; apply incl_refl | apply incl_refl].
- split; [lia|]. right. split; [reflexivity|]. exists q, CBS, REM. split; [reflexivity|]. split; [exact DCX|].
split; [eapply fresA_agree; [exact FRC | apply (AGX CBS); apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
assert (VL : put_costA so 1 VBS <= 512 * Z.of_nat (length VBS)) by (unfold put_costA; destruct so; [change (1 =? 1) with true; cbv iota; lia | destruct PP as [_ ->]; cbn; lia]).
lia.
Qed.

Lemma gran4_nowD : forall A LBa LMx FRS' B mc mdc ab k e,
HEAPAx A LBa LMx FRS' B mc mdc -> In (ab, k) LBa -> ab <= e -> e + 32 <= ab + k -> e mod 8 = 0 ->
ro_cells asegs mc (e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LMx FRS' B mc mdc ab k e HP Hin Hlo Hhi He8.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab k HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & _).
assert (E : forall i, 0 <= i -> e / 8 + 2147450880 + i = ab / 8 + 2147450880 + ((e - ab) / 8 + i)) by (intros i Hi; clear - Hal He8 Hlo; Z.div_mod_to_equations; lia).
assert (G : forall i, 0 <= i <= 3 -> ro_cells asegs mc (e / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)]).
{ intros i Hi. rewrite (E i) by lia. eapply (blk_gran0A HIx _ _ _ _ _ _ _ ab k _ HP Hin); [clear - Hlo Hi; Z.div_mod_to_equations; lia | clear - Hal He8 Hlo Hhi Hi; Z.div_mod_to_equations; lia]. }
pose proof (G 0 ltac:(lia)) as G0. pose proof (G 1 ltac:(lia)) as G1. pose proof (G 2 ltac:(lia)) as G2. pose proof (G 3 ltac:(lia)) as G3.
rewrite Z.add_0_r in G0.
change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]).
apply ro_cells_app. split; [exact G0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [exact G1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [replace (e / 8 + 2147450880 + 1 + 1) with (e / 8 + 2147450880 + 2) by lia; exact G2|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
replace (e / 8 + 2147450880 + 1 + 1 + 1) with (e / 8 + 2147450880 + 3) by lia. exact G3.
Qed.

Lemma obj_nowD : forall A LBa LMx FRS' B mc mdc,
HEAPAx A LBa LMx FRS' B mc mdc -> agree_on asegs BS m0 mc -> incl BS LBa ->
obj_view asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS /\
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
ro_cells asegs mc (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
0 < ot /\ ot mod 8 = 0 /\ ot + 56 <= alloc_ceiling /\
ro_cells asegs mc (ot / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LMx FRS' B mc mdc HP AG INC.
pose proof (obj_view_agree asegs A4F skids m0 mc BS p 1 opb OPBS ot OTBS oes OKBS OV0 AG) as OVc.
destruct (obj_view_tbl asegs A4F skids m0 BS p 1 opb OPBS ot OTBS oes OKBS OV0) as [_ TINB].
assert (INp : In (p, 48) BS) by (destruct OV0 as (EBS & _); rewrite EBS; apply in_or_app; left; left; reflexivity).
assert (INpA : In (p, 48) LBa) by (apply INC; exact INp).
assert (INtA : In (ot, 56) LBa) by (apply INC; exact TINB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ot 56 HP ltac:(apply in_or_app; left; exact INtA)) as (_ & Htal & Htlo & Hthi & _).
split; [exact OVc|]. split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [exact Htlo|]. split; [clear - Htal; Z.div_mod_to_equations; lia|]. split; [exact Hthi|].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ ot 56 HP INtA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH.
Qed.

Lemma ent_nowD : forall A LBa LMx FRS' B mc mdc j e,
HEAPAx A LBa LMx FRS' B mc mdc -> incl BS LBa ->
obj_view asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS -> nth_error oes j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ oe_a e + 32 <= alloc_ceiling /\
ro_cells asegs mc (oe_a e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
(exists pad : word, rw_cells asegs mc (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) oes)))]) /\
exists k bs, nth_error skids j = Some k /\ nth_error OKBS j = Some bs /\ incl bs BS /\ jopt asegs A4F k mc bs (oe_v e).
Proof.
intros A LBa LMx FRS' B mc mdc j e HP INC OV He.
destruct (obj_view_entry asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS j e OV He) as (EA0 & EA8 & (ba & bk & Hin & Hlo & Hhi) & ENT & k & bs & Hk & Hbs & KOK).
assert (EBS : BS = ((p, 48) :: OTBS ++ concat OKBS) ++ OPBS) by (destruct OV as (E & _); exact E).
assert (INbA : In (ba, bk) LBa) by (apply INC; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bk HP ltac:(apply in_or_app; left; exact INbA)) as (_ & _ & _ & Hbhi & _).
split; [exact EA0|]. split; [exact EA8|]. split; [lia|].
split; [eapply (gran4_nowD _ _ _ _ _ _ _ ba bk (oe_a e) HP INbA); [exact Hlo | exact Hhi | exact EA8] |].
split; [exact ENT|].
exists k, bs. split; [exact Hk|]. split; [exact Hbs|]. split.
- intros b Hb. rewrite EBS. apply in_or_app; left; right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb].
- destruct k; exact KOK.
Qed.

Notation okeys := (map (fun e : oent => (oe_k e, oe_kn e)) oes).

Definition do_copy (mc : word -> option byte) (Bc : bud) (q : Z) (CBS : list blk) (acc : Z) : Prop :=
exists (kids' : list (option jshape)) (wq : Z),
q <> 0 /\ dc_dst mc q /\ jval asegs A4F (Sobj kids') mc CBS q 1 /\ okmax kids' <= okmax skids /\
jtx (Sobj kids') CBS = Some (wq, []) /\ wq <= acc /\
obj_inv (obj_capA CBS) (Z.of_nat (length kids')) /\ 18 * Z.of_nat (length kids') <= acc /\
bD B0 - acc <= bD Bc /\ bB B0 - DC_KB * acc + 512 * Z.of_nat (length CBS) + PhiO (obj_capA CBS) (Z.of_nat (length kids')) <= bB Bc.

Notation own_W Fr := [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)].
Lemma do_copy_own : forall Ax LBx Bx mx mdx Fr mc' Bc q CBS acc,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl CBS LBx ->
munch (own_W Fr) mx mc' -> wmono asegs mx mc' ->
do_copy mx Bc q CBS acc -> do_copy mc' Bc q CBS acc.
Proof.
intros Ax LBx Bx mx mdx Fr mc' Bc q CBS acc HP Hi MU WM (kids' & wq & Hq & DD & JQ & REST).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM) as HPR.
exists kids', wq. split; [exact Hq|]. split; [exact (dc_dst_munch _ _ _ _ _ _ _ _ _ HP DD MU WM) |]. split; [| exact REST].
eapply (jval_agree asegs A4F); [exact JQ | | exact Hi].
eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma obj_wsum_skipn_all : forall (keys : list blk) (ws : list Z) n, (length ws <= n)%nat -> obj_wsum (skipn n keys) (skipn n ws) = 0.
Proof. intros keys ws n H. rewrite (skipn_all2 ws) by exact H. destruct (skipn n keys) as [|[? ?] ?]; reflexivity. Qed.

Lemma dc_obj_next :
forall (j : nat) (e : oent) (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 x19 x21 x22 x25 x26 x27 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (Fr q acc : Z) (v1 : word) (CBS REM : list blk),
nth_error oes j = Some e ->
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
do_own m2 Fr v1 0 ->
do_copy m2 B2 q CBS acc -> acc + obj_wsum (skipn (S j) okeys) (skipn (S j) ows) = w ->
(forall e', nth_error oes (S j) = Some e' ->
forall (mc : word -> option byte) (c0 c1 : word),
dc_inv mc md2 -> HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 mc md2 ->
do_own mc Fr v1 248 -> do_copy mc B2 q CBS acc ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) c0 c1 b2 b3 b4 b5 b6 b7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 (wz (Fr + 32)) (wz (oe_a e')) x25 x26 x27 u3 u4 u5 u6)
F2 (wz 0x9f968) fc2 None mc (seg_rom asegs))) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) b0 b1 b2 b3 b4 b5 b6 b7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 (wz (Fr + 32)) (wz (oe_a e)) x25 x26 x27 u3 u4 u5 u6)
F2 (wz 0x9fa90) fc2 None m2 (seg_rom asegs)).
Proof.
intros until REM. intros He INV FS FRM2 HP OWN COPY ACC KLOOP.
pose proof OWN as (j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HP HiB OVc He) as (E0 & E8 & E32 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] m2) as MU.
stash PRESi. stash Gi. stash COPY. stash KLOOP. stash OWN. stash INV. stash OVc. stash AG0.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ REM ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
lazymatch goal with MUc : munch _ m2 mX, WMc : wmono asegs m2 mX, MIc : mem_inv asegs mX |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPX;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STi SAVEi) as INVX;
unstash COPY; pose proof (do_copy_own _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYX
end.
assert (OWNX : do_own mX Fr v1 248) by (exists j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).

pose proof (da_src_agree _ _ _ _ _ _ _ _ HPX HiB INVX) as AGX.
destruct (obj_nowD _ _ _ _ _ _ _ HPX AGX HiB) as (OVX & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HPX HiB OVX He) as (_ & _ & _ & SHeX & (padX & ENTX) & _).
stash INVX. stash COPYX. stash OWNX. stash OVX. stash AGX.
step. asan_chkA.
step.
unstash INVX. unstash COPYX. unstash OWNX. unstash OVX. unstash AGX.
rewrite ohd_skipn.
destruct (nth_error oes (S j)) as [e'|] eqn:He'.
-
destruct (ent_nowD _ _ _ _ _ _ _ (S j) e' HPX HiB OVX He') as (E0' & _ & E32' & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32'.
step. if_truex.
evt_done5. unstash KLOOP.
exact (KLOOP e' eq_refl mX _ _ INVX HPX OWNX COPYX).
-
step. if_lit. step.
destruct OVX as (EBSo & _ & HDRX & _).
destruct (proj1 (rw_cells_app asegs mX _ _ _) HDRX) as [HDRX1 _].
destruct COPYX as (kids' & wq & Hq & DDX & JQX & OK & JTX & WQ & OINV & CNT & BDX & BBX).
pose proof (PhiO_nonnegW _ _ OINV) as PHI.
assert (ACC0 : acc = w).
{ rewrite obj_wsum_skipn_all in ACC; [lia |]. apply nth_error_None in He'. rewrite LWo. destruct OV0 as (_ & _ & _ & _ & _ & L1o & _). lia. }
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 Fr (wz 4294967295) (C8 (wz (D / 8 + 2147450880))) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sobj kids')) q 48 JT_OBJECT (fn_obj_to_json_string A4F) opb CBS REM);
[ exact INVX | exact FS | exact FRM2 | exact HPX | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HPX HiB INVX) | rewrite EBSo; left; reflexivity | lia | exact HDRX1
| rewrite Ero; exists (Sobj kids'); split; [reflexivity | rewrite !sdepth_Sobj; lia]
| cbn [dc_cwA]; exists wq; split; [exact JTX | lia]
| exact Hq | exact DDX | split; [exact Hq | exact JQX]
| lia | unfold DC_KB in *; lia ].
Qed.

Lemma dc_obj :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q : Z) (v1 : word) (CBS : list blk)
(j24 j16 jf1 jf2 : list byte) (w1 w2 : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
rw_cells asegs mc ASP (dc_scr Fr (wz 0) (CB 8 j24) j16) ->
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 8 jf1; C8 v1; CB 80 jf2] ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sobj []) mc CBS q 1 -> length CBS = 3%nat -> obj_capA CBS = 16 ->
jtx (Sobj []) CBS = Some (24, []) ->
bD B0 - 1 <= bD Bc -> bB B0 - ((16 * 48 + 512) + ((16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512)) <= bB Bc ->
(forall e0, nth_error oes 0 = Some e0 ->
forall (mc' : word -> option byte) (c0 c1 : word),
dc_inv mc' mdc -> HEAPAx A (BS ++ CBS ++ [] ++ LB) LM ((Fr, 1) :: FRS) Bc mc' mdc ->
do_own mc' Fr v1 248 -> do_copy mc' Bc q CBS 24 ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) c0 c1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz (Fr + 32)) (wz (oe_a e0)) s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x9f968) fc1 None mc' (seg_rom asegs))) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) (wz Fr) (wz Fr) (wz p) s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x9f90c) fc1 None mc (seg_rom asegs)).
Proof.
intros until w2. intros INV FS FRM1 HP0 SCR FF FSH Hq DD JQ LCBS CAPQ JTXQ BDc BBc KLOOP.
assert (HP : HEAPAx A (BS ++ CBS ++ [] ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc) by exact HP0.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.
pose proof (obj_wsum_nonneg okeys ows NNWo) as WS0.

assert (HiB : incl BS (BS ++ CBS ++ [] ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & Hp0 & Hp48 & Hp8 & SHpc & Ht0 & Ht8 & Ht56 & SHtc).
pose proof OVc as (EBSo & _ & HDRc & _).
pose proof (obj_view_head asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS OVc) as HEAD.
assert (INp : In (p, 48) BS) by (rewrite EBSo; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 5 HP ltac:(apply HiB; exact INp) ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hp48, Ht56. unfold A_SB in SHtc.
assert (COPY0 : do_copy mc Bc q CBS 24).
{ exists [], 24. split; [exact Hq|]. split; [exact DD|]. split; [exact JQ|].
split; [cbn [okmax]; apply okmax_nonneg|]. split; [exact JTXQ|]. split; [lia|].
rewrite CAPQ. cbn [length Z.of_nat]. split; [exact obj_inv_new|]. split; [lia|]. split; [lia|]. rewrite LCBS. unfold PhiO, DC_KB in *. cbn [Z.of_nat]. lia. }
unfold jhdr_cells in HDRc. cbn [app] in HDRc.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
assert (OHD : ohd oes = match nth_error oes 0%nat with Some x => oe_a x | None => 0 end) by (destruct oes; reflexivity).
rewrite OHD in HEAD. clear OHD.
stash PRESi. stash Gi. stash COPY0. stash INV. stash JQ. stash AG0. stash DD. stash KLOOP. stash OVc.
clear DC DSH.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. asan_chkA.
step. step. asan_chkA.
step.
destruct (nth_error oes 0%nat) as [e0|] eqn:He0.
-
unstash OVc. destruct (ent_nowD _ _ _ _ _ _ _ 0%nat e0 HP HiB OVc He0) as (E0 & E8 & E32 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32.
step. if_falsex.
step. step. step. step. step. step. stepz. step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ [] ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb]. }
lazymatch goal with MUc : munch _ mc mX, WMc : wmono asegs mc mX, MIc : mem_inv asegs mX |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPX;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STi SAVEi) as INVX;
unstash COPY0; pose proof (do_copy_own _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY0) as COPYX
end.
rewrite (unsigned_lit D) in SCR by lia. rewrite (Z.shiftr_div_pow2 D 3) in SCR by lia. change (2^3) with 8 in SCR.
assert (OWNX : do_own mX Fr v1 248) by (exists j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
evt_done5. unstash KLOOP.
exact (KLOOP e0 eq_refl mX _ _ INVX HPX OWNX COPYX).
-
step. if_lit.
destruct (proj1 (rw_cells_app asegs mc _ _ _) ltac:(unstash OVc; destruct OVc as (_ & _ & H & _); exact H)) as [HDRg1 _].
assert (W24 : w = 24).
{ rewrite EWo. apply nth_error_None in He0. destruct OV0 as (_ & _ & _ & _ & _ & L1o & _). destruct oes; [| cbn in He0; lia]. reflexivity. }
unstash INV. unstash JQ. unstash DD.
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 mc mdc A Bc Fr (wz 0) (CB 8 j24) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sobj [])) q 48 JT_OBJECT (fn_obj_to_json_string A4F) opb CBS []);
[ exact INV | exact FS | exact FRM1 | exact HP | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HP HiB INV) | exact INp | lia | exact HDRg1
| rewrite Ero; exists (Sobj []); split; [reflexivity | rewrite !sdepth_Sobj; cbn [okmax]; pose proof (okmax_nonneg skids); lia]
| cbn [dc_cwA]; exists 24; split; [exact JTXQ | lia]
| exact Hq | exact DD | split; [exact Hq | exact JQ]
| lia | rewrite LCBS; unfold DC_KB in *; cbn [Z.of_nat]; lia ].
Qed.

Lemma jtx_empty_obj : forall m CBS q, jval asegs A4F (Sobj []) m CBS q 1 -> length CBS = 3%nat -> jtx (Sobj []) CBS = Some (24, []).
Proof.
intros m CBS q J L3.
destruct (sobj_open asegs A4F _ _ _ _ _ J) as (pbq & PBSq & tq & TBSq & kvs & KBSq & ECBS & _ & _ & LH & L1q & L2q & _).
destruct LH as (tbl & size & es & svs & Hkvs & ETBS & _).
destruct kvs; [| cbn in L1q; lia]. destruct KBSq; [| cbn in L2q; lia].
destruct es; [| cbn in Hkvs; discriminate]. unfold lh_blocks in ETBS. cbn [map app] in ETBS.
subst TBSq. cbn [concat app] in ECBS. rewrite ECBS in L3 |- *. destruct PBSq; [| cbn in L3; lia]. reflexivity.
Qed.

Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HD_le : 96 + 4096 + 128 + HD <= DC_C.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.
Hypothesis OBL_STRDUP_NF : strdup_nf_stmt A4L HIx.

Definition dc_obj_add_stmt : Prop :=
forall (j : nat) (e : oent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x25 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v q acc wv wq : Z) (vs : option jshape) (kids' : list (option jshape)) (VBS CBS REM : list blk),
nth_error oes j = Some e ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
do_own mc Fr (wz v) 0 ->
jopt asegs A4F vs mc VBS v -> odep vs <= okmax skids ->
(exists wv', jtx_opt vs VBS = Some (wv', []) /\ wv' <= wv) -> 4 <= wv ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sobj kids') mc CBS q 1 -> okmax kids' <= okmax skids ->
jtx (Sobj kids') CBS = Some (wq, []) -> wq <= acc ->
obj_inv (obj_capA CBS) (Z.of_nat (length kids')) -> 18 * Z.of_nat (length kids') <= acc ->
bD B0 - (acc + wv) <= bD Bc ->
bB B0 - DC_KB * (acc + wv) + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) + PhiO (obj_capA CBS) (Z.of_nat (length kids')) <= bB Bc ->
acc + wv + key_w (oe_kn e) <= w ->
(forall (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 z19 z21 z22 z25 z26 z27 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (CBS' REM' : list blk),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS' ++ REM' ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
do_own m2 Fr (wz v) 0 ->
do_copy m2 B2 q CBS' (acc + wv + key_w (oe_kn e)) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) b0 b1 b2 b3 b4 b5 b6 b7
(wz (Fr / 8 + 2147450880)) z19 (wz 2147450880) z21 z22 (wz (Fr + 32)) (wz (oe_a e)) z25 z26 z27 u3 u4 u5 u6)
F2 (wz 0x9fa90) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 (wz (Fr + 32)) (wz (oe_a e)) x25 (wz (oe_k e)) x27 t3 t4 t5 t6)
F1 (wz 0x9f9bc) fc1 None mc (seg_rom asegs)).

Lemma dc_obj_add : dc_obj_add_stmt.
Proof.
unfold dc_obj_add_stmt. intros until REM.
intros He INV FS FRM1 HP OWN JOB ODEP (wv' & JTV & WV') WV4 Hq DD JQ OK JTX WQ OINV CNT BDc BBc ACCW KADD.
pose proof OWN as (j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

destruct (sobj_open asegs A4F _ _ _ _ _ JQ) as (pbq & PBSq & tq & TBSq & kvsq & KBSq & ECBS & OPBq & HDRq & LHq & Lq1 & Lq2 & KIDSq).
destruct LHq as (tblq & sizeq & esq & svsq & Ekvs & ETBS & OPENq).
assert (INq : In (q, 48) (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply in_or_app; right; apply in_or_app; left; rewrite ECBS; left; reflexivity).
assert (INt : In (tq, 56) (BS ++ CBS ++ VBS ++ REM ++ LB)).
{ apply in_or_app; right; apply in_or_app; left. rewrite ECBS, ETBS. unfold lh_blocks. right. left. reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q 48 HP ltac:(apply in_or_app; left; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tq 56 HP ltac:(apply in_or_app; left; exact INt)) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi, Hthi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 5 HP INq ltac:(lia) ltac:(lia)) as SHq5.
replace (q / 8 + 2147450880 + 5) with (q / 8 + 2147450885) in SHq5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ tq 56 5 HP INt ltac:(lia) ltac:(lia)) as SHt5.
replace (tq / 8 + 2147450880 + 5) with (tq / 8 + 2147450885) in SHt5 by lia.
unfold jhdr_cells in HDRq. cbn [app] in HDRq.
pose proof (proj1 OPENq) as THDR. unfold lh_hdr, lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free A4F] in THDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
stash PRESi. stash Gi. stash OWN. stash INV. stash JQ. stash JOB. stash OPBq. stash KIDSq. stash OPENq. stash KADD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. rewrite ?zxb_zero. step. if_lit.
step. step.
step. asan_chkA.
step. step. asan_chkA.
step. step. step.

step.
assert (HiB : incl BS (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
unstash INV.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & _).
pose proof OVc as (_ & _ & _ & _ & (_ & _ & OTE) & _).
destruct (OTE j e He) as (_ & _ & _ & _ & CSk & INk & KNk).
assert (INkB : In (oe_k e, oe_kn e) BS) by (destruct OVc as (E & _); rewrite E; apply in_or_app; left; right; apply in_or_app; left; exact INk).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
unstash Gi.
evt_done5.
eapply HASH with (LB := BS ++ CBS ++ VBS ++ REM ++ LB) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (errv := errs) (kp := oe_k e) (kn := oe_kn e) (ks := oe_ks e);
[ exact HP | apply HiB; exact INkB | exact CSk | exact Gi
| rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; unfold DC_C in HD_le; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM1
| cbn [length]; clear - FRNo RD0; lia | reflexivity | ].
intros ms2 md2 A2 (mB & h & e2 & RS2 & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2, HPR2 by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 653836)) with (wz 653836) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_rangex A4H a4_volatile ((BS ++ CBS ++ VBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs mB A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2 H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply HPRX in HDRq; [| eapply client_rangex_block; [apply in_or_app; left; exact INq | lia | cbn [cells_size csize Nat.add]; lia]].
pose proof (dc_dst_presx _ _ _ _ _ _ _ _ _ _ _ _ HP DD HPR2) as DD2. clear HPRX.
assert (AG2 : agree_on asegs (BS ++ CBS ++ VBS ++ REM ++ LB) mc mB).
{ eapply (agree_of_heap_presx asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }

assert (INV2 : dc_inv mB md2).
{ split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [unstash PRESi; exact PRESi |]; apply (QrIB.Mq0.presx_presxD A4H); eapply heap_presx_weaken; [exact HPR2 | lia | | intros a0' Xa; exact Xa] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST2 |]. split; [unfold dc_save; exact SAVEi | exact G2]. }
assert (HiC : incl CBS (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply incl_appr; apply incl_appl; apply incl_refl).
assert (HiV : incl VBS (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply incl_appr; apply incl_appr; apply incl_appl; apply incl_refl).
unstash JQ. pose proof (jval_agree asegs A4F _ _ _ _ _ _ _ JQ AG2 HiC) as JQ2.
unstash JOB. pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB AG2 HiV) as JOB2.
unstash OPENq.
assert (HiT : incl (lh_blocks tq tblq sizeq esq) (BS ++ CBS ++ VBS ++ REM ++ LB)).
{ intros b Hb. apply HiC. rewrite ECBS, ETBS. apply in_or_app; left. right. apply in_or_app; left. exact Hb. }
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPENq AG2 HiT) as OPEN2.
assert (OWN2 : do_own mB Fr (wz v) 0) by (exists j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).

pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 5 HP2 INq ltac:(lia) ltac:(lia)) as SHq5b.
replace (q / 8 + 2147450880 + 5) with (q / 8 + 2147450885) in SHq5b by lia.
clear MU WM MI SHq5 SHt5 THDR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs mB) as WM2. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mB) as MU2.
stash INV2. stash OWN2. stash JQ2. stash JOB2. stash OPEN2. stash DD2.
reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite ?zxb_zero. step. if_lit.
step. step. step. step. step.
assert (INkA : In (oe_k e, oe_kn e) (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply HiB; exact INkB).
pose proof (cstr_agree asegs _ _ _ _ _ _ CSk AG2 INkA ltac:(destruct CSk as (Lk & _); lia)) as CSk2.
destruct (Qkxa.oadd_keyX HIx LM ((Fr, 1) :: FRS) (oe_k e) (oe_kn e) (oe_ks e) _ _ _ _ _ HP2 INkA CSk2) as (STRk & NNk & KLk & KPOSk & KHIk & KALk).
destruct (Qkxa.oadd_factsX HIx LM ((Fr, 1) :: FRS) q tq tblq sizeq esq _ _ _ _ (BS ++ CBS ++ VBS ++ REM ++ LB) (concat KBSq ++ PBSq ++ BS ++ VBS ++ REM ++ LB) HP2
ltac:(rewrite ECBS, ETBS; perm))
as ((Hqal' & Hqlo' & Hqhi' & Hqimg) & (Htal' & Htlo' & Hthi' & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEPq & Dq1 & Dq2 & KFq).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (BELOW : lh_below lo tq tblq sizeq esq).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e1 He1. destruct (KFq e1 He1) as (_ & _ & K2 & _). lia. }
eapply evt_cut.
{ eapply (lh_lookup_A_spec HIx OBL_ISTRCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 tq tblq sizeq (oe_k e) lo esq svsq (oe_ks e) mB md2 A2 (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc (oe_k e) (oe_kn e) HP2) with (h := h);
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) by lia;
first [ exact MI2 | (unstash OPEN2; exact OPEN2) | exact BELOW | exact STRk | exact NNk | exact ST2 | exact LO | exact INkA | reflexivity | exact Hh | lia
| (clear - SPA; Z.div_mod_to_equations; lia)
| exact HiT ]. }
intros ms3 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & rl & mC & -> & MU3 & WM3 & MI3 & ST3 & OPEN3 & KB3 & RES).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in MU3, ST3 by lia.
assert (HP3 : HEAPAx A2 (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mC md2) by heap_nowA A4L HIx HP2 MU3 WM3 MI3.
assert (AG3 : agree_on asegs (BS ++ CBS ++ VBS ++ REM ++ LB) mB mC).
{ eapply (agree_of_munch asegs); [exact MU3 | exact WM3 |]. intros a0' n0' Ha. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a0' n0' HP2 ltac:(apply in_or_app; left; exact Ha)) as (? & _ & _ & ? & _). lia. }

assert (HPR3 : heap_pres A4H ((BS ++ CBS ++ VBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) mB mC).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp + -192)); [exact MU3 | exact WM3 |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP2]. }
unstash INV2. unstash OWN2. unstash JQ2. unstash JOB2. unstash DD2.
destruct OWN2 as (j16' & jf1' & jf2' & w1' & w2' & SCR2 & FF2 & FSH2).
assert (HPRX3 : forall A0 cs0, rw_cells asegs mB A0 cs0 ->
client_range A4H ((BS ++ CBS ++ VBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs mC A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3 H1 H2). }
pose proof INV2 as (VM2i & PRES2i & ST2i & SAVE2i & G2i). unfold dc_save in SAVE2i.
unfold ASP, dc_scr in SCR2.
apply HPRX3 in SCR2; [| left; lia]. apply HPRX3 in SAVE2i; [| left; lia].
apply HPRX3 in FF2; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX3 in FSH2; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP2 DD2 HPR3) as DD3. clear HPRX3.
assert (INV3 : dc_inv mC md2).
{ split; [exact VM2i |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRES2i |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR3 | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST3 |]. split; [unfold dc_save; exact SAVE2i | eapply lh_globA_client; [exact HPR3 | exact G2i]]. }
pose proof (jval_agree asegs A4F _ _ _ _ _ _ _ JQ2 AG3 HiC) as JQ3.
pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB2 AG3 HiV) as JOB3.
assert (OWN3 : do_own mC Fr (wz v) 0) by (exists j16', jf1', jf2', w1', w2'; split; [exact SCR2 | split; [exact FF2 | exact FSH2]]).

destruct (Qkxa.oadd_pvX HIx VBS LM ((Fr, 1) :: FRS) q v vs _ _ _ _ (BS ++ CBS ++ VBS ++ REM ++ LB) (lh_blocks tq tblq sizeq esq ++ concat KBSq ++ PBSq ++ BS ++ REM ++ LB) HP3
ltac:(rewrite ECBS, ETBS; perm) JOB3) as (Hqv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in V1.
stash INV3. stash JQ3. stash JOB3. stash OPEN3. stash KB3. stash KFq. stash OVc. stash OTE. stash KIDSq. stash BELOW. stash RES. stash DD3. stash OWN3.
clear HP2 HPR2 DD2 INV2 JQ2 JOB2 OPEN2 SHq5b WM2 MU2 VM2i PRES2i SAVE2i G2i ST2.
lazymatch type of MU3 with munch _ ?mq _ =>
transport_after_call asegs mq mC MU3 WM3; try match goal with H : mem_inv asegs mq |- _ => clear H end end.
replace (ret_pc (wz 653864)) with (wz 653864) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. if_falsex.
step.
unstash RES. destruct RES as [-> | (j' & e' & Hj' & -> & Hks')].
-
if_true.
step. step.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errs3 & ERRs3).
unstash KB3.
assert (BBs : 16 * (Z.of_nat (length (oe_ks e)) + 1) + 512 <= bB Bc).
{ pose proof (PhiO_nonnegW _ _ OINV) as PH0. pose proof (pair_budget (Z.of_nat (length (oe_ks e))) ltac:(lia)) as PB.
assert (KWM : key_w (Z.of_nat (length (oe_ks e)) + 1) <= key_w (oe_kn e)) by (unfold key_w; lia).
unfold strdup_costB, DC_KOBJ in PB. unfold DC_KB in *. lia. }
assert (BDs : 1 <= bD Bc).
{ pose proof (key_w_pos (oe_kn e)). lia. }
evt_done5.
eapply OBL_STRDUP_NF with (u := UWpaid) (src := oe_k e) (ab := oe_k e) (nb := oe_kn e) (str := oe_ks e) (lo := lo) (errv := errs3); [exact HP3 | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact INkA. 1: lia. 1: lia. 1: exact KB3. 1: exact NNk. 1: lia.
1: exact ST3.
1: exact LO. 1: cbn [hl_stack_A A4L]; lia. 1: clear - SPA; Z.div_mod_to_equations; lia. 1: lia.
1: exact ERRs3. 1: reflexivity. 1: reflexivity. 1: exact I. 1: exact I. 1: exact BBs. 1: cbn [uw_cost]; lia.
intros ms4 m4 md4 A4 r2 e4 RS4 VM4 ST4 HPR4 ERR4 Hr2 NEWK HP4. open_ret RS4.
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST4, HPR4 by lia.
change (hl_segs A4L) with asegs in *. cbn [uw_cost] in HP4.
replace (ret_pc (wz 653928)) with (wz 653928) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (AG4 : agree_on asegs (BS ++ CBS ++ VBS ++ REM ++ LB) mC m4).
{ eapply (agree_of_heap_pres asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_pres_weaken; [exact HPR4 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPRX4 : forall A0 cs0, rw_cells asegs mC A0 cs0 ->
client_range A4H ((BS ++ CBS ++ VBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m4 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4 H1 H2). }
unstash INV3. pose proof INV3 as (VM3i & PRES3i & ST3i & SAVE3i & G3i). unfold dc_save in SAVE3i.
apply HPRX4 in SCR2; [| left; lia]. apply HPRX4 in SAVE3i; [| left; lia].
apply HPRX4 in FF2; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX4 in FSH2; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply (rw_cells_agree asegs _ _ _ _ _ HDRq) in AG4 as HDRq4; [| exists q, 48; split; [exact INq | cbn; lia]].
unstash DD3. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP3 DD3 HPR4) as DD4.
unstash OPEN3. pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN3 AG4 HiT) as OPEN4.
unstash JOB3. pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB3 AG4 HiV) as JOB4.
pose proof (lh_globA_client _ _ _ _ HPR4 G3i) as G4.
assert (INV4 : dc_inv m4 md4).
{ split; [eapply model_vm_only_trans; [exact VM3i | exact VM4] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRES3i |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR4 | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST4 |]. split; [unfold dc_save; exact SAVE3i | exact G4]. }
assert (OWN4 : do_own m4 Fr (wz v) 0) by (exists j16', jf1', jf2', w1', w2'; split; [exact SCR2 | split; [exact FF2 | exact FSH2]]).
clear HPRX4.

pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r2 _ HP4 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & Hr2wr).
cbn [hl_segs hla_base A4L A4H] in Hr2wr. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
assert (INq4 : In (q, 48) ((r2, Z.of_nat (length (oe_ks e)) + 1) :: BS ++ CBS ++ VBS ++ REM ++ LB)) by (right; exact INq).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q 48 5 HP4 INq4 ltac:(lia) ltac:(lia)) as SHq5c.
replace (q / 8 + 2147450880 + 5) with (q / 8 + 2147450885) in SHq5c by lia.
assert (CS4 : cstr asegs m4 r2 (Z.of_nat (length (oe_ks e)) + 1) (oe_ks e)).
{ split; [lia|]. split; [exact (proj1 (proj2 CSk2))|]. exists []. rewrite app_nil_r.
pose proof (bytes_at_bound _ _ _ _ NEWK) as NB. rewrite length_app in NB. cbn [length] in NB.
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; exact NEWK] |].
cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (Z.of_nat (length (oe_ks e)) + 1) + 0)) with (Z.of_nat (length (oe_ks e)) + 1) by lia. exact Hr2wr. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. change (hl_segs A4L) with asegs in MI4.
pose proof (wmono_refl asegs m4) as WM4. pose proof (munch_refl [] m4) as MU4.
stash INV4. stash OPEN4. stash JOB4. stash DD4. stash OWN4. stash CS4. stash AG4. stash NEWK.
clear ST3 ERRs3 HPR3 MU3 WM3 MI3 STRk.
reenterA asegs A4L HIx asegs_wx HP4.
step. if_falsex.
step.
step. rewrite ?zxb_zero. step. if_false.
step.
step. step. step.
step.

assert (CAPq : obj_capA CBS = sizeq).
{ rewrite ECBS, ETBS. unstash OPEN4. pose proof OPEN4 as (_ & _ & _ & _ & Hszq & _). pose proof (lf_size_range sizeq Hszq). apply Qkxa.obj_capA_lh. lia. }
assert (LENq : Z.of_nat (length esq) = Z.of_nat (length kids')) by (rewrite <- Lq1, Ekvs, length_map; reflexivity).
assert (CAP29 : sizeq <= 2^29).
{ rewrite <- CAPq. eapply obj_inv_cap; [exact OINV|]. pose proof (key_w_pos (oe_kn e)). lia. }
set (cap' := if lf_thr sizeq <=? Z.of_nat (length kids') then lh_ns sizeq else sizeq).
assert (GROWN : obj_grownA sizeq (Z.of_nat (length kids')) cap').
{ subst cap'. unfold obj_grownA. destruct (Z.leb_spec (lf_thr sizeq) (Z.of_nat (length kids'))); [right | left]; split; [reflexivity | lia | reflexivity | lia]. }
rewrite CAPq in OINV, BBc.
destruct (potential_step_obj_add _ _ _ OINV CAP29 GROWN) as [PST OINV'].
pose proof (PhiO_nonnegW _ _ OINV') as PH1. pose proof (PhiO_nonnegW _ _ OINV) as PH0.
pose proof (pair_budget (Z.of_nat (length (oe_ks e))) ltac:(lia)) as PB.
assert (KWM : key_w (Z.of_nat (length (oe_ks e)) + 1) <= key_w (oe_kn e)) by (unfold key_w; lia).
lazymatch goal with |- AJ5e _ _ _ _ _ _ => idtac | |- _ => idtac end.
lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?Bx _ _ => assert (BBi : ins_costB sizeq (Z.of_nat (length esq)) <= bB Bx /\ 0 <= bD Bx) end.
{ rewrite LENq. cbn [bB bD charge]. unfold strdup_costB, DC_KOBJ in PB. unfold DC_KOBJ in PST. unfold DC_KB in *. pose proof (key_w_pos (oe_kn e)). split; lia. }
destruct BBi as [BBi BDi].
unstash OPEN4. unstash CS4.
evt_done5.
eapply (lh_insert_A_full HIx LF OBL_AMEMSET (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) (fun a => model_vm_only_refl (cfg_model a))
(fun a b c => model_vm_only_trans (cfg_model a) (cfg_model b) (cfg_model c)) (fun a b H => H) HD HD_ge HASH)
with (LB := (q, 48) :: concat KBSq ++ PBSq ++ BS ++ VBS ++ REM ++ LB) (t := tq) (tbl := tblq) (size := sizeq) (es := esq) (svs := svsq)
(k := r2) (kn := Z.of_nat (length (oe_ks e)) + 1) (ks := oe_ks e) (v := v) (h := h) (lo := lo) (errv := e4);
a4l_goal; rewrite ?unsigned_lit by lia;
first [ eapply (heapA_perm A4L HIx); [exact HP4 | rewrite ECBS, ETBS; unfold lh_blocks; perm | apply Permutation_refl | apply Permutation_refl]
| exact OPEN4 | exact G4 | exact CS4 | exact ST4 | exact ERR4 | exact (FRM2 FRM1) | exact BBi | exact BDi | reflexivity | exact LO
| solve [cbn [length]; clear - FRNo RD0; lia]
| solve [clear - SPA; Z.div_mod_to_equations; lia]
| solve [unfold DC_C in HD_le; lia]
| lia | idtac ].
intros ms5 md5 A5 (m5 & r5 & e5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & G5 & BB5 & BD5 & OUT5).
destruct RS5 as (yy0 & yy1 & yy2 & yy3 & yy4 & yy5 & yy6 & yy7 & yy8 & yy9 & yy10 & yy11 & yy12 & yy13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST5, HPR5 by lia.
cbn [bB bD charge] in BB5, BD5.
set (LBI := (q, 48) :: concat KBSq ++ PBSq ++ BS ++ VBS ++ REM ++ LB) in *.

assert (AG5 : agree_on asegs LBI m4 m5).
{ eapply (agree_of_heap_presx asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_presx_weaken; [exact HPR5 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb | intros a' Ha'; exact Ha']. }
assert (HPRX5 : forall A0 cs0, rw_cells asegs m4 A0 cs0 ->
client_rangex A4H a4_volatile (LBI ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m5 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR5 H1 H2). }
unstash INV4. pose proof INV4 as (VM4i & PRES4i & ST4i & SAVE4i & G4i). unfold dc_save in SAVE4i.
apply HPRX5 in SCR2; [| left; lia]. apply HPRX5 in SAVE4i; [| left; lia].
apply HPRX5 in FF2; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX5 in FSH2; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
apply HPRX5 in HDRq4; [| eapply client_rangex_block; [apply in_or_app; left; left; reflexivity | lia | cbn [cells_size csize Nat.add]; lia]].
assert (OWN5 : do_own m5 Fr (wz v) 0) by (exists j16', jf1', jf2', w1', w2'; split; [exact SCR2 | split; [exact FF2 | exact FSH2]]).
assert (HiCI : incl (concat KBSq) LBI) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiPI : incl PBSq LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiBI : incl BS LBI) by (intros b Hb; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb).
assert (HiVI : incl VBS LBI) by (intros b Hb; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb).
assert (HiLI : incl LB LBI) by (intros b Hb; right; do 5 (apply in_or_app; right); exact Hb).
unstash JOB4. pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB4 AG5 HiVI) as JOB5.
unstash AG4. unstash OPBq. unstash KIDSq. unstash KIDSq.
assert (AGc5 : agree_on asegs (concat KBSq ++ PBSq) mc m5).
{ eapply agree_on_trans; [eapply agree_on_incl; [exact AG2 |] | eapply agree_on_trans; [eapply agree_on_incl; [exact AG3 |] | eapply agree_on_trans; [eapply agree_on_incl; [exact AG4 |] | eapply agree_on_incl; [exact AG5 |]]]].
1-3: intros b Hb; apply HiC; rewrite ECBS; cbn [app]; right; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply HiCI; exact Hb | apply HiPI; exact Hb]. }
pose proof (okids_agree asegs A4F _ _ _ _ _ _ KIDSq AGc5 ltac:(intros b Hb; apply in_or_app; left; exact Hb)) as KIDS5.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPBq AGc5 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as OPB5.
assert (HPR45 : heap_presx A4H a4_volatile ((BS ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) mC m5).
{ eapply heap_presx_trans; [apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR4 | lia |] |].
- clear. intros b Hb. apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right; do 3 (apply in_or_app; right); exact Hb].
- eapply heap_presx_weaken; [exact HPR5 | lia | | intros a' Xa; exact Xa].
clear. intros b Hb. apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left | right; exact Hb]. unfold LBI.
apply in_app_or in Hb as [Hb | Hb]; right; [do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb | do 5 (apply in_or_app; right); exact Hb]. }
assert (INV5 : dc_inv m5 md5).
{ split; [eapply model_vm_only_trans; [exact VM4i | exact VM5] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRES3i |]; apply (QrIB.Mq0.presx_presxD A4H); eapply heap_presx_weaken; [exact HPR45 | lia | | intros a0' Xa; exact Xa] |].
{ clear. intros b Hb. apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right].
apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST5 |]. split; [unfold dc_save; exact SAVE4i | exact G5]. }
clear HPRX5.
destruct OUT5 as [(-> & OPEN5 & CS5 & HP5) | (-> & tbl' & size' & es' & svs' & g & STRIP & OPEN5 & HP5 & SZ')].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (wmono_refl asegs m5) as WM5. pose proof (munch_refl [] m5) as MU5.
assert (HP5p : HEAPAx A5 (BS ++ CBS ++ VBS ++ ((r2, Z.of_nat (length (oe_ks e)) + 1) :: REM) ++ LB) LM ((Fr, 1) :: FRS) B5 m5 md5).
{ eapply (heapA_perm A4L HIx); [exact HP5 | unfold LBI; rewrite ECBS, ETBS; unfold lh_blocks; perm | apply Permutation_refl | apply Permutation_refl]. }
assert (JRs5 : jroot_repA r m5 BS p) by (eapply da_src_now; [exact HP5p | intros b Hb; apply in_or_app; left; exact Hb | exact INV5]).
unstash DD4. pose proof (dc_dst_presx _ _ _ _ _ _ _ _ _ _ _ _ HP4 DD4 HPR5) as DD5.
assert (JQ5 : jval asegs A4F (Sobj kids') m5 CBS q 1).
{ eapply (sobj_close asegs A4F) with (TBS := lh_blocks tq tblq sizeq esq) (kvs := kvsq);
[ rewrite <- ETBS; exact ECBS | exact OPB5 | unfold jhdr_cells; cbn [app]; exact HDRq4
| exists tblq, sizeq, esq, svsq; split; [exact Ekvs | split; [reflexivity | exact OPEN5]]
| exact Lq1 | exact Lq2 | exact KIDS5 ]. }
reenterA asegs A4L HIx asegs_wx HP5.
step. if_lit.
evt_done5.
unfold strdup_costB, DC_KOBJ in PB. unfold DC_KOBJ in PST. rewrite LENq in BB5. pose proof (key_w_pos (oe_kn e)) as KW14.
eapply dc_obj_fail with (v1 := v) (q := q) (VBS := VBS) (CBS := CBS) (REM := (r2, Z.of_nat (length (oe_ks e)) + 1) :: REM);
[ exact INV5 | eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS5]] | apply FRM5; apply FRM2; exact FRM1 | exact HP5p | exact OWN5
| destruct vs as [sv|]; [right; split; [exact (proj1 JOB5) | exists sv; exact (proj2 JOB5)] | left; exact JOB5] | exact JRs5 | exact DD5
| right; split; [exact Hq | exists (Sobj kids'); exact JQ5] | lia | unfold DC_KB in *; lia ].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (wmono_refl asegs m5) as WM5. pose proof (munch_refl [] m5) as MU5.
assert (LEN' : length es' = length esq) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
set (CBS' := ((q, 48) :: lh_blocks tq tbl' size' (es' ++ [LE g r2 (Z.of_nat (length (oe_ks e)) + 1) (oe_ks e) v]) ++ concat (KBSq ++ [VBS])) ++ PBSq).
assert (HP5p : HEAPAx A5 (BS ++ CBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) B5 m5 md5).
{ subst CBS'. rewrite concat_app. cbn [concat]. rewrite app_nil_r.
eapply (heapA_perm A4L HIx); [exact HP5 | unfold LBI, lh_blocks; rewrite map_app; cbn [map le_k le_kn]; perm | apply Permutation_refl | apply Permutation_refl]. }
unstash DD4. pose proof (dc_dst_presx _ _ _ _ _ _ _ _ _ _ _ _ HP4 DD4 HPR5) as DD5.
pose proof OPEN5 as (_ & _ & _ & _ & Hsz5 & Hcnt5 & _). pose proof (lf_size_range size' Hsz5) as HSR5.
assert (CAP' : obj_capA CBS' = cap').
{ subst CBS' cap'. rewrite SZ', LENq. apply Qkxa.obj_capA_lh.
pose proof OPEN4 as (_ & _ & _ & _ & Hszq & _). pose proof (lf_size_range sizeq Hszq) as HSRq. unfold lh_ns. destruct (lf_thr sizeq <=? Z.of_nat (length kids')); [destruct (sizeq <=? 2 ^ 29); lia | lia]. }
assert (LCBS' : Z.of_nat (length CBS') = Z.of_nat (length CBS) + Z.of_nat (length VBS) + 1).
{ subst CBS'. rewrite ECBS, ETBS. unfold lh_blocks. rewrite !length_app. cbn [length app]. rewrite !length_app, !length_map, !length_app, !concat_app. cbn [concat length].
rewrite !length_app. cbn [length]. rewrite Nat.add_0_r, LEN'. unfold blk in *. lia. }
assert (JQ5 : jval asegs A4F (Sobj (kids' ++ [vs])) m5 CBS' q 1).
{ eapply (sobj_close asegs A4F) with (kvs := map kv (es' ++ [LE g r2 (Z.of_nat (length (oe_ks e)) + 1) (oe_ks e) v]));
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app]; exact HDRq4
| exists tbl', size', (es' ++ [LE g r2 (Z.of_nat (length (oe_ks e)) + 1) (oe_ks e) v]), svs'; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map, !length_app, LEN'; cbn [length]; rewrite <- Lq1, Ekvs, length_map; lia
| rewrite !length_app; cbn [length]; lia
| rewrite map_app, (strip_kv _ _ STRIP); cbn [map]; apply okids_app; [unfold kv; rewrite <- Ekvs; exact KIDS5 | apply okids_one; unfold kv; cbn [le_k le_v]; exact JOB5] ]. }
assert (JTX5 : jtx (Sobj (kids' ++ [vs])) CBS' = Some (wq + (key_w (Z.of_nat (length (oe_ks e)) + 1) + wv'), [])).
{ subst CBS'. unfold lh_blocks. rewrite map_app. cbn [map le_k le_kn].
rewrite ECBS, ETBS in JTX. unfold lh_blocks in JTX.
assert (EKEYS : map (fun e0 : lent => (le_k e0, le_kn e0)) es' = map (fun e0 : lent => (le_k e0, le_kn e0)) esq).
{ pose proof (f_equal (map (fun x : Z * Z * list byte * Z => (fst (fst (fst x)), snd (fst (fst x))))) STRIP) as E. rewrite !map_map in E. exact E. }
rewrite EKEYS.
exact (obj_add_jtx asegs A4F m5 kids' kvsq KBSq PBSq (q, 48) (tq, 56) (tblq, 40 * sizeq) (tbl', 40 * size') (r2, Z.of_nat (length (oe_ks e)) + 1)
(map (fun e0 : lent => (le_k e0, le_kn e0)) esq) vs VBS wq wv' KIDS5 ltac:(rewrite length_map, <- Lq1, Ekvs, length_map; reflexivity) JTX JTV). }
reenterA asegs A4L HIx asegs_wx HP5.
step. if_lit.
evt_done5.
unfold strdup_costB, DC_KOBJ in PB. unfold DC_KOBJ in PST. rewrite LENq in BB5. pose proof (key_w_pos (oe_kn e)) as KW14.
unstash KADD.
eapply KADD with (CBS' := CBS') (REM' := REM);
[ exact INV5 | eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS5]] | apply FRM5; apply FRM2; exact FRM1 | exact HP5p | exact OWN5 | ].
exists (kids' ++ [vs]), (wq + (key_w (Z.of_nat (length (oe_ks e)) + 1) + wv')).
split; [exact Hq|]. split; [exact DD5|]. split; [exact JQ5|].
split; [rewrite okmax_app, okmax_single; pose proof (okmax_nonneg kids'); pose proof (odep_nonneg vs); lia|].
split; [exact JTX5|]. split; [lia|].
rewrite CAP', length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
split; [exact OINV'|]. split; [lia|]. split; [lia|].
unfold blk in *. change (Z.of_nat 1) with 1. unfold DC_KB in *. lia.
-
unstash OPEN3. unstash KIDSq. unstash KIDSq. unstash OPBq. unstash JQ3. unstash JOB3. unstash KFq. unstash DD3. unstash OWN3. unstash INV3.
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN3 Hj') as (sl & Hsl & Hix & SLOT).
pose proof OPEN3 as (_ & _ & LINK3 & _ & Hsz3 & _ & Hlen3). destruct LINK3 as (_ & _ & _ & LK4).
destruct (LK4 e' (nth_error_In _ _ Hj')) as (_ & _ & _ & Hve). clear LK4.
pose proof (lf_size_range sizeq Hsz3) as HSR3.
remember (ent_addr tblq (le_ix e')) as EA eqn:HEA.
assert (EAR : tblq <= EA /\ EA + 40 <= tblq + 40 * sizeq) by (subst EA; unfold ent_addr; clear - Hix Hlen3; split; [lia | nia]).
assert (TB8 : tblq mod 8 = 0) by (clear - Hbal; Z.div_mod_to_equations; lia).
assert (EA8 : EA mod 8 = 0) by (subst EA; unfold ent_addr; clear - TB8; Z.div_mod_to_equations; lia).
assert (Hjkv : nth_error kvsq j' = Some (le_k e', le_v e')) by (rewrite Ekvs, nth_error_map, Hj'; reflexivity).
destruct (okids_nth asegs A4F _ _ _ _ _ _ _ KIDSq Hjkv) as (kj & bsj & Hkj & Hbsj & JO).
destruct (nth_error_split3 _ esq j' e' Hj') as [Ees Lpre]. set (pre := firstn j' esq) in *. set (post := skipn (S j') esq) in *.
destruct (nth_error_split3 _ kids' j' kj Hkj) as [Ek Lk1]. set (kids1 := firstn j' kids') in *. set (kids2 := skipn (S j') kids') in *.
destruct (nth_error_split3 _ KBSq j' bsj Hbsj) as [EK Lb1]. set (KBS1 := firstn j' KBSq) in *. set (KBS2 := skipn (S j') KBSq) in *.
clearbody pre post kids1 kids2 KBS1 KBS2.
assert (Lq1' : length (map kv esq) = length kids') by (rewrite length_map, <- Lq1, Ekvs, length_map; reflexivity).
assert (K12 : okids asegs A4F mc kids1 (map kv pre) KBS1 /\ okids asegs A4F mc kids2 (map kv post) KBS2).
{ pose proof KIDSq as KIDS'. rewrite Ekvs in KIDS'. change (map (fun e0 : lent => (le_k e0, le_v e0)) esq) with (map kv esq) in KIDS'.
rewrite Ek, Ees, EK, map_app in KIDS'. cbn [map] in KIDS'.
apply okids_app_inv in KIDS' as [K1 K2]; [| rewrite length_map; clear - Lpre Lk1; lia | clear - Lb1 Lk1; unfold blk in *; lia]. split; [exact K1 | exact (proj2 K2)]. }
destruct K12 as [K1 K2].
assert (JX : exists w', jtx (Sobj (kids1 ++ vs :: kids2)) (((q, 48) :: lh_blocks tq tblq sizeq esq ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBSq) = Some (w', []) /\ w' <= wq + wv').
{ unfold lh_blocks. pose proof KIDSq as KIDS'. rewrite Ekvs in KIDS'. change (map (fun e0 : lent => (le_k e0, le_v e0)) esq) with (map kv esq) in KIDS'.
rewrite Ek, EK in KIDS'. pose proof JTX as JTX'. rewrite ECBS, ETBS, Ek, EK in JTX'. unfold lh_blocks in JTX'.
exact (QnPO.Mq1.obj_set_jtx asegs A4F mc kids1 kj kids2 (map kv esq) KBS1 bsj KBS2 PBSq (q, 48) (tq, 56) (tblq, 40 * sizeq) (tblq, 40 * sizeq)
(map (fun e0 : lent => (le_k e0, le_kn e0)) esq) vs VBS wq wv' KIDS' ltac:(clear - Lb1 Lk1; unfold blk in *; lia) ltac:(rewrite length_map, <- Ek; rewrite length_map in Lq1'; exact Lq1') JTX' JTV). }
assert (LBSJ : (length bsj <= length (concat KBSq))%nat) by (clear - EK; rewrite EK, concat_app; cbn [concat]; rewrite !length_app; unfold blk in *; lia).

assert (INtbl : In (tblq, 40 * sizeq) (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply HiT; unfold lh_blocks; right; left; reflexivity).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tblq sizeq (le_ix e') HP3 INtbl TB8 ltac:(lia)) as SHe. rewrite <- HEA in SHe. a4l.
clear MU3 WM3 MI3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs mC) as WM3. pose proof (munch_refl [(EA + 16, EA + 24)] mC) as MU3.
stash KFq. stash K1. stash K2. stash OPBq. stash KIDSq. stash JQ3. stash JOB3. stash JX. stash INV3. stash OWN3. stash DD3.

subst EA. unfold ent_addr. if_falsex. fold (ent_addr tblq (le_ix e')). remember (ent_addr tblq (le_ix e')) as EA eqn:HEA.
step.
step. step. sh_norm. rewrite (div8_add EA 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false.
step.
step.
set (RESTp := (q, 48) :: (tq, 56) :: map (fun e0 : lent => (le_k e0, le_kn e0)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ BS ++ VBS ++ REM ++ LB).

assert (TAIL : forall (x1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (FX : bvmap 5 word) (fcX : bv 32)
(mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (BX : bud) (LX : list blk) (jq : list byte) (jfa jfb : list byte) (wq1 wq2 : word),
HEAPAx AX LX LM ((Fr, 1) :: FRS) BX mX mdX -> Permutation LX ((tblq, 40 * sizeq) :: RESTp) ->
dc_inv mX mdX -> fsaved F FX -> frm0 fcX ->
rw_cells asegs mX (bv_unsigned sp + -192) [C8 (wz 4294967295); C8 (wz 1); C8 (wz Fr); C8 (wz (D / 8 + 2147450880)); C8 (wz Fr); C8 (wz p); C8 (wz SH_A); C8 (wz D); CB 16 jq; C8 (wz Fr)] ->
rw_cells asegs mX Fr [C8 (wz 1102416563); C8 wq1; C8 wq2; CB 8 jfa; C8 (wz v); CB 80 jfb] ->
rw_cells asegs mX (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
dc_dst mX q ->
rw_cells asegs mX EA [C8 (wz (le_k e')); C4 (wz 0); C4 (wz (sv_pad sl)); C8 (wz (le_v e')); C8 (wz (nx_of tblq esq j')); C8 (wz (pv_of tblq esq j'))] ->
ro_cells asegs mX (EA / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
rw_cells asegs mX q [C4 (wz JT_OBJECT); C4 (wz 1); C8 (wz (fn_obj_to_json_string A4F)); C8 (wz pbq); C8 (wz 0); C8 (wz 0); C8 (wz tq)] ->
okids asegs A4F mX kids1 (map kv pre) KBS1 -> okids asegs A4F mX kids2 (map kv post) KBS2 -> opt_pbuf asegs mX PBSq pbq -> jopt asegs A4F vs mX VBS v ->
lh_open asegs A4F mX tq tblq sizeq esq svsq -> stk asegs mX lo (bv_unsigned sp + -192) -> mem_inv asegs mX ->
bD B0 - (acc + wv) <= bD BX ->
bB B0 - DC_KB * (acc + wv) + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS) - Z.of_nat (length bsj)) + PhiO (obj_capA CBS) (Z.of_nat (length kids')) <= bB BX ->
AJ5 A4L HIx AX T mdX
(MS (mkR x1 (wz (bv_unsigned sp + -192)) gp (wz 6434400) u0 u1 u2 sp (wz (bv_unsigned sp + -192)) b0 b1 b2 b3 b4 b5 b6 b7
(wz sh) (wz (EA / 8 + 2147450882)) (wz 2147450880) (wz q) (wz (EA + 16)) (wz (Fr + 32)) (wz (oe_a e)) (wz (q + 40)) (wz (oe_k e)) (wz v) u3 u4 u5 u6)
FX (wz 653904) fcX None mX (seg_rom asegs))).
{ intros x1' u0' u1' u2' b0' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' FX fcX mX mdX AX BX LX jq jfa jfb wq1 wq2.
intros HPX PX INVX FSX FRMX SCRX FFX FSHX DDX SLOTX SHeX HDRX K1X K2X OPBX JOBX OPENX STX MIX BDX BBX.
clear MU3 WM3 MI3 SLOT HP3 ST3.
assert (INtX : In (tblq, 40 * sizeq) LX) by (eapply Permutation_in; [apply Permutation_sym; exact PX | left; reflexivity]).
assert (HiRX : incl RESTp LX) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PX | right; exact Hb]).
assert (HW : Forall (fun iv => exists a n, In (a, n) (LX ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(EA + 16, EA + 24)]).
{ apply Forall_cons; [| apply Forall_nil]. exists tblq, (40 * sizeq). split; [apply in_or_app; left; exact INtX | cbn [fst snd]; lia]. }
pose proof (wmono_refl asegs mX) as WMX. pose proof (munch_refl [(EA + 16, EA + 24)] mX) as MUX.
stash K1X. stash K2X. stash OPBX. stash JOBX. stash OPENX. stash HDRX. stash SCRX. stash FFX. stash FSHX. stash DDX. stash INVX.
reenterA asegs A4L HIx asegs_wx HPX.
step. rewrite ?zxb_zero. step. if_false.
stepz.
step.
rename m into mS.
assert (MUw : munch ([(lo, bv_unsigned sp); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6434236, 6434240)] ++ [(EA + 16, EA + 24)]) mX mS).
{ eapply munch_weaken; [| exact MUX]. unfold sub_fp. cbn [outside app]. intros x Hx. lia. }
assert (HPs : HEAPAx AX LX LM ((Fr, 1) :: FRS) BX mS mdX).
{ eapply (fk1_HEAPA_W _ _ _ _ _ _ _ _ lo (bv_unsigned sp) [(EA + 16, EA + 24)]); [exact HPX | exact LO | exact HT | exact HW | exact MUw | exact WMX | exact MIX]. }
assert (HPr : HEAPAx AX ((tblq, 40 * sizeq) :: RESTp) LM ((Fr, 1) :: FRS) BX mX mdX) by (eapply (heapA_perm A4L HIx); [exact HPX | exact PX | apply Permutation_refl | apply Permutation_refl]).
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPr) as NDr.
assert (NTR : forall k, ~ In (tblq, k) (RESTp ++ LM)) by (intros k; exact (nodup_prefix_suffix [(tblq, 40 * sizeq)] (RESTp ++ LM) tblq (40 * sizeq) k NDr (or_introl eq_refl))).
assert (NTBR : ~ In tblq (map blk_addr (RESTp ++ LM))) by (apply List.NoDup_cons_iff in NDr as [NT _]; exact NT).
clear HPr NDr.
assert (NTB : ~ In (tblq, 40 * sizeq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)).
{ intros Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply (NTR (40 * sizeq)). apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left | right; exact Hin].
unfold RESTp. apply in_app_or in Hin as [Hin|Hin]; right; right; [do 4 (apply in_or_app; right); apply in_or_app; left; exact Hin | do 7 (apply in_or_app; right); exact Hin].
- apply (dc_blk_notfr _ _ _ _ _ _ _ _ _ HPX ltac:(apply in_or_app; left; exact INtX) ltac:(lia)). cbn [fr_ivs flat_map app]. right; right. exact Hin. }
assert (HPRs : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mX mS).
{ eapply (fk1_pres_W _ _ _ _ _ _ _ _ lo (bv_unsigned sp) [(EA + 16, EA + 24)]); [exact HPX | exact LO | clear - LOSu RD0 LO; lia | | | exact MUw | exact WMX].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; apply HiRX; unfold RESTp; right; right; apply in_app_or in Hb as [Hb|Hb]; [do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb | do 7 (apply in_or_app; right); exact Hb] |].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb].
- apply Forall_cons; [| apply Forall_nil]. exists tblq, (40 * sizeq). split; [apply in_or_app; left; exact INtX|]. split; [exact NTB | cbn [fst snd]; lia]. }
unstash INVX. pose proof INVX as (VMXi & PRESXi & _ & SAVEXi & GXi). unfold dc_save in SAVEXi.
assert (SAVEs : dc_save mS).
{ unfold dc_save. eapply (rw_cells_transport asegs); [exact SAVEXi | exact MUX | exact WMX | eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HPX HW); left; cbn [cells_size csize Nat.add]; clear - LOSu RD0 LO; lia]. }
assert (INVs : dc_inv mS mdX).
{ split; [exact VMXi|]. split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESXi | apply (QrIB.Mq0.pres_presxD A4H); exact HPRs] |].
split; [| split; [exact SAVEs|]].
- lazymatch goal with H : stk asegs mS _ _ |- _ => exact H end.
- eapply lh_globA_frame; [exact GXi | exact MUX | exact WMX |]. unfold GHASHA, GSEEDA. apply Forall_cons; [cbn [fst snd]; clear - EAR Hbimg Hblo; lia | apply Forall_nil]. }
unstash SCRX. unstash FFX. unstash FSHX. unstash DDX. unstash HDRX.
assert (OWNs : do_own mS Fr (wz v) 0).
{ exists jq, jfa, jfb, wq1, wq2. unfold Qoif.Mq2.ASP, Qoif.Mq2.dc_scr. split; [| split].
- eapply (rw_cells_transport asegs); [exact SCRX | exact MUX | exact WMX | eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HPX HW); left; cbn [cells_size csize Nat.add]; clear - LOSu RD0 LO; lia].
- eapply (rw_cells_transport asegs); [exact FFX | exact MUX | exact WMX | eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HPX HW); right; left; cbn [cells_size csize Nat.add]; clear; lia].
- eapply (rw_cells_transport asegs); [exact FSHX | exact MUX | exact WMX | eapply (dc_blkW_disj _ _ _ _ _ _ _ _ _ HPX HW); right; right; left; cbn [cells_size csize Nat.add]; clear - D12 D13; unfold sh in *; lia]. }
pose proof (dc_dst_blkW _ _ _ _ _ _ _ _ _ _ HPX HW MUX WMX DDX) as DDs.
assert (AGo : agree_on asegs (others tblq LX) mX mS).
{ eapply (agree_others_of_munch asegs); [exact INtX | | | exact MUX | exact WMX | apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]].
- intros a1' k1 a2' k2 H1 H2 NE. exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPX ltac:(apply in_or_app; left; exact H1) ltac:(apply in_or_app; left; exact H2) NE).
- intros a1' k1 H1. exact (proj1 (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPX ltac:(apply in_or_app; left; exact H1))). }
assert (AGr : agree_on asegs RESTp mX mS).
{ eapply agree_on_incl; [exact AGo|]. intros b Hb. apply in_others_iff. split; [exact (HiRX _ Hb)|].
intros E. apply NTBR. rewrite map_app. apply in_or_app; left. rewrite <- E. exact (in_map blk_addr _ _ Hb). }
unstash K1X. unstash K2X. unstash OPBX. unstash JOBX. unstash OPENX.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K1X AGr ltac:(unfold RESTp; intros b Hb; right; right; apply in_or_app; right; apply in_or_app; left; exact Hb)) as K1s.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K2X AGr ltac:(unfold RESTp; intros b Hb; right; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K2s.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPBX AGr ltac:(unfold RESTp; intros b Hb; right; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPBs.
pose proof (jopt_agree _ _ _ _ _ _ _ _ JOBX AGr ltac:(unfold RESTp; intros b Hb; right; right; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOBs.
apply (rw_cells_agree asegs _ _ _ _ _ HDRX) in AGr as HDRs; [| exists q, 48; split; [left; reflexivity | cbn; lia]].
unstash KFq.
assert (OPENs : lh_open asegs A4F mS tq tblq sizeq (upd esq j' (with_v e' v)) (upd svsq (le_ix e') (sv_with_v sl v))).
{ unfold lh_open. subst EA. eapply (lh_open_set_val asegs A4F); [exact OPENX | exact Hj' | exact Hsl | clear - V0 V1 ACR; lia | exact MUX | exact WMX | | exact SEPq | | exact SLOTX].
- apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
- intros x Hx. destruct (KFq x Hx) as (_ & _ & _ & _ & K5). exact K5. }
set (CBS' := ((q, 48) :: lh_blocks tq tblq sizeq (upd esq j' (with_v e' v)) ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBSq).
assert (LU : length (upd esq j' (with_v e' v)) = length esq) by (apply upd_length).
assert (JQs : jval asegs A4F (Sobj (kids1 ++ vs :: kids2)) mS CBS' q 1).
{ eapply (sobj_close asegs A4F) with (kvs := map kv (upd esq j' (with_v e' v))) (KBS := KBS1 ++ VBS :: KBS2);
[ reflexivity | exact OPBs | unfold jhdr_cells; cbn [app]; exact HDRs
| exists tblq, sizeq, (upd esq j' (with_v e' v)), (upd svsq (le_ix e') (sv_with_v sl v)); split; [reflexivity | split; [reflexivity | exact OPENs]]
| rewrite length_map, LU; clear - Lq1' Ek; rewrite length_map in Lq1'; rewrite Lq1', Ek, !length_app; cbn [length]; lia
| rewrite !length_app; cbn [length]; clear - Lk1 Lb1 Lq2 Ek EK; subst; rewrite !length_app in Lq2; cbn [length] in Lq2; unfold blk in *; lia
| ].
rewrite (kv_upd_v esq j' e' v pre post Hj' Ees Lpre).
apply okids_app; [exact K1s|]. apply (okids_app asegs A4F mS [vs] [(le_k e', v)] [VBS] kids2); [apply okids_one; exact JOBs | exact K2s]. }
assert (HPs' : HEAPAx AX (BS ++ CBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) BX mS mdX).
{ subst CBS'. rewrite (lh_blocks_upd_v tq tblq sizeq esq j' e' v Hj'), concat_mid.
eapply (heapA_perm A4L HIx); [exact HPs | eapply Permutation_trans; [exact PX | unfold RESTp, lh_blocks; unfold blk; perm] | apply Permutation_refl | apply Permutation_refl]. }
assert (CAPs : obj_capA CBS' = sizeq) by (subst CBS'; apply Qkxa.obj_capA_lh; lia).
assert (LENs : Z.of_nat (length CBS') = Z.of_nat (length CBS) + Z.of_nat (length VBS) - Z.of_nat (length bsj)).
{ subst CBS'. rewrite (lh_blocks_upd_v tq tblq sizeq esq j' e' v Hj'), concat_mid, ECBS, ETBS, EK, concat_mid.
clear. cbn [app length]. rewrite !length_app. cbn [length]. unfold blk in *. lia. }
assert (CAPq : obj_capA CBS = sizeq) by (rewrite ECBS, ETBS; apply Qkxa.obj_capA_lh; lia).
unstash JX. destruct JX as (w' & JTXs & Hw').
unstash KADD. pose proof (key_w_pos (oe_kn e)) as KW14.
evt_done5.
eapply KADD with (CBS' := CBS') (REM' := REM);
[ exact INVs | exact FSX | exact FRMX | exact HPs' | exact OWNs | ].
exists (kids1 ++ vs :: kids2), w'.
split; [exact Hq|]. split; [exact DDs|]. split; [exact JQs|].
split; [rewrite Ek in OK; rewrite !okmax_app, !okmax_cons in OK |- *; pose proof (okmax_nonneg kids1); pose proof (okmax_nonneg kids2); pose proof (odep_nonneg vs); clear - OK ODEP H H0 H1; lia|].
split; [subst CBS'; rewrite (lh_blocks_upd_v tq tblq sizeq esq j' e' v Hj'); exact JTXs|]. split; [clear - Hw' WQ WV' KW14; lia|].
rewrite CAPs. replace (Z.of_nat (length (kids1 ++ vs :: kids2))) with (Z.of_nat (length kids')) by (rewrite Ek, !length_app; cbn [length]; reflexivity).
rewrite CAPq in OINV, BBX.
split; [exact OINV|]. split; [clear - CNT KW14 WV4; lia|]. split; [clear - BDX KW14; lia|].
clear - BBX KW14 LENs. unfold blk in *. unfold DC_KB in *. lia. }
stash HDRq. stash SCR2. stash FF2. stash FSH2.
destruct kj as [sj|].
2: {
destruct JO as [Hvo Ebsj].
unstash HDRq. unstash SCR2. unstash FF2. unstash FSH2. unstash INV3. unstash DD3. unstash K1. unstash K2. unstash OPBq. unstash JOB3. unstash OPEN3.
assert (AGc3 : agree_on asegs (BS ++ CBS ++ VBS ++ REM ++ LB) mc mC) by (eapply agree_on_trans; [exact AG2 | exact AG3]).
rewrite Hvo in SLOT, TAIL |- *. if_lit.
evt_done5.
eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mC md2 A2 Bc (BS ++ CBS ++ VBS ++ REM ++ LB) j16' jf1' jf2' w1' w2');
[ exact HP3 | unfold RESTp; rewrite ECBS, ETBS, EK, Ebsj, concat_mid; unfold lh_blocks; unfold blk; perm
| exact INV3 | eapply fsaved_trans; [exact FS | exact FS2] | exact (FRM2 FRM1)
| exact SCR2 | exact FF2 | exact FSH2 | exact DD3 | exact SLOT | exact SHe | exact HDRq
| exact (okids_agree asegs A4F _ _ _ _ _ _ K1 AGc3 ltac:(intros b Hb; apply HiC; rewrite ECBS, EK, concat_app; cbn [app]; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hb))
| exact (okids_agree asegs A4F _ _ _ _ _ _ K2 AGc3 ltac:(intros b Hb; apply HiC; rewrite ECBS, EK, concat_app; cbn [app concat]; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb))
| exact (opt_pbuf_agree asegs _ _ _ _ _ OPBq AGc3 ltac:(intros b Hb; apply HiC; rewrite ECBS; apply in_or_app; right; exact Hb))
| exact JOB3 | exact OPEN3 | exact ST3 | exact MI3
| clear - BDc; lia
| rewrite Ebsj; cbn [length Z.of_nat]; clear - BBc; unfold blk in *; lia ]. }

destruct JO as [Hvo Jo].
if_falsex.
step.
assert (HPp : HEAPAx A2 (bsj ++ ((tblq, 40 * sizeq) :: RESTp)) LM ((Fr, 1) :: FRS) Bc mC md2).
{ eapply (heapA_perm A4L HIx); [exact HP3 | unfold RESTp; rewrite ECBS, ETBS, EK, concat_mid; unfold lh_blocks; unfold blk; perm | apply Permutation_refl | apply Permutation_refl]. }
assert (JoC : jval asegs A4F sj mC bsj (le_v e') 1).
{ eapply jval_agree; [exact Jo | | apply incl_refl]. eapply agree_on_trans; [eapply agree_on_incl; [exact AG2|] | eapply agree_on_incl; [exact AG3|]];
intros b Hb; apply HiC; rewrite ECBS, EK, concat_mid; cbn [app]; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb. }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errs3 & ERRs3).
assert (PC : put_costA (Some sj) 1 bsj <= bB Bc).
{ unfold put_costA. change (1 =? 1) with true. cbv iota. pose proof (PhiO_nonnegW _ _ OINV) as PH0. pose proof (key_w_pos (oe_kn e)) as KW14.
assert (LC : (length (concat KBSq) <= length CBS)%nat) by (rewrite ECBS, ETBS; unfold lh_blocks; cbn [app length]; rewrite !length_app; clear; lia).
clear - BBc ACCW BBWo WV4 PH0 KW14 LBSJ LC. unfold blk in *. unfold DC_KB in *. lia. }
pose proof PUT as PUT'. unfold put_stmt_A, put_stmtA in PUT'.
assert (USP : bv_unsigned (wz (bv_unsigned sp + -192)) = bv_unsigned sp + -192) by (apply unsigned_lit; clear - SPR LOSu LO RD0 ACR; lia).
evt_done5.
eapply PUT' with (s := Some sj) (BS := bsj) (p := le_v e') (rc := 1) (LB := (tblq, 40 * sizeq) :: RESTp) (lo := lo) (errv := errs3);
a4l_goal; rewrite ?USP;
first [ exact HPp | exact ST3 | exact ERRs3 | exact PC | exact LO | reflexivity
| solve [cbn [QPZI.Mq4.put_pre]; split; [exact Hvo | split; [lia | exact JoC]]]
| solve [clear - SPA; Z.div_mod_to_equations; lia] | solve [unfold put_stk_A; clear - LOSu RD0; lia] | solve [clear - HT; lia] | idtac ].
clear PUT'.
intros ms5 md5 A5 (mP & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & OUT5).
destruct RS5 as (yy0 & yy1 & yy2 & yy3 & yy4 & yy5 & yy6 & yy7 & yy8 & yy9 & yy10 & yy11 & yy12 & yy13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST5, HPR5 by (clear - SPR LOSu LO RD0 ACR; lia).
destruct OUT5 as [[_ HP5] | (s'' & _ & Hrc & _)]; [| lia].
unfold put_costA in BB5. change (1 =? 1) with true in BB5. cbv iota in BB5.
replace (ret_pc (wz 653904)) with (wz 653904) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (AG5 : agree_on asegs ((tblq, 40 * sizeq) :: RESTp) mC mP).
{ eapply (agree_of_heap_pres asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_pres_weaken; [exact HPR5 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb]. }
assert (HPRX5 : forall A0 cs0, rw_cells asegs mC A0 cs0 ->
client_range A4H (((tblq, 40 * sizeq) :: RESTp) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs mP A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5 H1 H2). }
unstash INV3. pose proof INV3 as (VM3i & PRES3i & ST3i & SAVE3i & G3i). unfold dc_save in SAVE3i.
unstash SCR2. unstash FF2. unstash FSH2. unstash HDRq. unstash DD3.
apply HPRX5 in SCR2; [| left; clear - LOSu RD0 LO; lia]. apply HPRX5 in SAVE3i; [| left; clear - LOSu RD0 LO; lia].
apply HPRX5 in FF2; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX5 in FSH2; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP3 DD3 HPR5) as DD5.
apply (rw_cells_agree asegs _ _ _ _ _ HDRq) in AG5 as HDR5; [| exists q, 48; split; [right; left; reflexivity | cbn; lia]].
apply (rw_cells_agree asegs _ _ _ _ _ SLOT) in AG5 as SLOT5; [| exists tblq, (40 * sizeq); split; [left; reflexivity | cbn; lia]].
assert (INV5 : dc_inv mP md5).
{ split; [eapply model_vm_only_trans; [exact VM3i | exact VM5] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRES3i |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPR5 | lia |] |].
{ clear. intros b Hb. apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; right; unfold RESTp; right; right | right].
- apply in_app_or in Hb as [Hb | Hb]; [do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb | do 7 (apply in_or_app; right); exact Hb].
- apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST5 |]. split; [unfold dc_save; exact SAVE3i | exact (lh_globA_client _ _ _ _ HPR5 G3i)]. }
unstash K1. unstash K2. unstash OPBq. unstash JOB3. unstash OPEN3. unstash SHe.
assert (PERMp : Permutation (BS ++ CBS ++ VBS ++ REM ++ LB) (bsj ++ ((tblq, 40 * sizeq) :: RESTp))) by (unfold RESTp; rewrite ECBS, ETBS, EK, concat_mid; unfold lh_blocks; unfold blk; perm).
assert (HiR : incl RESTp (BS ++ CBS ++ VBS ++ REM ++ LB)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PERMp | apply in_or_app; right; right; exact Hb]).
assert (AGc5 : agree_on asegs RESTp mc mP).
{ eapply agree_on_trans; [eapply agree_on_incl; [exact AG2 | exact HiR] | eapply agree_on_trans; [eapply agree_on_incl; [exact AG3 | exact HiR] | eapply agree_on_incl; [exact AG5 | intros b Hb; right; exact Hb]]]. }
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K1 AGc5 ltac:(unfold RESTp; intros b Hb; right; right; apply in_or_app; right; apply in_or_app; left; exact Hb)) as K15.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K2 AGc5 ltac:(unfold RESTp; intros b Hb; right; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K25.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPBq AGc5 ltac:(unfold RESTp; intros b Hb; right; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB5.
pose proof (jopt_agree _ _ _ _ _ _ _ _ JOB3 AG5 ltac:(unfold RESTp; intros b Hb; right; right; right; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB5.
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN3 AG5 ltac:(unfold RESTp, lh_blocks; intros b [Hb|[Hb|Hb]]; [right; right; left; exact Hb | left; exact Hb | right; right; right; apply in_or_app; left; exact Hb])) as OPEN5.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tblq sizeq (le_ix e') HP5 ltac:(left; reflexivity) TB8 ltac:(lia)) as SHe5. rewrite <- HEA in SHe5. a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 mP md5 A5 B5 ((tblq, 40 * sizeq) :: RESTp) j16' jf1' jf2' w1' w2');
[ exact HP5 | apply Permutation_refl | exact INV5 | eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS5]] | apply FRM5; apply FRM2; exact FRM1
| exact SCR2 | exact FF2 | exact FSH2 | exact DD5 | exact SLOT5 | exact SHe5 | exact HDR5 | exact K15 | exact K25 | exact OPB5 | exact JOB5 | exact OPEN5 | exact ST5 | exact MI5
| clear - BDc BD5; lia
| pose proof (key_w_pos (oe_kn e)); clear - BBc BB5 H; unfold blk in *; unfold DC_KB in *; lia ].
Qed.

Lemma dc_obj_loop :
forall (n j : nat) (e : oent) (x1 t0 t1 t2 c0 c1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x25 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q acc : Z) (v1 : word) (CBS REM : list blk),
n = (length oes - j)%nat -> nth_error oes j = Some e ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
do_own mc Fr v1 248 -> do_copy mc Bc q CBS acc -> acc + obj_wsum (skipn j okeys) (skipn j ows) = w ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) c0 c1 a2 a3 a4 a5 a6 a7
(wz (Fr / 8 + 2147450880)) x19 (wz 2147450880) x21 x22 (wz (Fr + 32)) (wz (oe_a e)) x25 x26 x27 t3 t4 t5 t6)
F1 (wz 0x9f968) fc1 None mc (seg_rom asegs)).
Proof.
induction n as [|n IHn]; intros until REM; intros Hn He INV FS FRM1 HP OWN COPY ACC.
{ exfalso. assert (L : (j < length oes)%nat) by (apply nth_error_Some; congruence). lia. }
pose proof OWN as (j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof COPY as (kids' & wq & Hq & DD & JQ & OK & JTX & WQ & OINV & CNT & BDc & BBc).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.
assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ REM ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HP HiB OVc He) as (E0 & E8 & E32 & SHe & (pad & ENT) & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32.

destruct OV0 as (EBSo & _ & _ & _ & _ & L1o & L2o & _).
assert (Hj : (j < length oes)%nat) by (apply nth_error_Some; congruence).
pose proof (obj_wsum_skipn okeys ows j (oe_k e) (oe_kn e) (nth j ows 0) ltac:(rewrite nth_error_map, He; reflexivity) ltac:(apply nth_error_nth_len; lia)) as WS1.
pose proof (obj_wsum_nonneg (skipn (S j) okeys) (skipn (S j) ows) (Forall_skipn_nonneg ows (S j) NNWo)) as WS2.
unfold blk in WS1, WS2, ACC.
pose proof (key_w_pos (oe_kn e)) as KW14.
pose proof (PhiO_nonnegW _ _ OINV) as PHI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mc) as MU.
stash PRESi. stash Gi. stash COPY. stash OWN. stash INV. stash OVc. stash AG0. stash JQ. stash DD. stash IHn.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. asan_chkA.
step. step.
stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mk end.
lazymatch goal with MUc : munch _ mc mk, WMc : wmono asegs mc mk, MIc : mem_inv asegs mk |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPc;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STi SAVEi) as INVc;
unstash COPY; pose proof (do_copy_own _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYc; clear COPY
end.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPc HiB INVc) as AGc.
destruct (obj_nowD _ _ _ _ _ _ _ HPc AGc HiB) as (OVk & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HPc HiB OVk He) as (_ & _ & _ & _ & _ & k & bs & Hk & Hbs & BSI & JOk).
pose proof (nth_error_In skids j Hk) as KIN.
destruct COPYc as (kidsc & wqc & Hqc & DDk & JQk & OKc & JTXc & WQc & OINVc & CNTc & BDk & BBk).
destruct k as [sk|].
-
destruct JOk as [Hpk JVk].
destruct (jval_root_in asegs A4F _ _ _ _ _ JVk) as (nk & INk & Hnk).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ nk HP ltac:(apply in_or_app; left; apply HiB; apply BSI; exact INk)) as (_ & Hpkal & Hpklo & Hpkhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpkhi.
step. if_falsex.
step. step. step. step. step. step.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HPc) as (errs & ERRs).
destruct (KW1o j sk bs Hk Hbs) as (Yi & Ri & JTk). set (wk := nth j ows 0) in *.
pose proof (jtx_ge8 _ _ _ _ JTk) as WK8.
set (K1 := concat (firstn j OKBS)). set (K2 := concat (skipn (S j) OKBS)).
assert (EBSk : BS = ((p, 48) :: OTBS ++ K1 ++ bs ++ K2) ++ OPBS) by (rewrite EBSo, (QJlD.concat_nth_split OKBS j bs Hbs); reflexivity).
set (LBk := ((p, 48) :: OTBS ++ K1 ++ K2) ++ OPBS ++ CBS ++ REM ++ LB).
assert (HPk : HEAPAx A (bs ++ LBk) LM ((Fr, 1) :: FRS) Bc mk mdc).
{ eapply (heapA_perm A4L HIx); [exact HPc | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
lazymatch type of FF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF end.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FF) as [FFa FFx]. cbn [cells_size csize Nat.add] in FFx.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FFx) as [FFj FFb]. cbn [cells_size csize Nat.add] in FFb.
replace (Fr + Z.of_nat 32) with (Fr + 32) in FFj, FFb by lia. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
clear FF FFx.
assert (UNP : unpoisoned asegs mk A_SB (Fr + 32) 8).
{ pose proof (unpoisoned_of_fshadow1 mk Fr _ 4 5 (proj2 (proj1 FSH)) eq_refl D6 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl) as U.
change (8 * Z.of_nat 4) with 32 in U. change (8 * Z.of_nat (5 - 4)) with 8 in U. exact U. }
assert (DEPk : sdepth sk + 1 <= rdepth r).
{ rewrite Ero. cbn [rdepth]. rewrite sdepth_Sobj. pose proof (odep_le_okmax skids (Some sk) KIN) as X. cbn [odep] in X. lia. }
assert (WKLT : wk < 2^28) by (pose proof (jtx_nonneg _ _ _ _ JTXc) as WQ0; clear - WLTo WS1 WS2 ACC WQc WQ0 KW14; lia).
evt_done5.
eapply (IHo sk KIN) with (A := A) (LB := LBk) (BS := bs) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (p := oe_v e) (D := Fr + 32) (w := wk) (errv := errs);
[ exact HPk | split; [exact Hpk | exact JVk] | discriminate | exact (proj2 (proj2 (proj2 (proj2 INVc)))) | exact FFj
| exists Fr, 1; split; [left; reflexivity | rewrite fr_size_1; lia]
| exact UNP | clear - D6; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; exact STi | exact LO
| rewrite unsigned_lit by lia; unfold dc_stkA, DC_F, DC_C; cbn [rdepth]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM1
| cbn [length rdepth]; lia
| exists Yi, Ri; exact JTk
| exact WKLT
| unfold DC_KB in *; lia | lia | reflexivity | reflexivity | reflexivity | ].
intros msr mdr mr rvr Ar Br (RSr & VMr & STr & PXr & (errr & ERRr)) Gr JRr (BDr & OUTr).
destruct RSr as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in STr, PXr by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 653752)) with (wz 653752) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (PXR : forall A0 cs0, rw_cells asegs mk A0 cs0 ->
client_rangex A4H (hl_volatile A4H) ((bs ++ LBk) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) ->
(A0 + Z.of_nat (cells_size cs0) <= Fr + 32 \/ Fr + 32 + 8 <= A0) -> rw_cells asegs mr A0 cs0).
{ intros A0 cs0 H1 H2 H3. exact (QrIB.Mq0.presxD_rw_cells A4H _ _ _ _ _ _ _ PXr H1 H2 H3). }
apply PXR in SCR; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in SAVEi; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in FFa; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FFb; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FSH; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]
| cbn [cells_size csize Nat.add]; lia].
clear PXR.
assert (INVr : dc_inv mr mdr).
{ destruct INVc as (VMc & PXc & _ & _ & _).
split; [eapply model_vm_only_trans; [exact VMc | exact VMr] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PXc |] | split; [exact STr | split; [unfold dc_save; exact SAVEi | exact Gr]]].
eapply presxD_own with (D' := Fr + 32); [exact PXr | lia | |].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
+ apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply HiBL; exact Hb].
+ apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- intros x Hx. eapply da_own_outside; [exact HPc | exact HiBL | unfold alloc_ceiling, sp_window_lo, stack_max_size in D8; lia | lia]. }
pose proof (dc_dst_presxD _ _ _ _ _ Fr (Fr + 32) (bs ++ LBk) (bv_unsigned sp + -192) mk mr q HPc ltac:(lia) ltac:(lia) DDk PXr) as DDr.
assert (AGr : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mk mr).
{ intros BSx Hi. eapply presxD_agree_blocks; [exact PXr | |].
- intros b Hb. apply in_or_app; left. apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply Hi; exact Hb].
- intros a0' k0' Hin. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ Fr 1 a0' k0' HPc ltac:(left; reflexivity) ltac:(apply in_or_app; left; apply Hi; exact Hin)) as DF.
rewrite fr_size_1 in DF. lia. }
pose proof (jval_agree asegs A4F _ _ _ _ _ _ _ JQk (AGr CBS ltac:(apply incl_appr; apply incl_appl; apply incl_refl)) (incl_refl _)) as JQr.
clear JVk FFj UNP.
assert (OWNr : forall qk, rw_cells asegs mr (Fr + 32) [C8 (wz qk)] -> do_own mr Fr (wz qk) 0).
{ intros qk DCk. exists j16, jf1, jf2, w1, w2. split; [exact SCR | split; [| exact FSH]].
lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) end.
apply (proj2 (rw_cells_app asegs mr _ _ _)). split; [exact FFa |]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs mr _ _ _)). cbn [cells_size csize Nat.add].
replace (Fr + Z.of_nat 32) with (Fr + 32) by lia. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) by lia. split; [exact DCk | exact FFb]. }
destruct OUTr as [(-> & d & qk & KCBS & KREM & COk & CWk & Hqk & DCk & JRk & BBr & HPr) | (-> & qk & KCBS & KREM & DCk & FRk & BBr & HPr)].
+
destruct COk as (sk' & -> & DEPk'). cbn [dc_cwA] in CWk. destruct CWk as (wk' & JTk' & WK').
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
pose proof (OWNr qk DCk) as OWNa.
clear SCR FFa FFb FSH SAVEi OWNr.
stash INVr. stash OWNa. stash JQr. stash JRk. stash DDr.
try clear MU WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
evt_done5. unstash INVr. unstash OWNa. unstash JQr. unstash JRk. unstash DDr.
eapply (dc_obj_add j e) with (v := qk) (q := q) (acc := acc) (wv := wk) (wq := wqc) (vs := Some sk') (kids' := kidsc) (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact He | exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNa | exact JRk
| cbn [odep]; pose proof (odep_le_okmax skids (Some sk) KIN) as X; cbn [odep] in X; lia
| exists wk'; split; [exact JTk' | exact WK'] | lia
| exact Hqc | exact DDr | exact JQr | exact OKc | exact JTXc | exact WQc | exact OINVc | exact CNTc
| lia | unfold DC_KB in *; lia | lia | ].
intros z1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 z19 z21 z22 z25 z26 z27 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' REM' INV3 FS3 FRM3 HP3 OWN3 COPY3.
eapply (dc_obj_next j e) with (q := q) (acc := acc + wk + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ exact He | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | exact COPY3 | unfold blk; lia | ].
intros e' He' mc' c0' c1' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S j) e') with (q := q) (acc := acc + wk + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ lia | exact He' | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | unfold blk; lia ].
+
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
pose proof (OWNr qk DCk) as OWNa.
assert (HiBa : incl BS (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_now _ _ _ _ _ _ _ _ HPa HiBa INVr) as JRsrc.
clear SCR FFa FFb FSH SAVEi OWNr.
stash INVr. stash OWNa. stash JRsrc. stash JQr. stash FRk. stash DDr.
try clear MU WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6434236, 6434240)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
evt_done5. unstash INVr. unstash OWNa. unstash JRsrc. unstash JQr. unstash FRk. unstash DDr.
eapply dc_obj_fail with (v1 := qk) (q := q) (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNa | exact FRk | exact JRsrc | exact DDr
| right; split; [exact Hqc | exists (Sobj kidsc); exact JQr] | lia | unfold DC_KB in *; lia ].
-
destruct JOk as [Ev Ebs].
rewrite Ev.
step. if_lit.
pose proof (KW2o j Hk) as WKN. rewrite WKN in WS1.
assert (OWNc : do_own mk Fr (wz 0) 0) by (exists j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
evt_done5.
eapply (dc_obj_add j e) with (v := 0) (q := q) (acc := acc) (wv := NULL_W) (wq := wqc) (vs := None) (kids' := kidsc) (VBS := []) (CBS := CBS) (REM := REM);
[ exact He | exact INVc | exact FS | exact FRM1 | exact HPc | exact OWNc | split; reflexivity
| cbn [odep]; apply okmax_nonneg
| exists NULL_W; split; [reflexivity | lia] | unfold NULL_W; lia
| exact Hqc | exact DDk | exact JQk | exact OKc | exact JTXc | exact WQc | exact OINVc | exact CNTc
| unfold NULL_W in *; lia | cbn [length]; unfold DC_KB, NULL_W in *; lia | unfold NULL_W in *; lia | ].
intros z1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 z19 z21 z22 z25 z26 z27 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' REM' INV3 FS3 FRM3 HP3 OWN3 COPY3.
eapply (dc_obj_next j e) with (q := q) (acc := acc + NULL_W + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ exact He | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | exact COPY3 | unfold blk; unfold NULL_W in *; lia | ].
intros e' He' mc' c0' c1' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S j) e') with (q := q) (acc := acc + NULL_W + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ lia | exact He' | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | unfold blk; unfold NULL_W in *; lia ].
Qed.
End MDcObj.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg1M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDwa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDwa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB6X.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB6X.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRcT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRcT.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qeia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qeia.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section MDcObj.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation jroot_repA := (jroot_rep A4H A4F).
Hypothesis SHALLOW : shallow_A_stmt HIx.
Hypothesis PUT : put_stmt_A HIx.

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
Local Notation fk1_HEAPA := (Qoif.Mq6.fk1_HEAPA HIx) (only parsing).
Local Notation fk1_pres := (Qoif.Mq6.fk1_pres HIx) (only parsing).
Local Notation ASP := (Qoif.Mq6.ASP sp) (only parsing).
Local Notation dc_save := (Qoif.Mq6.dc_save ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (only parsing).
Local Notation dc_inv := (Qoif.Mq6.dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D) (only parsing).
Local Notation dc_dst := (Qoif.Mq6.dc_dst D) (only parsing).
Local Notation dc_dfacts := (Qoif.Mq6.dc_dfacts HIx ra sp LM FRS D DLOC DAL) (only parsing).
Local Notation dc_dst_munch := (Qoif.Mq6.dc_dst_munch HIx ra sp LM FRS lo D LO DLOC DAL) (only parsing).
Local Notation dc_dst_presx := (Qoif.Mq6.dc_dst_presx HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_dst_pres := (Qoif.Mq6.dc_dst_pres HIx ra sp LM FRS D DLOC) (only parsing).
Local Notation dc_epi := (Qoif.Mq6.dc_epi HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS HT DLOC NN JR0 Kont) (only parsing).
Local Notation dc_scr := (Qoif.Mq6.dc_scr p) (only parsing).
Local Notation dc_tail0 := (Qoif.Mq6.dc_tail0 HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS SPA HT RA DLOC DAL NN JR0 Kont) (only parsing).
Local Notation da_src_agree := (QRcT.Mq3.da_src_agree HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo D DLOC DAL) (only parsing).
Local Notation da_src_now := (QRcT.Mq3.da_src_now HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB BS LM FRS lo p D r DLOC DAL JR0) (only parsing).
Local Notation dc_inv_own := (QRcT.Mq3.dc_inv_own HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation da_own_outside := (QRcT.Mq3.da_own_outside HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB BS LM FRS B0 lo p D w r T LO LOS NN JR0 Kont) (only parsing).
Local Notation dc_dst_presxD := (QRcT.Mq3.dc_dst_presxD HIx ra sp LM FRS D DLOC DAL) (only parsing).

Local Notation PhiO := (Qiiq.Mq0.PhiO) (only parsing).

Definition do_own (mc : word -> option byte) (Fr : Z) (v1 : word) (b4 : Z) : Prop :=
exists (j16a j8 j16 jf1 jf2 : list byte) (w1 w2 : word),
rw_cells asegs mc ASP (dc_scr Fr (wz 0) j16a (CB 8 j8) j16) /\
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 8 jf1; C8 v1; CB 80 jf2] /\
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 b4); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Variable skids : list (option jshape).
Hypothesis Ero : r = JRtree (Sobj skids).
Hypothesis FRNo : Z.of_nat (length FRS) + (1 + rdepth r) < 4096.
Hypothesis IHo : forall s', In (Some s') skids -> DCOPY HIx (JRtree s').
Variables (opb ot : Z) (OPBS OTBS : list blk) (oes : list oent) (OKBS : list (list blk)) (ows : list Z).
Hypothesis OV0 : obj_view asegs A4F skids m0 BS p 1 opb OPBS ot OTBS oes OKBS.
Hypothesis LWo : length ows = length skids.
Hypothesis EWo : w = 24 + obj_wsum (map (fun e => (oe_k e, oe_kn e)) oes) ows.
Hypothesis NNWo : Forall (fun x => 0 <= x) ows.
Hypothesis KW1o : forall i s bs, nth_error skids i = Some (Some s) -> nth_error OKBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ows 0, Ri).
Hypothesis KW2o : forall i, nth_error skids i = Some None -> nth i ows 0 = NULL_W.
Hypothesis WLTo : w < 2^28.
Hypothesis BBWo : DC_KB * w <= bB B0.
Hypothesis BDWo : w <= bD B0.

Lemma dc_obj_fail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v1 q : Z) (VBS CBS REM : list blk),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
do_own mc Fr (wz v1) 0 -> fresA mc VBS v1 -> jroot_repA r mc BS p ->
dc_dst mc q -> fresA mc CBS q ->
bD B0 - w <= bD Bc -> bB B0 - DC_KB * w + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) <= bB Bc ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) x19 x21 x22 x24 (wz (Fr + 32)) x25 x26 x27 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1aac) fc1 None mc (seg_rom asegs)).
Proof.
intros until REM. intros INV FS FRM1 HP (j16a & j8 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH) FRV JRc DD FRC BDc BBc.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.

assert (PP : exists so, QPZI.Mq4.put_pre A4H A4F so mc VBS v1 1).
{ destruct FRV as [[-> ->] | (Hv & s & JV)]; [exists None; split; reflexivity | exists (Some s); split; [exact Hv | split; [lia | exact JV]]]. }
destruct PP as (so & PP).
assert (HPp : HEAPAx A (VBS ++ (BS ++ CBS ++ REM ++ LB)) LM ((Fr, 1) :: FRS) Bc mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl]. }
assert (V2R : 0 <= v1 < 2^64).
{ destruct FRV as [[-> _] | (Hv & s & JV)]; [lia|]. destruct (jval_root_in asegs A4F _ _ _ _ _ JV) as (n & Hin & Hn).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v1 n HPp ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & Hlo & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
stash PRESi. stash Gi. stash FRC. stash JRc. stash DD.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

assert (PC : put_costA so 1 VBS <= bB Bc).
{ unfold put_costA. destruct so; [change (1 =? 1) with true; cbv iota|]; unfold DC_KB in *; lia. }
evt_done5.
eapply PUT with (LB := BS ++ CBS ++ REM ++ LB) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (errv := errs) (s := so) (BS := VBS) (p := v1) (rc := 1);
[ exact HPp | exact PP | reflexivity | rewrite unsigned_lit by lia; exact STi | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERRs | reflexivity | reflexivity | exact PC | ].
intros ms2 md2 A2 (m2 & rr & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
destruct OUT2 as [[_ HP2] | (s' & _ & Habs & _)]; [| exfalso; lia].
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in HPR2 by lia.
change (hl_segs A4L) with asegs in *.
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_range A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2 H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
unstash DD. pose proof (dc_dst_pres _ _ _ _ _ _ _ _ _ _ _ HP2 DD HPR2) as DD2. clear DD HPRX. stash DD2.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m2) as MU2.
replace (ret_pc (wz 662196)) with (wz 662196) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
stash SAVEi.
reenterA asegs A4L HIx asegs_wx HP2.
step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2 MI2) as HPY.
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP2 LO ltac:(lia) MU2 WM2) as HPR2X.
unstash SAVEi. apply (rw_cells_transport asegs [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] _ mX) in SAVEi; [| exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; lia].
unstash DD2. pose proof (dc_dst_munch _ _ _ _ _ _ _ _ _ HP2 DD2 MU2 WM2) as [DCX DSHX].
assert (HPRcX : heap_pres A4H ((BS ++ CBS ++ REM ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mX).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia |] | eapply heap_pres_weaken; [exact HPR2X | lia | intros b Hb; exact Hb]].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (AGX : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mc mX).
{ intros BSx Hi. eapply (agree_of_heap_pres asegs A4H); [exact HPRcX | reflexivity | intros b Hb; apply in_or_app; left; apply Hi; exact Hb]. }
unstash JRc. unstash PRESi. unstash Gi. unstash FRC.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply (dc_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 (BS ++ CBS ++ REM ++ LB) Fr (2^64 - 1)).
- split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.pres_presxD A4H); eapply heap_pres_weaken; [exact HPRcX | lia |] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
split; [exact ST2 |].
split; [unfold dc_save; exact SAVEi |]. eapply lh_globA_client; [exact HPRcX | exact Gi].
- eapply fsaved_trans; [exact FS | exact FS2].
- apply FRM2. exact FRM1.
- exact HPY.
- exact SCR.
- reflexivity.
- exact FF.
- reflexivity.
- exact FSH.
- eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JRc | apply (AGX BS); apply incl_appl; apply incl_refl | apply incl_refl].
- split; [lia|]. right. split; [reflexivity|]. exists q, CBS, REM. split; [reflexivity|]. split; [exact DCX|].
split; [eapply fresA_agree; [exact FRC | apply (AGX CBS); apply incl_appr; apply incl_appl; apply incl_refl | apply incl_refl] |].
assert (VL : put_costA so 1 VBS <= 512 * Z.of_nat (length VBS)) by (unfold put_costA; destruct so; [change (1 =? 1) with true; cbv iota; lia | destruct PP as [_ ->]; cbn; lia]).
lia.
Qed.

Lemma gran4_nowD : forall A LBa LMx FRS' B mc mdc ab k e,
HEAPAx A LBa LMx FRS' B mc mdc -> In (ab, k) LBa -> ab <= e -> e + 32 <= ab + k -> e mod 8 = 0 ->
ro_cells asegs mc (e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LMx FRS' B mc mdc ab k e HP Hin Hlo Hhi He8.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab k HP ltac:(apply in_or_app; left; exact Hin)) as (_ & Hal & _).
assert (E : forall i, 0 <= i -> e / 8 + 2147450880 + i = ab / 8 + 2147450880 + ((e - ab) / 8 + i)) by (intros i Hi; clear - Hal He8 Hlo; Z.div_mod_to_equations; lia).
assert (G : forall i, 0 <= i <= 3 -> ro_cells asegs mc (e / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)]).
{ intros i Hi. rewrite (E i) by lia. eapply (blk_gran0A HIx _ _ _ _ _ _ _ ab k _ HP Hin); [clear - Hlo Hi; Z.div_mod_to_equations; lia | clear - Hal He8 Hlo Hhi Hi; Z.div_mod_to_equations; lia]. }
pose proof (G 0 ltac:(lia)) as G0. pose proof (G 1 ltac:(lia)) as G1. pose proof (G 2 ltac:(lia)) as G2. pose proof (G 3 ltac:(lia)) as G3.
rewrite Z.add_0_r in G0.
change [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] with ([C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 0)]).
apply ro_cells_app. split; [exact G0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [exact G1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply ro_cells_app. split; [replace (e / 8 + 2147450880 + 1 + 1) with (e / 8 + 2147450880 + 2) by lia; exact G2|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
replace (e / 8 + 2147450880 + 1 + 1 + 1) with (e / 8 + 2147450880 + 3) by lia. exact G3.
Qed.

Lemma obj_nowD : forall A LBa LMx FRS' B mc mdc,
HEAPAx A LBa LMx FRS' B mc mdc -> agree_on asegs BS m0 mc -> incl BS LBa ->
obj_view asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS /\
0 < p /\ p + 48 <= alloc_ceiling /\ p mod 8 = 0 /\
ro_cells asegs mc (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
0 < ot /\ ot mod 8 = 0 /\ ot + 56 <= alloc_ceiling /\
ro_cells asegs mc (ot / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LBa LMx FRS' B mc mdc HP AG INC.
pose proof (obj_view_agree asegs A4F skids m0 mc BS p 1 opb OPBS ot OTBS oes OKBS OV0 AG) as OVc.
destruct (obj_view_tbl asegs A4F skids m0 BS p 1 opb OPBS ot OTBS oes OKBS OV0) as [_ TINB].
assert (INp : In (p, 48) BS) by (destruct OV0 as (EBS & _); rewrite EBS; apply in_or_app; left; left; reflexivity).
assert (INpA : In (p, 48) LBa) by (apply INC; exact INp).
assert (INtA : In (ot, 56) LBa) by (apply INC; exact TINB).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ot 56 HP ltac:(apply in_or_app; left; exact INtA)) as (_ & Htal & Htlo & Hthi & _).
split; [exact OVc|]. split; [exact Hplo|]. split; [exact Hphi|]. split; [clear - Hpal; Z.div_mod_to_equations; lia|].
split.
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH. }
split; [exact Htlo|]. split; [clear - Htal; Z.div_mod_to_equations; lia|]. split; [exact Hthi|].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ ot 56 HP INtA) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
cbn [hl_sb hl_segs hla_base A4L A4H] in SH. exact SH.
Qed.

Lemma ent_nowD : forall A LBa LMx FRS' B mc mdc j e,
HEAPAx A LBa LMx FRS' B mc mdc -> incl BS LBa ->
obj_view asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS -> nth_error oes j = Some e ->
0 < oe_a e /\ oe_a e mod 8 = 0 /\ oe_a e + 32 <= alloc_ceiling /\
ro_cells asegs mc (oe_a e / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] /\
(exists pad : word, rw_cells asegs mc (oe_a e) [C8 (wz (oe_k e)); C4 (wz 0); C4 pad; C8 (wz (oe_v e)); C8 (wz (ohd (skipn (S j) oes)))]) /\
exists k bs, nth_error skids j = Some k /\ nth_error OKBS j = Some bs /\ incl bs BS /\ jopt asegs A4F k mc bs (oe_v e).
Proof.
intros A LBa LMx FRS' B mc mdc j e HP INC OV He.
destruct (obj_view_entry asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS j e OV He) as (EA0 & EA8 & (ba & bk & Hin & Hlo & Hhi) & ENT & k & bs & Hk & Hbs & KOK).
assert (EBS : BS = ((p, 48) :: OTBS ++ concat OKBS) ++ OPBS) by (destruct OV as (E & _); exact E).
assert (INbA : In (ba, bk) LBa) by (apply INC; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bk HP ltac:(apply in_or_app; left; exact INbA)) as (_ & _ & _ & Hbhi & _).
split; [exact EA0|]. split; [exact EA8|]. split; [lia|].
split; [eapply (gran4_nowD _ _ _ _ _ _ _ ba bk (oe_a e) HP INbA); [exact Hlo | exact Hhi | exact EA8] |].
split; [exact ENT|].
exists k, bs. split; [exact Hk|]. split; [exact Hbs|]. split.
- intros b Hb. rewrite EBS. apply in_or_app; left; right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb].
- destruct k; exact KOK.
Qed.
Notation okeys := (map (fun e : oent => (oe_k e, oe_kn e)) oes).

Definition do_copy (mc : word -> option byte) (Bc : bud) (q : Z) (CBS : list blk) (acc : Z) : Prop :=
exists (kids' : list (option jshape)) (wq : Z),
q <> 0 /\ dc_dst mc q /\ jval asegs A4F (Sobj kids') mc CBS q 1 /\ okmax kids' <= okmax skids /\
jtx (Sobj kids') CBS = Some (wq, []) /\ wq <= acc /\
obj_inv (obj_capA CBS) (Z.of_nat (length kids')) /\ 18 * Z.of_nat (length kids') <= acc /\
bD B0 - acc <= bD Bc /\ bB B0 - DC_KB * acc + 512 * Z.of_nat (length CBS) + PhiO (obj_capA CBS) (Z.of_nat (length kids')) <= bB Bc.

Notation own_W Fr := [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 16); (6444156, 6444160)].
Lemma do_copy_own : forall Ax LBx Bx mx mdx Fr mc' Bc q CBS acc,
HEAPAx Ax LBx LM ((Fr, 1) :: FRS) Bx mx mdx -> incl CBS LBx ->
munch (own_W Fr) mx mc' -> wmono asegs mx mc' ->
do_copy mx Bc q CBS acc -> do_copy mc' Bc q CBS acc.
Proof.
intros Ax LBx Bx mx mdx Fr mc' Bc q CBS acc HP Hi MU WM (kids' & wq & Hq & DD & JQ & REST).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof (fk1_pres _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MU WM) as HPR.
exists kids', wq. split; [exact Hq|]. split; [exact (dc_dst_munch _ _ _ _ _ _ _ _ _ HP DD MU WM) |]. split; [| exact REST].
eapply (jval_agree asegs A4F); [exact JQ | | exact Hi].
eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma obj_wsum_skipn_all : forall (keys : list blk) (ws : list Z) n, (length ws <= n)%nat -> obj_wsum (skipn n keys) (skipn n ws) = 0.
Proof. intros keys ws n H. rewrite (skipn_all2 ws) by exact H. destruct (skipn n keys) as [|[? ?] ?]; reflexivity. Qed.

Lemma dc_obj_next :
forall (j : nat) (e : oent) (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 x26 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (Fr q acc : Z) (v1 : word) (CBS REM : list blk),
nth_error oes j = Some e ->
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
do_own m2 Fr v1 0 ->
do_copy m2 B2 q CBS acc -> acc + obj_wsum (skipn (S j) okeys) (skipn (S j) ows) = w ->
(forall e', nth_error oes (S j) = Some e' ->
forall (mc : word -> option byte) (c0 c1 : word),
dc_inv mc md2 -> HEAPAx A2 (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 mc md2 ->
do_own mc Fr v1 248 -> do_copy mc B2 q CBS acc ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) c0 c1 b2 b3 b4 b5 b6 b7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz 0) (wz 2147450880) (wz (Fr + 32)) (wz (oe_a e')) (wz 4294967295) x26 (wz (Fr / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0xa17cc) fc2 None mc (seg_rom asegs))) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) b0 b1 b2 b3 b4 b5 b6 b7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz 0) (wz 2147450880) (wz (Fr + 32)) (wz (oe_a e)) (wz 4294967295) x26 (wz (Fr / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0xa184c) fc2 None m2 (seg_rom asegs)).
Proof.
intros until REM. intros He INV FS FRM2 HP OWN COPY ACC KLOOP.
pose proof OWN as (j16a & j8 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HP HiB OVc He) as (E0 & E8 & E32 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] m2) as MU.
stash PRESi. stash Gi. stash COPY. stash KLOOP. stash OWN. stash INV. stash OVc. stash AG0.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mX end.
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ REM ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
lazymatch goal with MUc : munch _ m2 mX, WMc : wmono asegs m2 mX, MIc : mem_inv asegs mX |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPX;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STi SAVEi) as INVX;
unstash COPY; pose proof (do_copy_own _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYX
end.
assert (OWNX : do_own mX Fr v1 248) by (exists j16a, j8, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).

pose proof (da_src_agree _ _ _ _ _ _ _ _ HPX HiB INVX) as AGX.
destruct (obj_nowD _ _ _ _ _ _ _ HPX AGX HiB) as (OVX & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HPX HiB OVX He) as (_ & _ & _ & SHeX & (padX & ENTX) & _).
stash INVX. stash COPYX. stash OWNX. stash OVX. stash AGX.
step. asan_chkA.
step.
unstash INVX. unstash COPYX. unstash OWNX. unstash OVX. unstash AGX.
rewrite ohd_skipn.
destruct (nth_error oes (S j)) as [e'|] eqn:He'.
-
destruct (ent_nowD _ _ _ _ _ _ _ (S j) e' HPX HiB OVX He') as (E0' & _ & E32' & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32'.
step. if_truex.
evt_done5. unstash KLOOP.
exact (KLOOP e' eq_refl mX _ _ INVX HPX OWNX COPYX).
-
step. if_lit. step.
destruct OVX as (EBSo & _ & HDRX & _).
destruct (proj1 (rw_cells_app asegs mX _ _ _) HDRX) as [HDRX1 _].
destruct COPYX as (kids' & wq & Hq & DDX & JQX & OK & JTX & WQ & OINV & CNT & BDX & BBX).
pose proof (PhiO_nonnegW _ _ OINV) as PHI.
assert (ACC0 : acc = w).
{ rewrite obj_wsum_skipn_all in ACC; [lia |]. apply nth_error_None in He'. rewrite LWo. destruct OV0 as (_ & _ & _ & _ & _ & L1o & _). lia. }
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mX md2 A2 B2 Fr (wz 0) j16a (CB 8 j8) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sobj kids')) q 48 JT_OBJECT (fn_obj_to_json_string A4F) opb CBS REM);
[ exact INVX | exact FS | exact FRM2 | exact HPX | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HPX HiB INVX) | rewrite EBSo; left; reflexivity | lia | exact HDRX1
| rewrite Ero; exists (Sobj kids'); split; [reflexivity | rewrite !sdepth_Sobj; lia]
| cbn [dc_cwA]; exists wq; split; [exact JTX | lia]
| exact Hq | exact DDX | split; [exact Hq | exact JQX]
| lia | unfold DC_KB in *; lia ].
Qed.

Lemma dc_obj :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q : Z) (v1 : word) (CBS : list blk)
(j16a j8 j16 jf1 jf2 : list byte) (w1 w2 : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
rw_cells asegs mc ASP (dc_scr Fr (wz 0) j16a (CB 8 j8) j16) ->
rw_cells asegs mc Fr [C8 (wz 1102416563); C8 w1; C8 w2; CB 8 jf1; C8 v1; CB 80 jf2] ->
rw_cells asegs mc (Fr / 8 + 2147450880) [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sobj []) mc CBS q 1 -> length CBS = 3%nat -> obj_capA CBS = 16 ->
jtx (Sobj []) CBS = Some (24, []) ->
bD B0 - 1 <= bD Bc -> bB B0 - ((16 * 48 + 512) + ((16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512)) <= bB Bc ->
(forall e0, nth_error oes 0 = Some e0 ->
forall (mc' : word -> option byte) (c0 c1 : word),
dc_inv mc' mdc -> HEAPAx A (BS ++ CBS ++ [] ++ LB) LM ((Fr, 1) :: FRS) Bc mc' mdc ->
do_own mc' Fr v1 248 -> do_copy mc' Bc q CBS 24 ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) c0 c1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz 0) (wz 2147450880) (wz (Fr + 32)) (wz (oe_a e0)) (wz 4294967295) s10 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa17cc) fc1 None mc' (seg_rom asegs))) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) (wz p) a1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz Fr) (wz D) x21 (wz 2147450880) (wz p) s8 s9 s10 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1770) fc1 None mc (seg_rom asegs)).
Proof.
intros until w2. intros INV FS FRM1 HP0 SCR FF FSH Hq DD JQ LCBS CAPQ JTXQ BDc BBc KLOOP.
assert (HP : HEAPAx A (BS ++ CBS ++ [] ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc) by exact HP0.
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.
pose proof (obj_wsum_nonneg okeys ows NNWo) as WS0.

assert (HiB : incl BS (BS ++ CBS ++ [] ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & Hp0 & Hp48 & Hp8 & SHpc & Ht0 & Ht8 & Ht56 & SHtc).
pose proof OVc as (EBSo & _ & HDRc & _).
pose proof (obj_view_head asegs A4F skids mc BS p 1 opb OPBS ot OTBS oes OKBS OVc) as HEAD.
assert (INp : In (p, 48) BS) by (rewrite EBSo; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 48 5 HP ltac:(apply HiB; exact INp) ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hp48, Ht56. unfold A_SB in SHtc.
assert (COPY0 : do_copy mc Bc q CBS 24).
{ exists [], 24. split; [exact Hq|]. split; [exact DD|]. split; [exact JQ|].
split; [cbn [okmax]; apply okmax_nonneg|]. split; [exact JTXQ|]. split; [lia|].
rewrite CAPQ. cbn [length Z.of_nat]. split; [exact obj_inv_new|]. split; [lia|]. split; [lia|]. rewrite LCBS. unfold PhiO, DC_KB in *. cbn [Z.of_nat]. lia. }
unfold jhdr_cells in HDRc. cbn [app] in HDRc.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
assert (OHD : ohd oes = match nth_error oes 0%nat with Some x => oe_a x | None => 0 end) by (destruct oes; reflexivity).
rewrite OHD in HEAD. clear OHD.
stash PRESi. stash Gi. stash COPY0. stash INV. stash JQ. stash AG0. stash DD. stash KLOOP. stash OVc.
clear DC DSH.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step.
step. asan_chkA.
step.
step. if_falsex.
step. step. ub_resolve.
step. asan_chkA.
step.
destruct (nth_error oes 0%nat) as [e0|] eqn:He0.
-
unstash OVc. destruct (ent_nowD _ _ _ _ _ _ _ 0%nat e0 HP HiB OVc He0) as (E0 & E8 & E32 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32.
step. if_falsex.
step. step. step. step. step. sh_norm. step.
rewrite ?(unsigned_lit D) by lia. rewrite ?(ub_land7 D DAL). rewrite ?(Z.shiftr_div_pow2 D 3) by lia. change (2 ^ 3) with 8.
assert (OWNX : do_own mc Fr v1 248) by (exists j16a, j8, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
evt_done5. unstash KLOOP. unstash INV. unstash COPY0.
exact (KLOOP e0 eq_refl mc _ _ INV HP OWNX COPY0).
-
step. if_lit.
destruct (proj1 (rw_cells_app asegs mc _ _ _) ltac:(unstash OVc; destruct OVc as (_ & _ & H & _); exact H)) as [HDRg1 _].
assert (W24 : w = 24).
{ rewrite EWo. apply nth_error_None in He0. destruct OV0 as (_ & _ & _ & _ & _ & L1o & _). destruct oes; [| cbn in He0; lia]. reflexivity. }
unstash INV. unstash JQ. unstash DD.
evt_done5.
eapply (dc_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 mc mdc A Bc Fr (wz 0) j16a (CB 8 j8) j16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (JRtree (Sobj [])) q 48 JT_OBJECT (fn_obj_to_json_string A4F) opb CBS []);
[ exact INV | exact FS | exact FRM1 | exact HP | exact SCR | reflexivity | exact FF | reflexivity | exact FSH
| exact (da_src_now _ _ _ _ _ _ _ _ HP HiB INV) | exact INp | lia | exact HDRg1
| rewrite Ero; exists (Sobj []); split; [reflexivity | rewrite !sdepth_Sobj; cbn [okmax]; pose proof (okmax_nonneg skids); lia]
| cbn [dc_cwA]; exists 24; split; [exact JTXQ | lia]
| exact Hq | exact DD | split; [exact Hq | exact JQ]
| lia | rewrite LCBS; unfold DC_KB in *; cbn [Z.of_nat]; lia ].
Qed.

Lemma jtx_empty_obj : forall m CBS q, jval asegs A4F (Sobj []) m CBS q 1 -> length CBS = 3%nat -> jtx (Sobj []) CBS = Some (24, []).
Proof.
intros m CBS q J L3.
destruct (sobj_open asegs A4F _ _ _ _ _ J) as (pbq & PBSq & tq & TBSq & kvs & KBSq & ECBS & _ & _ & LH & L1q & L2q & _).
destruct LH as (tbl & size & es & svs & Hkvs & ETBS & _).
destruct kvs; [| cbn in L1q; lia]. destruct KBSq; [| cbn in L2q; lia].
destruct es; [| cbn in Hkvs; discriminate]. unfold lh_blocks in ETBS. cbn [map app] in ETBS.
subst TBSq. cbn [concat app] in ECBS. rewrite ECBS in L3 |- *. destruct PBSq; [| cbn in L3; lia]. reflexivity.
Qed.

Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= DC_C.
Hypothesis HASH : lh_char_hash_A_stmt HIx (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)) HD.

Definition dc_obj_add_stmt : Prop :=
forall (j : nat) (e : oent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr v q acc wv wq : Z) (vs : option jshape) (kids' : list (option jshape)) (VBS CBS REM : list blk),
nth_error oes j = Some e ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ VBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
do_own mc Fr (wz v) 0 ->
jopt asegs A4F vs mc VBS v -> odep vs <= okmax skids ->
(exists wv', jtx_opt vs VBS = Some (wv', []) /\ wv' <= wv) -> 4 <= wv ->
q <> 0 -> dc_dst mc q -> jval asegs A4F (Sobj kids') mc CBS q 1 -> okmax kids' <= okmax skids ->
jtx (Sobj kids') CBS = Some (wq, []) -> wq <= acc ->
obj_inv (obj_capA CBS) (Z.of_nat (length kids')) -> 18 * Z.of_nat (length kids') <= acc ->
bD B0 - (acc + wv) <= bD Bc ->
bB B0 - DC_KB * (acc + wv) + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS)) + PhiO (obj_capA CBS) (Z.of_nat (length kids')) <= bB Bc ->
acc + wv + key_w (oe_kn e) <= w ->
(forall (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 z26 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (CBS' REM' : list blk),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
HEAPAx A2 (BS ++ CBS' ++ REM' ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2 ->
do_own m2 Fr (wz v) 0 ->
do_copy m2 B2 q CBS' (acc + wv + key_w (oe_kn e)) ->
AJ5 A4L HIx A2 T md2
(MS (mkR y1 (wz ASP) gp (wz A_TP) u0 u1 u2 sp (wz ASP) b0 b1 b2 b3 b4 b5 b6 b7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz 0) (wz 2147450880) (wz (Fr + 32)) (wz (oe_a e)) (wz 4294967295) z26 (wz (Fr / 8 + 2147450880)) u3 u4 u5 u6)
F2 (wz 0xa184c) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) a0 a1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz 0) (wz 2147450880) (wz (Fr + 32)) (wz (oe_a e)) (wz 4294967295) (wz (oe_k e)) (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa1828) fc1 None mc (seg_rom asegs)).

Lemma ins_costB_AB : forall c n, ins_costB c n = Q1Y6.Mq0.ins_costB c n.
Proof. reflexivity. Qed.
Lemma strdup_costB_AB : forall k, strdup_costB k = Qoif.Mq0.strdup_costB k.
Proof. reflexivity. Qed.
Lemma obj_grownA_AB : forall a b c, obj_grownA a b c -> Qoif.Mq0.obj_grownA a b c.
Proof. intros a b c H. exact H. Qed.

Lemma dc_obj_add : dc_obj_add_stmt.
Proof.
unfold dc_obj_add_stmt. intros until REM.
intros He INV FS FRM1 HP OWN JOB ODEP (wv' & JTV & WV') WV4 Hq DD JQ OK JTX WQ OINV CNT BDc BBc ACCW KADD.
pose proof OWN as (j16a & j8 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
pose proof DD as [DC DSH]. pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
set (sh := Fr / 8 + 2147450880) in *.

assert (HiB : incl BS (BS ++ CBS ++ VBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & _).
pose proof OVc as (_ & _ & _ & _ & (_ & _ & OTE) & _).
destruct (OTE j e He) as (_ & _ & _ & _ & CSk & INk & KNk).
assert (INkB : In (oe_k e, oe_kn e) BS) by (destruct OVc as (E & _); rewrite E; apply in_or_app; left; right; apply in_or_app; left; exact INk).
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errs & ERRs).
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [_ BD00].

pose proof (key_w_pos (oe_kn e)) as KW14.
pose proof (PhiO_nonnegW _ _ OINV) as PH0.
assert (CAP29 : obj_capA CBS <= 2^29) by (eapply obj_inv_cap; [exact OINV | lia]).
set (cap' := if lf_thr (obj_capA CBS) <=? Z.of_nat (length kids') then lh_ns (obj_capA CBS) else obj_capA CBS).
assert (GROWN : Qoif.Mq0.obj_grownA (obj_capA CBS) (Z.of_nat (length kids')) cap').
{ subst cap'. unfold Qoif.Mq0.obj_grownA. change Q1Y6.Mq0.lh_ns with lh_ns.
destruct (Z.leb_spec (lf_thr (obj_capA CBS)) (Z.of_nat (length kids'))); [right | left]; split; [reflexivity | lia | reflexivity | lia]. }
destruct (potential_step_obj_add _ _ _ OINV CAP29 GROWN) as [PST OINV'].
pose proof (PhiO_nonnegW _ _ OINV') as PH1.
pose proof (pair_budget (Z.of_nat (length (oe_ks e))) ltac:(lia)) as PB.
assert (KWM : key_w (Z.of_nat (length (oe_ks e)) + 1) <= key_w (oe_kn e)) by (destruct CSk as (Lk & _); unfold key_w; lia).
rewrite <- ins_costB_AB in PST. rewrite <- strdup_costB_AB in PB.
assert (COST : oadd_costB (Z.of_nat (length (oe_ks e))) (obj_capA CBS) (Z.of_nat (length kids')) + 512 + 512 * (Z.of_nat (length CBS) + Z.of_nat (length VBS))
+ PhiO cap' (Z.of_nat (length kids') + 1) <= bB Bc).
{ unfold oadd_costB. unfold DC_KOBJ in PB, PST. unfold DC_KB in *. clear - PB PST PH0 PH1 KWM KW14 BBc ACCW BBWo WV4. nia. }
assert (INS0 : 0 <= ins_costB (obj_capA CBS) (Z.of_nat (length kids'))).
{ pose proof (lf_sizes_pos _ (proj1 OINV)) as C16. unfold ins_costB, resize_costB, lh_ns.
destruct (lf_thr (obj_capA CBS) <=? Z.of_nat (length kids')); [destruct (obj_capA CBS <=? 2 ^ 29); lia | lia]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
stash PRESi. stash Gi. stash OWN. stash INV. stash JQ. stash JOB. stash KADD. stash OVc. stash AG0.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. if_lit.
step. rewrite ?zxb_zero. step. if_lit.
step. step. step. step. step.
unstash Gi. unstash JQ. unstash JOB.
evt_done5.
eapply (json_object_object_add_ex0_A_cps HIx PUT LF OBL_AMEMSET OBL_ISTRCMP HD HD_ge HASH)
with (OBS := CBS) (VBS := VBS) (LB := BS ++ REM ++ LB) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (p := q) (v := v)
(k := oe_k e) (kn := oe_kn e) (ks := oe_ks e) (kids := kids') (vs := vs) (errv := errs);
[ unfold jo_preA; rewrite ?unsigned_lit by lia;
split; [eapply (heapA_perm A4L HIx); [exact HP | perm | apply Permutation_refl | apply Permutation_refl] |];
split; [exact STi|]; split; [exact LO|]; split; [unfold DC_C in HD_le; lia|]; split; [clear - SPA; Z.div_mod_to_equations; lia|]; split; [lia|];
split; [exact ERRs|]; split; reflexivity
| exact Gi | exact JQ | exact JOB | apply in_or_app; left; exact INkB | exact CSk | exact KNk | exact FRM1
| cbn [length]; clear - FRNo RD0; lia
| reflexivity | reflexivity | reflexivity | reflexivity
| clear - COST PH1; lia | clear - COST PH1 INS0; unfold oadd_costB, strdup_costB in *; lia | exact BD00 | ].

intros ms2 md2 m2 rr A2 B2 (RS2 & VM2 & ST2 & HPR2 & (e2 & ERR2)) G2 BD2 OUT2.
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in ST2, HPR2 by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 661576)) with (wz 661576) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HPRX : forall A0 cs0, rw_cells asegs mc A0 cs0 ->
client_rangex A4H a4_volatile ((BS ++ REM ++ LB) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) -> rw_cells asegs m2 A0 cs0).
{ intros A0 cs0 H1 H2. exact (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2 H1 H2). }
apply HPRX in SCR; [| left; lia]. apply HPRX in SAVEi; [| left; lia].
apply HPRX in FF; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]].
apply HPRX in FSH; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]].
pose proof (dc_dst_presx _ _ _ _ _ _ _ _ _ _ _ _ HP DD HPR2) as DD2. clear HPRX.
unstash PRESi. unstash INV.
assert (INV2 : dc_inv m2 md2).
{ split; [eapply model_vm_only_trans; [exact VMi | exact VM2] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PRESi |]; apply (QrIB.Mq0.presx_presxD A4H); eapply heap_presx_weaken; [exact HPR2 | lia | | intros a0' Xa; exact Xa] |].
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
- apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [exact ST2 |]. split; [unfold dc_save; exact SAVEi | exact G2]. }
assert (OWN2 : do_own m2 Fr (wz v) 0) by (exists j16a, j8, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
clear MU WM MI.
destruct OUT2 as [(-> & OBS' & kids'' & JQ' & HP' & LEN' & OK' & CASES) | (-> & REM' & JQ' & JOB' & HP' & BB')].
-
assert (HPn : HEAPAx A2 (BS ++ OBS' ++ REM ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP' | perm | apply Permutation_refl | apply Permutation_refl]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPn) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [] m2) as MU2.
stash INV2. stash OWN2. stash JQ'. stash DD2.
reenterA asegs A4L HIx asegs_wx HPn.
step. if_lit.
evt_done5. unstash INV2. unstash OWN2. unstash JQ'. unstash DD2. unstash KADD.
eapply KADD with (CBS' := OBS') (REM' := REM);
[ exact INV2 | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPn | exact OWN2 | ].
destruct CASES as [(LENn & BBn & LOBS & GRn & JTn) | (LENn & BBn & LOBS & CAPn & JTn)].
+
destruct (potential_step_obj_add _ _ _ OINV CAP29 (obj_grownA_AB _ _ _ GRn)) as [PSTn OINVn].
rewrite <- ins_costB_AB in PSTn. pose proof (PhiO_nonnegW _ _ OINVn) as PHn.
exists kids'', (wq + (key_w (Z.of_nat (length (oe_ks e)) + 1) + wv')).
split; [exact Hq|]. split; [exact DD2|]. split; [exact JQ'|]. split; [cbn [odep] in OK'; destruct vs; cbn [odep] in OK', ODEP; lia|].
split; [exact (JTn wq wv' JTX JTV)|]. split; [lia|].
split; [rewrite LENn; exact OINVn|]. split; [lia|]. split; [lia|].
rewrite LENn. unfold oadd_costB in BBn. unfold DC_KOBJ in PB, PSTn. unfold DC_KB in *. unfold blk in *.
clear - BBn BBc PB PSTn PHn PH0 KWM KW14 ACCW BBWo WV4 LOBS. lia.
+
destruct (JTn wq wv' JTX JTV) as (w' & JT' & W').
exists kids'', w'.
split; [exact Hq|]. split; [exact DD2|]. split; [exact JQ'|]. split; [cbn [odep] in OK'; destruct vs; cbn [odep] in OK', ODEP; lia|].
split; [exact JT'|]. split; [lia|].
split; [rewrite LENn, CAPn; exact OINV|]. split; [lia|]. split; [lia|].
rewrite LENn, CAPn. unfold DC_KB in *. unfold blk in *.
clear - BBn BBc PH0 KW14 ACCW BBWo WV4 LOBS. lia.
-
assert (HPn : HEAPAx A2 (BS ++ CBS ++ VBS ++ (REM' ++ REM) ++ LB) LM ((Fr, 1) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP' | perm | apply Permutation_refl | apply Permutation_refl]. }
assert (JRs2 : jroot_repA r m2 BS p) by (eapply da_src_now; [exact HPn | intros b Hb; apply in_or_app; left; exact Hb | exact INV2]).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPn) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof (wmono_refl asegs m2) as WM2. pose proof (munch_refl [] m2) as MU2.
stash INV2. stash OWN2. stash JQ'. stash JOB'. stash DD2. stash JRs2.
reenterA asegs A4L HIx asegs_wx HPn.
replace (wz (2 ^ 64 - 1)) with (wz (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_lit.
evt_done5. unstash INV2. unstash OWN2. unstash JQ'. unstash JOB'. unstash DD2. unstash JRs2.
eapply dc_obj_fail with (v1 := v) (q := q) (VBS := VBS) (CBS := CBS) (REM := REM' ++ REM);
[ exact INV2 | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPn | exact OWN2
| destruct vs as [sv|]; [right; split; [exact (proj1 JOB') | exists sv; exact (proj2 JOB')] | left; exact JOB'] | exact JRs2 | exact DD2
| right; split; [exact Hq | exists (Sobj kids'); exact JQ'] | lia | ].
unfold oadd_costB in BB'. unfold DC_KOBJ in PB, PST. unfold DC_KB in *. unfold blk in *.
clear - BB' BBc PB PST PH0 PH1 KWM KW14 ACCW BBWo WV4. lia.
Qed.

Lemma dc_obj_loop :
forall (n j : nat) (e : oent) (x1 t0 t1 t2 c0 c1 a2 a3 a4 a5 a6 a7 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A : ASA A4L HIx) (Bc : bud) (Fr q acc : Z) (v1 : word) (CBS REM : list blk),
n = (length oes - j)%nat -> nth_error oes j = Some e ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
HEAPAx A (BS ++ CBS ++ REM ++ LB) LM ((Fr, 1) :: FRS) Bc mc mdc ->
do_own mc Fr v1 248 -> do_copy mc Bc q CBS acc -> acc + obj_wsum (skipn j okeys) (skipn j ows) = w ->
AJ5 A4L HIx A T mdc
(MS (mkR x1 (wz ASP) gp (wz A_TP) t0 t1 t2 sp (wz ASP) c0 c1 a2 a3 a4 a5 a6 a7
(wz Fr) (wz (D / 8 + 2147450880)) (wz D) (wz 0) (wz 2147450880) (wz (Fr + 32)) (wz (oe_a e)) (wz 4294967295) x26 (wz (Fr / 8 + 2147450880)) t3 t4 t5 t6)
F1 (wz 0xa17cc) fc1 None mc (seg_rom asegs)).
Proof.
induction n as [|n IHn]; intros until REM; intros Hn He INV FS FRM1 HP OWN COPY ACC.
{ exfalso. assert (L : (j < length oes)%nat) by (apply nth_error_Some; congruence). lia. }
pose proof OWN as (j16a & j8 & j16 & jf1 & jf2 & w1 & w2 & SCR & FF & FSH).
pose proof INV as (VMi & PRESi & STi & SAVEi & Gi). unfold dc_save in SAVEi.
pose proof COPY as (kids' & wq & Hq & DD & JQ & OK & JTX & WQ & OINV & CNT & BDc & BBc).
pose proof LOS as LOSu. unfold dc_stkA, DC_F, DC_C in LOSu. unfold ASP, dc_scr in *.
assert (RD0 : 0 <= rdepth r) by (destruct r; cbn [rdepth]; try lia; apply sdepth_nonneg).
pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (dc_dfacts _ _ _ _ _ _ HP) as (D1 & D2 & D3 & D4 & DBLK & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13).
set (sh := Fr / 8 + 2147450880) in *.
assert (HiB : incl BS (BS ++ CBS ++ REM ++ LB)) by (apply incl_appl; apply incl_refl).
assert (HiBL : incl (BS ++ LB) (BS ++ CBS ++ REM ++ LB)).
{ intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
pose proof (da_src_agree _ _ _ _ _ _ _ _ HP HiB INV) as AG0.
destruct (obj_nowD _ _ _ _ _ _ _ HP AG0 HiB) as (OVc & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HP HiB OVc He) as (E0 & E8 & E32 & SHe & (pad & ENT) & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in E32.

destruct OV0 as (EBSo & _ & _ & _ & _ & L1o & L2o & _).
assert (Hj : (j < length oes)%nat) by (apply nth_error_Some; congruence).
pose proof (obj_wsum_skipn okeys ows j (oe_k e) (oe_kn e) (nth j ows 0) ltac:(rewrite nth_error_map, He; reflexivity) ltac:(apply nth_error_nth_len; lia)) as WS1.
pose proof (obj_wsum_nonneg (skipn (S j) okeys) (skipn (S j) ows) (Forall_skipn_nonneg ows (S j) NNWo)) as WS2.
unfold blk in WS1, WS2, ACC.
pose proof (key_w_pos (oe_kn e)) as KW14.
pose proof (PhiO_nonnegW _ _ OINV) as PHI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mc) as MU.
stash PRESi. stash Gi. stash COPY. stash OWN. stash INV. stash OVc. stash AG0. stash JQ. stash DD. stash IHn.
unfold A_TP. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step. ub_resolve.
asan_chk0.
step. asan_chkA.
step. step.
stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into mk end.
lazymatch goal with MUc : munch _ mc mk, WMc : wmono asegs mc mk, MIc : mem_inv asegs mk |- _ =>
pose proof (fk1_HEAPA _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -104) _ HP LO ltac:(lia) MUc WMc MIc) as HPc;
unstash INV; pose proof (dc_inv_own _ _ _ _ _ _ _ HP HiBL MUc WMc INV STi SAVEi) as INVc;
unstash COPY; pose proof (do_copy_own _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply incl_appr; apply incl_appl; apply incl_refl) MUc WMc COPY) as COPYc; clear COPY
end.
pose proof (da_src_agree _ _ _ _ _ _ _ _ HPc HiB INVc) as AGc.
destruct (obj_nowD _ _ _ _ _ _ _ HPc AGc HiB) as (OVk & _).
destruct (ent_nowD _ _ _ _ _ _ _ j e HPc HiB OVk He) as (_ & _ & _ & _ & _ & k & bs & Hk & Hbs & BSI & JOk).
pose proof (nth_error_In skids j Hk) as KIN.
destruct COPYc as (kidsc & wqc & Hqc & DDk & JQk & OKc & JTXc & WQc & OINVc & CNTc & BDk & BBk).
destruct k as [sk|].
-
destruct JOk as [Hpk JVk].
destruct (jval_root_in asegs A4F _ _ _ _ _ JVk) as (nk & INk & Hnk).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ nk HP ltac:(apply in_or_app; left; apply HiB; apply BSI; exact INk)) as (_ & Hpkal & Hpklo & Hpkhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpkhi.
step. if_falsex.
step. step. step. step. step. step.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HPc) as (errs & ERRs).
destruct (KW1o j sk bs Hk Hbs) as (Yi & Ri & JTk). set (wk := nth j ows 0) in *.
pose proof (jtx_ge8 _ _ _ _ JTk) as WK8.
set (K1 := concat (firstn j OKBS)). set (K2 := concat (skipn (S j) OKBS)).
assert (EBSk : BS = ((p, 48) :: OTBS ++ K1 ++ bs ++ K2) ++ OPBS) by (rewrite EBSo, (QJlD.concat_nth_split OKBS j bs Hbs); reflexivity).
set (LBk := ((p, 48) :: OTBS ++ K1 ++ K2) ++ OPBS ++ CBS ++ REM ++ LB).
assert (HPk : HEAPAx A (bs ++ LBk) LM ((Fr, 1) :: FRS) Bc mk mdc).
{ eapply (heapA_perm A4L HIx); [exact HPc | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
lazymatch type of FF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF end.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FF) as [FFa FFx]. cbn [cells_size csize Nat.add] in FFx.
destruct (proj1 (rw_cells_app asegs mk _ _ _) FFx) as [FFj FFb]. cbn [cells_size csize Nat.add] in FFb.
replace (Fr + Z.of_nat 32) with (Fr + 32) in FFj, FFb by lia. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
clear FF FFx.
assert (UNP : unpoisoned asegs mk A_SB (Fr + 32) 8).
{ pose proof (QRcT.Mq3.unpoisoned_of_fshadow1 mk Fr _ 4 5 (proj2 (proj1 FSH)) eq_refl D6 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl) as U.
change (8 * Z.of_nat 4) with 32 in U. change (8 * Z.of_nat (5 - 4)) with 8 in U. exact U. }
assert (DEPk : sdepth sk + 1 <= rdepth r).
{ rewrite Ero. cbn [rdepth]. rewrite sdepth_Sobj. pose proof (odep_le_okmax skids (Some sk) KIN) as X. cbn [odep] in X. lia. }
assert (WKLT : wk < 2^28) by (pose proof (jtx_nonneg _ _ _ _ JTXc) as WQ0; clear - WLTo WS1 WS2 ACC WQc WQ0 KW14; lia).
evt_done5.
eapply (IHo sk KIN) with (A := A) (LB := LBk) (BS := bs) (LM := LM) (FRS := (Fr, 1) :: FRS) (B := Bc) (lo := lo) (p := oe_v e) (D := Fr + 32) (w := wk) (errv := errs);
[ exact HPk | split; [exact Hpk | exact JVk] | discriminate | exact (proj2 (proj2 (proj2 (proj2 INVc)))) | exact FFj
| exists Fr, 1; split; [left; reflexivity | rewrite fr_size_1; lia]
| exact UNP | clear - D6; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; exact STi | exact LO
| rewrite unsigned_lit by lia; unfold dc_stkA, DC_F, DC_C; cbn [rdepth]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| exact ERRs | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM1
| cbn [length rdepth]; lia
| exists Yi, Ri; exact JTk
| exact WKLT
| unfold DC_KB in *; lia | lia | reflexivity | reflexivity | reflexivity | ].
intros msr mdr mr rvr Ar Br (RSr & VMr & STr & PXr & (errr & ERRr)) Gr JRr (BDr & OUTr).
destruct RSr as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?(unsigned_lit (bv_unsigned sp + -192)) in STr, PXr by lia.
change (hl_segs A4L) with asegs in *.
replace (ret_pc (wz 661540)) with (wz 661540) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (PXR : forall A0 cs0, rw_cells asegs mk A0 cs0 ->
client_rangex A4H (hl_volatile A4H) ((bs ++ LBk) ++ LM ++ fr_ivs A4L ((Fr, 1) :: FRS)) (bv_unsigned sp + -192) A0 (Z.of_nat (cells_size cs0)) ->
(A0 + Z.of_nat (cells_size cs0) <= Fr + 32 \/ Fr + 32 + 8 <= A0) -> rw_cells asegs mr A0 cs0).
{ intros A0 cs0 H1 H2 H3. exact (QrIB.Mq0.presxD_rw_cells A4H _ _ _ _ _ _ _ PXr H1 H2 H3). }
apply PXR in SCR; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in SAVEi; [| left; lia | cbn [cells_size csize Nat.add]; lia].
apply PXR in FFa; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FFb; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn [fr_base fst]; lia | cbn [cells_size csize Nat.add fr_base fr_class fst snd]; rewrite fr_size_1; lia]
| cbn [cells_size csize Nat.add]; lia].
apply PXR in FSH; [| eapply client_rangex_block; [apply in_or_app; right; apply in_or_app; right; right; left; reflexivity | unfold shad; cbn [fr_base fst hl_sb A4L]; unfold A_SB; fold sh; lia
| unfold shad; cbn [cells_size csize Nat.add fr_base fr_class fst snd hl_sb A4L]; rewrite fr_shadow_len_1; unfold A_SB; fold sh; lia]
| cbn [cells_size csize Nat.add]; lia].
clear PXR.
assert (INVr : dc_inv mr mdr).
{ destruct INVc as (VMc & PXc & _ & _ & _).
split; [eapply model_vm_only_trans; [exact VMc | exact VMr] |].
split; [eapply (QrIB.Mq0.presxD_trans A4H); [exact PXc |] | split; [exact STr | split; [unfold dc_save; exact SAVEi | exact Gr]]].
eapply presxD_own with (D' := Fr + 32); [exact PXr | lia | |].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left | apply in_or_app; right].
+ apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply HiBL; exact Hb].
+ apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- intros x Hx. eapply da_own_outside; [exact HPc | exact HiBL | unfold alloc_ceiling, sp_window_lo, stack_max_size in D8; lia | lia]. }
pose proof (dc_dst_presxD _ _ _ _ _ Fr (Fr + 32) (bs ++ LBk) (bv_unsigned sp + -192) mk mr q HPc ltac:(lia) ltac:(lia) DDk PXr) as DDr.
assert (AGr : forall BSx, incl BSx (BS ++ CBS ++ REM ++ LB) -> agree_on asegs BSx mk mr).
{ intros BSx Hi. eapply presxD_agree_blocks; [exact PXr | |].
- intros b Hb. apply in_or_app; left. apply (Permutation_in b (l := BS ++ CBS ++ REM ++ LB)); [rewrite EBSk; unfold LBk; perm | apply Hi; exact Hb].
- intros a0' k0' Hin. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ Fr 1 a0' k0' HPc ltac:(left; reflexivity) ltac:(apply in_or_app; left; apply Hi; exact Hin)) as DF.
rewrite fr_size_1 in DF. lia. }
pose proof (jval_agree asegs A4F _ _ _ _ _ _ _ JQk (AGr CBS ltac:(apply incl_appr; apply incl_appl; apply incl_refl)) (incl_refl _)) as JQr.
clear JVk FFj UNP.
assert (OWNr : forall qk, rw_cells asegs mr (Fr + 32) [C8 (wz qk)] -> do_own mr Fr (wz qk) 0).
{ intros qk DCk. exists j16a, j8, j16, jf1, jf2, w1, w2. split; [exact SCR | split; [| exact FSH]].
lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) end.
apply (proj2 (rw_cells_app asegs mr _ _ _)). split; [exact FFa |]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs mr _ _ _)). cbn [cells_size csize Nat.add].
replace (Fr + Z.of_nat 32) with (Fr + 32) by lia. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) by lia. split; [exact DCk | exact FFb]. }
destruct OUTr as [(-> & d & qk & KCBS & KREM & COk & CWk & Hqk & DCk & JRk & BBr & HPr) | (-> & qk & KCBS & KREM & DCk & FRk & BBr & HPr)].
+
destruct COk as (sk' & -> & DEPk'). cbn [dc_cwA] in CWk. destruct CWk as (wk' & JTk' & WK').
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
pose proof (OWNr qk DCk) as OWNa.
clear SCR FFa FFb FSH SAVEi OWNr.
stash INVr. stash OWNa. stash JQr. stash JRk. stash DDr.
try clear MU WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
evt_done5. unstash INVr. unstash OWNa. unstash JQr. unstash JRk. unstash DDr.
eapply (dc_obj_add j e) with (v := qk) (q := q) (acc := acc) (wv := wk) (wq := wqc) (vs := Some sk') (kids' := kidsc) (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact He | exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNa | exact JRk
| cbn [odep]; pose proof (odep_le_okmax skids (Some sk) KIN) as X; cbn [odep] in X; lia
| exists wk'; split; [exact JTk' | exact WK'] | lia
| exact Hqc | exact DDr | exact JQr | exact OKc | exact JTXc | exact WQc | exact OINVc | exact CNTc
| lia | unfold DC_KB in *; lia | lia | ].
intros z1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 z26 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' REM' INV3 FS3 FRM3 HP3 OWN3 COPY3.
eapply (dc_obj_next j e) with (q := q) (acc := acc + wk + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ exact He | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | exact COPY3 | unfold blk; lia | ].
intros e' He' mc' c0' c1' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S j) e') with (q := q) (acc := acc + wk + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ lia | exact He' | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | unfold blk; lia ].
+
assert (HPa : HEAPAx Ar (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB) LM ((Fr, 1) :: FRS) Br mr mdr).
{ eapply (heapA_perm A4L HIx); [exact HPr | rewrite EBSk; unfold LBk; perm | apply Permutation_refl | apply Permutation_refl]. }
pose proof (OWNr qk DCk) as OWNa.
assert (HiBa : incl BS (BS ++ CBS ++ KCBS ++ (KREM ++ REM) ++ LB)) by (apply incl_appl; apply incl_refl).
pose proof (da_src_now _ _ _ _ _ _ _ _ HPa HiBa INVr) as JRsrc.
clear SCR FFa FFb FSH SAVEi OWNr.
stash INVr. stash OWNa. stash JRsrc. stash JQr. stash FRk. stash DDr.
try clear MU WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPa) as MIr. change (hl_segs A4L) with asegs in MIr.
pose proof (wmono_refl asegs mr) as WMr. pose proof (munch_refl [(lo, bv_unsigned sp + -104); (Fr, Fr + 120); (sh, sh + 16); (6444156, 6444160)] mr) as MUr.
reenterA asegs A4L HIx asegs_wx HPa.
step. if_lit.
evt_done5. unstash INVr. unstash OWNa. unstash JRsrc. unstash JQr. unstash FRk. unstash DDr.
eapply dc_obj_fail with (v1 := qk) (q := q) (VBS := KCBS) (CBS := CBS) (REM := KREM ++ REM);
[ exact INVr | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM1 | exact HPa | exact OWNa | exact FRk | exact JRsrc | exact DDr
| right; split; [exact Hqc | exists (Sobj kidsc); exact JQr] | lia | unfold DC_KB in *; lia ].
-
destruct JOk as [Ev Ebs].
rewrite Ev.
step. if_lit.
pose proof (KW2o j Hk) as WKN. rewrite WKN in WS1.
assert (OWNc : do_own mk Fr (wz 0) 0) by (exists j16a, j8, j16, jf1, jf2, w1, w2; split; [exact SCR | split; [exact FF | exact FSH]]).
evt_done5.
eapply (dc_obj_add j e) with (v := 0) (q := q) (acc := acc) (wv := NULL_W) (wq := wqc) (vs := None) (kids' := kidsc) (VBS := []) (CBS := CBS) (REM := REM);
[ exact He | exact INVc | exact FS | exact FRM1 | exact HPc | exact OWNc | split; reflexivity
| cbn [odep]; apply okmax_nonneg
| exists NULL_W; split; [reflexivity | lia] | unfold NULL_W; lia
| exact Hqc | exact DDk | exact JQk | exact OKc | exact JTXc | exact WQc | exact OINVc | exact CNTc
| unfold NULL_W in *; lia | cbn [length]; unfold DC_KB, NULL_W in *; lia | unfold NULL_W in *; lia | ].
intros z1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 z26 u3 u4 u5 u6 F3 fc3 m3 md3 A3 B3 CBS' REM' INV3 FS3 FRM3 HP3 OWN3 COPY3.
eapply (dc_obj_next j e) with (q := q) (acc := acc + NULL_W + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ exact He | exact INV3 | exact FS3 | exact FRM3 | exact HP3 | exact OWN3 | exact COPY3 | unfold blk; unfold NULL_W in *; lia | ].
intros e' He' mc' c0' c1' INV' HP' OWN' COPY'. unstash IHn.
eapply (IHn (S j) e') with (q := q) (acc := acc + NULL_W + key_w (oe_kn e)) (CBS := CBS') (REM := REM');
[ lia | exact He' | exact INV' | exact FS3 | exact FRM3 | exact HP' | exact OWN' | exact COPY' | unfold blk; unfold NULL_W in *; lia ].
Qed.
End MDcObj.
End RC__1.
