(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QBxa Q6q3 QEpW QWxq_c1 QZDE Qc3B Q7UD Qwm6 QZsi Q0TL Q2y2 QdM4 QS67 QpzM QteI QbVh QQIi Qc6I QJFf Qsn5 QBrp Q2ui Q1KO QwAs QlES QCiC Qpj5 QdZp Qk8e QNqr QCrt QgTJ QRGF QmAH QvG1 Qu3b QnRU Q9Ho QQNJ QSLK Qa5v QnaW QQ8H Qx6U Q8zl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.

Import QQIi.
Import Qc6I QJFf Qsn5 QBrp Q2ui Q1KO.

Import QlES.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition file_cellsO (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list QbVh.cell :=
[QbVh.C4 flags; QbVh.C4 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0xd2884);
QbVh.C8 (Z_to_bv 64 wend); QbVh.C8 (Z_to_bv 64 wpos); QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 wbase); QbVh.C8 (Z_to_bv 64 0);
QbVh.C8 (Z_to_bv 64 writefn); QbVh.C8 (Z_to_bv 64 0xd29c8); QbVh.C8 (Z_to_bv 64 buf); QbVh.C8 (Z_to_bv 64 bufsize);
QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C4 (Z_to_bv 64 fd); QbVh.C4 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C4 mode; QbVh.C4 (Z_to_bv 64 0xffffffff); QbVh.C4 (Z_to_bv 64 lbf); QbVh.C4 (Z_to_bv 64 0);
QbVh.CB 80 tail].
Lemma file_cells_D : forall flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
map QmAH.cellD (file_cellsO flags wend wpos wbase writefn buf bufsize fd mode lbf tail) = Qu3b.Mq0.file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail.
Proof. reflexivity. Qed.

Definition Z80 : list byte := repeat (Z_to_bv 8 0) 80.
Definition Z1024 : list byte := repeat (Z_to_bv 8 0) 1024.

Lemma stdout_file_init : forall m, QdM4.Mq0.STDOUT0_A m -> Qu3b.Mq0.stdout_file m QdZp.stdout_init.
Proof.
intros m [P1 P2]. unfold QdM4.Mq0.STDOUT0_A, Q2y2.F_STDOUT in *.
exists (Z_to_bv 64 5), (Z_to_bv 64 0), Z80, Z1024. cbn [QdZp.stdout_init QdZp.so_active QdZp.so_buf QdZp.so_lbf_nl QdZp.so_first].
split.
{ rewrite <- file_cells_D. apply (proj1 (QmAH.rw_cells_D Q7UD.asegs m 0xea750 _)).
refine (QdM4.Mq1.rw_cells_pristine_recast m 0xea750 (QbVh.cells_bytes (file_cellsO (Z_to_bv 64 5) 0 0 0 0xd36bc 0x6435e8 1024 1 (Z_to_bv 64 0) 10 Z80)) _ _ _ _ _ _ _ _);
[ exact P1 | vm_compute; reflexivity | lia | cbn; lia | cbn; tauto | reflexivity | reflexivity ]. }
split; [reflexivity|].
split.
{ change [QMow.CB 1024 Z1024] with (map QmAH.cellD [QbVh.CB 1024 Z1024]). apply (proj1 (QmAH.rw_cells_D Q7UD.asegs m 0x6435e8 _)).
refine (QdM4.Mq1.rw_cells_pristine_recast m 0x6435e8 Z1024 _ _ _ _ _ _ _ _);
[ apply (QdM4.Mq1.pristine_sub m 0x6435e0 0x6439f0); [exact P2 | lia | cbn; lia] | vm_compute; reflexivity | lia | unfold Z1024; rewrite repeat_length; lia | cbn [QbVh.cells_wf QbVh.cell_wf]; unfold Z1024; rewrite repeat_length; tauto | cbn [QbVh.cells_bytes QbVh.cbytes]; apply app_nil_r | cbn [QbVh.cells_size QbVh.csize]; unfold Z1024; rewrite repeat_length; reflexivity ]. }
split; [reflexivity|]. split; [apply Z.leb_le; reflexivity|]. intros _. reflexivity.
Qed.

Lemma stderr_wfile0_init : forall m, QdM4.Mq0.STDERR0_A m -> QpzM.Mqc.stderr_wfile0 m.
Proof.
intros m P. unfold QdM4.Mq0.STDERR0_A, Q2y2.F_STDERR in *.
exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, Z80.
split.
{ rewrite <- file_cells_D. apply (proj1 (QmAH.rw_cells_D Q7UD.asegs m 0xea660 _)).
refine (QdM4.Mq1.rw_cells_pristine_recast m 0xea660 (QbVh.cells_bytes (file_cellsO (Z_to_bv 64 5) 0 0 0 0xd29d0 0x6435e0 0 2 (Z_to_bv 64 0) 0xffffffff Z80)) _ _ _ _ _ _ _ _);
[ exact P | vm_compute; reflexivity | lia | cbn; lia | cbn; tauto | reflexivity | reflexivity ]. }
split; [reflexivity|]. split; [left; reflexivity| lia].
Qed.

Lemma file_cells_clean : forall m f flags wend e w buf bsz fd mode lbf tail,
QmAH.DT.rw_cells Q7UD.asegs m f (Qu3b.Mq0.file_cells flags wend e e w buf bsz fd mode lbf tail) ->
QS67.file_clean m f (Z_to_bv 64 e) (Z_to_bv 64 0).
Proof.
intros m f flags wend e w buf bsz fd mode lbf tail [[WF BA] _].
assert (LT : length tail = 80%nat) by (unfold Qu3b.Mq0.file_cells in WF; cbn [QMow.cells_wf QMow.cell_wf] in WF; tauto).
change (QZDE.bytes_at Q7UD.asegs m f (QMow.cells_bytes (Qu3b.Mq0.file_cells flags wend e e w buf bsz fd mode lbf tail))) in BA.
assert (LEN : length (QMow.cells_bytes (Qu3b.Mq0.file_cells flags wend e e w buf bsz fd mode lbf tail)) = 232%nat).
{ unfold Qu3b.Mq0.file_cells. cbn [QMow.cells_bytes QMow.cbytes]. rewrite !length_app. cbn [length]. rewrite LT. reflexivity. }
assert (RD : forall k n, (k + n <= 232)%nat -> QsjA.rdn Q7UD.asegs m (Z_to_bv 64 (f + Z.of_nat k)) n
= Some (firstn n (skipn k (QMow.cells_bytes (Qu3b.Mq0.file_cells flags wend e e w buf bsz fd mode lbf tail))))).
{ intros k n Hk. apply (QZDE.bytes_at_rdn Q7UD.asegs m f _ k n BA). rewrite LEN. exact Hk. }
unfold QS67.file_clean.
split; [exact (RD 140%nat 4%nat ltac:(lia))|]. split; [exact (RD 40%nat 8%nat ltac:(lia))|]. split; [exact (RD 56%nat 8%nat ltac:(lia))|].
split; [exact (RD 8%nat 8%nat ltac:(lia))| exact (RD 16%nat 8%nat ltac:(lia))].
Qed.

Section Inst.
Context {RC__ : Q6q3.RunConsts}.
Context {BAND : Band}.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap Q7UD.asegs.
Hypothesis Hsegs : segs_in_base LV Q7UD.asegs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.
Local Notation J := (QRGF.aj_base_vj Q7UD.asegs LV Hwx Hsegs).

Lemma ssp_of_ISH : forall m, Q9Ho.Mq0.ISH m -> QnRU.Mq4.ssp_cells m band_guard.
Proof.
intros m (_ & RC & _). split.
- pose proof (Q9Ho.Mq0.rt_1589b8_guard m RC) as G.
change (QmAH.DT.ro_cells Q7UD.asegs m 0xe6b80 (map QmAH.cellD [QbVh.C8 (Z_to_bv 64 0x642ea0)])) in G.
apply QmAH.ro_cells_D in G. apply QdM4.Mq1.rw_of_ro_img in G; [| vm_compute; reflexivity]. apply QmAH.rw_cells_D in G. exact G.
- pose proof (Q9Ho.Mq0.rt_683ae0 m RC) as G.
change (QmAH.DT.ro_cells Q7UD.asegs m 0x642ea0 (map QmAH.cellD [QbVh.C8 band_guard])) in G.
apply QmAH.ro_cells_D in G. apply QdM4.Mq1.rw_of_ro_img in G; [| vm_compute; reflexivity]. apply QmAH.rw_cells_D in G. exact G.
Qed.

Lemma cnext_of_drift : forall cf c1, QZsi.CK J cf -> drift LV (cfg_model cf) (cfg_model c1) -> cinvA LV (cfg_ms c1) (cfg_model c1) ->
QZsi.CNEXT J cf c1 /\ Q0TL.same_io cf c1.
Proof.
intros cf c1 [HC HH] D C1. pose proof D as (P & _ & _ & E).
split; [split; [split; [exact C1| rewrite E; exact HH]| exact (QRGF.vmrel_drift LV _ _ D)]| split; rewrite E; reflexivity].
Qed.

Theorem pf1_inst : QdM4.Mq0.emitpf1_stmt J (@Q9Ho.Mq0.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq0.emitpf1_stmt.
intros sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo
HCK FD1 OUT0 IMG RT STK CE BLO LOS A16 SP47 MI FRM KN HK.
pose proof (@QQ8H.Mq1.emit_printf_proof BAND QdZp.stdout_st (fun so => so) (fun so _ => so)
(Z_to_bv 64 0x919a4) sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m QdZp.stdout_init lo band_guard 0
(fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (@QSLK.fwritex_stdout_proof BAND)
(stdout_file_init m OUT0) RT ltac:(lia) eq_refl STK ltac:(unfold QQNJ.Mq1.EMIT_DEPTH, QdM4.Mq0.PF_STACK_A in *; lia) BLO SP47
(ssp_of_ISH m RT) MI FRM) as IMPL.
pose proof (QgTJ.Mq3.sdet_stdout_vprintf (fun so : QdZp.stdout_st => so) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
(QdZp.pieces_emit_d 0) QdZp.stdout_init QdZp.stdout_init eq_refl ltac:(apply Z.leb_le; reflexivity)
ltac:(rewrite QgTJ.Mq3.pieces_emit_d_0; repeat constructor)) as SDET.
rewrite QgTJ.Mq3.so_vprintf_emit0_first in SDET. cbn [fst snd] in SDET.
refine (QgTJ.Mq3.implM_vj_sdet Q7UD.asegs LV Hwx Hsegs Hsh Hbx Hbc (fun so : QdZp.stdout_st => so) (fun so _ => so) _ QdZp.stdout_init _ _ tt _ K cf _
IMPL (proj1 HCK) (QgTJ.Mq3.mio_stdout_vprintf _ _ _) SDET KN _).
intros st' c1 msv1 -> EV D C1 _.
apply (QNqr.vj_evt Q7UD.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes Q7UD.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SOF & SSP).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
replace (QUcd.ret_pc (Z_to_bv 64 596388)) with (Z_to_bv 64 596388 : word)
by (symmetry; apply QEpW.ret_pc_even; [lia| reflexivity]).
refine (HK (Z_to_bv 64 596388) q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' SOF _ (fun _ => FRM') CN SIO).
intros k Hk. apply FREG. unfold QCcH.FSAVED in Hk. cbn [In] in Hk.
repeat (destruct Hk as [<-|Hk]; [vm_compute; discriminate|]). destruct Hk.
Qed.

Lemma zl_snoc : forall k, QdM4.Mq0.zl k ++ [48; 10] = QdM4.Mq0.zl (S k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [QdM4.Mq0.zl app]. rewrite IH. reflexivity. Qed.
Lemma zl_len : forall k, QCiC.Mq1.zlength (QdM4.Mq0.zl k) = 2 * Z.of_nat k.
Proof. induction k as [|k IH]; [reflexivity|]. unfold QCiC.Mq1.zlength in *. cbn [QdM4.Mq0.zl length]. lia. Qed.

Lemma t_emit_nil : forall K : QRjH.TSet, K [] ->
QRjH.t_eq (QRjH.t_emit [] K) K.
Proof.
intros K KN tr. unfold QRjH.t_emit. split.
- intros [HP|(tr' & -> & HT)]; [destruct tr; [exact KN| cbn in HP; contradiction]| exact HT].
- intros HT. right. exists tr. split; [reflexivity| exact HT].
Qed.

Theorem pfk_inst : QdM4.Mq0.emitpfk_stmt J (@Q9Ho.Mq0.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq0.emitpfk_stmt.
intros k sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo
HCK Hk OUTW IMG RT STK CE BLO LOS A16 SP47 MI FRM KN HK.
unfold QdM4.Mq0.STDOUTW_A in OUTW.
pose proof (zl_len (Nat.pred k)) as ZL.
pose proof (@QQ8H.Mq1.emit_printf_proof BAND QdZp.stdout_st (fun so => so) (fun so _ => so)
(Z_to_bv 64 0x919a4) sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m (QdM4.Mq0.so_w k) lo band_guard 0
(fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (@QSLK.fwritex_stdout_proof BAND)
OUTW RT ltac:(lia) eq_refl STK ltac:(unfold QQNJ.Mq1.EMIT_DEPTH, QdM4.Mq0.PF_STACK_A in *; lia) BLO SP47
(ssp_of_ISH m RT) MI FRM) as IMPL.
pose proof (QgTJ.Mq3.sdet_stdout_vprintf (fun so : QdZp.stdout_st => so) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
(QdZp.pieces_emit_d 0) (QdM4.Mq0.so_w k) (QdM4.Mq0.so_w k) eq_refl ltac:(unfold QdM4.Mq0.so_w, QdZp.STDOUT_BUFSIZ; cbn [QdZp.so_buf]; lia)
ltac:(rewrite QgTJ.Mq3.pieces_emit_d_0; repeat constructor)) as SDET.
unfold QdM4.Mq0.so_w in SDET. rewrite QgTJ.Mq3.so_vprintf_emit0_next in SDET by (unfold QdZp.STDOUT_BUFSIZ; lia). cbn [fst snd] in SDET.
rewrite zl_snoc in SDET.
apply (QRGF.AJv_conseq Q7UD.asegs LV (QRjH.t_emit [] K) K); [| exact (t_emit_nil K KN)].
refine (QgTJ.Mq3.implM_vj_sdet Q7UD.asegs LV Hwx Hsegs Hsh Hbx Hbc (fun so : QdZp.stdout_st => so) (fun so _ => so) _ (QdM4.Mq0.so_w k) _ _ tt _ K cf _
IMPL (proj1 HCK) (QgTJ.Mq3.mio_stdout_vprintf _ _ _) SDET KN _).
intros st' c1 msv1 -> EV D C1 _.
apply (QNqr.vj_evt Q7UD.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes Q7UD.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SOF & SSP).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
replace (QUcd.ret_pc (Z_to_bv 64 596388)) with (Z_to_bv 64 596388 : word)
by (symmetry; apply QEpW.ret_pc_even; [lia| reflexivity]).
refine (HK (Z_to_bv 64 596388) q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' _ _ (fun _ => FRM') CN SIO).
- unfold QdM4.Mq0.STDOUTW_A, QdM4.Mq0.so_w. replace (Nat.pred (S k)) with (S (Nat.pred k)) by lia. exact SOF.
- intros j Hj. apply FREG. unfold QCcH.FSAVED in Hj. cbn [In] in Hj.
repeat (destruct Hj as [<-|Hj]; [vm_compute; discriminate|]). destruct Hj.
Qed.

Definition msgZ (msg : Z) : list Z := map bv_unsigned (QdM4.Mq0.fwrite_msg msg).
Lemma zb_msgZ : forall msg, QteI.Mq1.zb (msgZ msg) = QdM4.Mq0.fwrite_msg msg.
Proof.
intros msg. unfold msgZ, QteI.Mq1.zb. rewrite map_map.
rewrite (map_ext _ (fun b => b)); [apply map_id| intros b; apply Z_to_bv_bv_unsigned].
Qed.

Theorem fwrite_inst : QdM4.Mq0.fwrite_stmt J (@Q9Ho.Mq0.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq0.fwrite_stmt.
intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo msg
HCK FD2 HMSG -> -> -> -> ERR0 IMG RT SHZ STK CE BLO LOS A16 SP47 MI RA2 KN HK.
pose proof (@Q6q3.alloc_ceiling_range RC__) as ACR.
assert (MSGF : 0x10000 <= msg /\ msg + Z.of_nat (length (QdM4.Mq0.fwrite_msg msg)) <= 0x23080 /\ 0 < Z.of_nat (length (QdM4.Mq0.fwrite_msg msg)) <= 31
/\ QZDE.bytes_at Q7UD.asegs m msg (QdM4.Mq0.fwrite_msg msg)).
{ destruct HMSG as [-> | [-> | ->]]; (split; [unfold QdM4.Mq0.MSG_SHORT, QdM4.Mq0.MSG_OVERRUN, QdM4.Mq0.MSG_OOM; lia|]); (split; [vm_compute; discriminate|]); (split; [vm_compute; split; [reflexivity| discriminate]|]);
(apply (QZDE.ro_bytes_at Q7UD.asegs m _ _ MI); [vm_compute; discriminate | vm_compute; discriminate |]);
vm_compute; repeat split. }
destruct MSGF as (MS1 & MS2 & MS3 & MSB).
assert (LZ : QCiC.Mq1.zlength (msgZ msg) = Z.of_nat (length (QdM4.Mq0.fwrite_msg msg))) by (unfold QCiC.Mq1.zlength, msgZ; rewrite length_map; reflexivity).
assert (UM : bv_unsigned (Z_to_bv 64 msg) = msg) by (apply QZDE.wa_unsigned; lia).
pose proof (@Q8zl.Mq1.fwrite_icpt_proof BAND unit (@Qa5v.fwrite_diag_proof BAND unit)
ra sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 msg) (Z_to_bv 64 (Z.of_nat (length (QdM4.Mq0.fwrite_msg msg)))) (Z_to_bv 64 1) (Z_to_bv 64 Q2y2.F_STDERR)
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tt lo band_guard (msgZ msg)
QnaW.Mq0.towrite_proof (stderr_wfile0_init m ERR0)) as IMPL.
rewrite UM, zb_msgZ, LZ in IMPL.
specialize (IMPL MSB).
assert (FA : Forall (fun c : Z => 0 <= c < 256) (msgZ msg)).
{ unfold msgZ. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. }
specialize (IMPL FA ltac:(unfold QQNJ.Mq1.OUT_MAX; lia) eq_refl eq_refl eq_refl STK
ltac:(unfold Q8zl.Mq1.FWRITE_ICPT_DEPTH, QpzM.Mqc.FWRITE_DEPTH, QdM4.Mq0.PF_STACK_A in *; lia) BLO ltac:(left; lia) ltac:(left; lia)
(ssp_of_ISH m RT) MI RT ltac:(left; lia) ltac:(lia)).
pose proof (QgTJ.Mq3.mdet_stderr_fwrite (msgZ msg) tt ltac:(rewrite LZ; lia)) as MD.
assert (EO : QCrt.Mq3.wev 2 (msgZ msg) = QBxa.Mq5.W 2 (QdM4.Mq0.fwrite_msg msg)).
{ unfold QCrt.Mq3.wev, QBxa.Mq5.W, QdZp.to_bytes. rewrite <- (zb_msgZ msg). reflexivity. }
rewrite <- EO.
refine (QCrt.Mq3.implM_vj_det Q7UD.asegs LV Hwx Hsegs Hsh Hbx Hbc _ tt _ _ tt tt K cf _ IMPL (proj1 HCK) (QgTJ.Mq3.mio_stderr_fwrite _ tt) MD KN _).
intros c1 msv1 EV D C1 _.
apply (QNqr.vj_evt Q7UD.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes Q7UD.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & m' & -> & MU & WM & MI' & STK' & SWF & SSP & _).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
refine (HK q0 q1 q2 (Z_to_bv 64 1) r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F fc m' c1 MU WM MI' STK' _ (fun _ _ => eq_refl) (fun H => H) CN SIO).
destruct SWF as (flags & mode & e & wend & tail & FC & _). exists (Z_to_bv 64 e), (Z_to_bv 64 0).
exact (file_cells_clean m' Q2y2.F_STDERR _ _ _ _ _ _ _ _ _ _ FC).
Qed.

Lemma stderr_wfile_init : forall m, QdM4.Mq0.STDERR0_A m -> QQNJ.Mq1.stderr_wfile m.
Proof. intros m P. exact (QpzM.Mqc.stderr_wfile0_wfile m (stderr_wfile0_init m P)). Qed.

Lemma fsaved_of : forall (F Ft : bvmap 5 word), (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get Ft k = Sem.reg_get F k) -> QCcH.fsaved F Ft.
Proof.
intros F Ft FREG j Hj. apply FREG. unfold QCcH.FSAVED in Hj. cbn [In] in Hj.
repeat (destruct Hj as [<-|Hj]; [vm_compute; discriminate|]). destruct Hj.
Qed.

Lemma stderrc_of_wfile : forall m, QQNJ.Mq1.stderr_wfile m -> QdM4.Mq0.STDERRC_A m.
Proof.
intros m (flags & mode & e & wend & tail & FC & _). exists (Z_to_bv 64 e), (Z_to_bv 64 0).
exact (file_cells_clean m Q2y2.F_STDERR _ _ _ _ _ _ _ _ _ _ FC).
Qed.

Theorem fprintf_u_inst : QdM4.Mq0.fprintf_u_stmt J (@Q9Ho.Mq0.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq0.fprintf_u_stmt.
intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo
HCK FD2 -> -> -> ERR0 IMG RT STK CE BLO LOS A16 SP47 MI FRM RA2 KN HK.
pose proof (@Qx6U.Mq0.fprintf_diag_proof BAND unit Qk8e.Mq0.DTooBig
ra sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 Q2y2.F_STDERR) (Z_to_bv 64 QdM4.Mq0.FMT_REFUSED) (Z_to_bv 64 67108864)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tt lo band_guard
(@QpzM.Mq0.fwritex_stderr_proof BAND) (@QpzM.Mq2.stdio_write_flush_proof BAND) (stderr_wfile_init m ERR0) RT eq_refl
(conj eq_refl eq_refl) STK ltac:(unfold QQNJ.Mq1.FPRINTF_DEPTH, QdM4.Mq0.PF_STACK_A in *; lia) BLO SP47 (ssp_of_ISH m RT) MI FRM) as IMPL.
pose proof (QgTJ.Mq3.mdet_stderr_fprintf QdZp.pieces_too_big tt ltac:(vm_compute; reflexivity)) as MD.
assert (EO : QCrt.Mq3.wev 2 (concat QdZp.pieces_too_big) = QBxa.Mq5.W 2 QBxa.Mq5.msg_refused) by (vm_compute; reflexivity).
rewrite <- EO.
refine (QCrt.Mq3.implM_vj_det Q7UD.asegs LV Hwx Hsegs Hsh Hbx Hbc _ tt _ _ tt tt K cf _ IMPL (proj1 HCK) (QgTJ.Mq3.mio_stderr_fprintf _ tt) MD KN _).
intros c1 msv1 EV D C1 _.
apply (QNqr.vj_evt Q7UD.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes Q7UD.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SWF & SSP & _).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
exact (HK q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' (stderrc_of_wfile m' SWF) (fsaved_of F Ft FREG) (fun _ => FRM') CN SIO).
Qed.

Definition strZ (str : list byte) : list Z := map bv_unsigned str.
Lemma zb_strZ : forall str, QteI.Mq1.zb (strZ str) = str.
Proof.
intros str. unfold strZ, QteI.Mq1.zb. rewrite map_map.
rewrite (map_ext _ (fun b => b)); [apply map_id| intros b; apply Z_to_bv_bv_unsigned].
Qed.
Lemma to_bytes_strZ : forall str, QdZp.to_bytes (strZ str) = str.
Proof. exact zb_strZ. Qed.

Definition diag_of (fmt : Z) (str : list byte) : Qk8e.Mq0.diag_msg :=
if Z.eqb fmt QdM4.Mq0.FMT_USAGE then Qk8e.Mq0.DUsage (strZ str) else if Z.eqb fmt QdM4.Mq0.FMT_CANNOT then Qk8e.Mq0.DCannotOpen (strZ str) else Qk8e.Mq0.DReadError (strZ str).

Lemma out_usage : forall str, QdZp.to_bytes (concat (QdZp.pieces_usage (strZ str))) = QBxa.Mq5.msg_usage str.
Proof. intros. unfold QdZp.pieces_usage, QBxa.Mq5.msg_usage. cbn [concat]. unfold QdZp.to_bytes. rewrite !map_app. fold (QdZp.to_bytes (strZ str)). rewrite to_bytes_strZ. reflexivity. Qed.
Lemma out_cannot : forall str, QdZp.to_bytes (concat (QdZp.pieces_cannot_open (strZ str))) = QBxa.Mq5.msg_cannot_open str.
Proof. intros. unfold QdZp.pieces_cannot_open, QBxa.Mq5.msg_cannot_open. cbn [concat]. unfold QdZp.to_bytes. rewrite !map_app. fold (QdZp.to_bytes (strZ str)). rewrite to_bytes_strZ. reflexivity. Qed.
Lemma out_readerr : forall str, QdZp.to_bytes (concat (QdZp.pieces_read_error (strZ str))) = QBxa.Mq5.msg_read_error str.
Proof. intros. unfold QdZp.pieces_read_error, QBxa.Mq5.msg_read_error. cbn [concat]. unfold QdZp.to_bytes. rewrite !map_app. fold (QdZp.to_bytes (strZ str)). rewrite to_bytes_strZ. reflexivity. Qed.
Lemma zlen_app : forall (a b : list Z), QCiC.Mq1.zlength (a ++ b) = QCiC.Mq1.zlength a + QCiC.Mq1.zlength b.
Proof. intros; unfold QCiC.Mq1.zlength; rewrite length_app; lia. Qed.
Lemma zlen_strZ : forall str, QCiC.Mq1.zlength (strZ str) = Z.of_nat (length str).
Proof. intros. unfold QCiC.Mq1.zlength, strZ. rewrite length_map. reflexivity. Qed.
Lemma len_usage : forall str, QCiC.Mq1.zlength (concat (QdZp.pieces_usage (strZ str))) = Z.of_nat (length str) + 14.
Proof. intros. unfold QdZp.pieces_usage. cbn [concat]. rewrite !zlen_app, zlen_strZ. change (QCiC.Mq1.zlength (QdZp.str "usage: ")) with 7. change (QCiC.Mq1.zlength (QdZp.str " INPUT")) with 6. change (QCiC.Mq1.zlength [10]) with 1. change (QCiC.Mq1.zlength (@nil Z)) with 0. lia. Qed.
Lemma len_cannot : forall str, QCiC.Mq1.zlength (concat (QdZp.pieces_cannot_open (strZ str))) = Z.of_nat (length str) + 18.
Proof. intros. unfold QdZp.pieces_cannot_open. cbn [concat]. rewrite !zlen_app, zlen_strZ. change (QCiC.Mq1.zlength (QdZp.str "cli: cannot open ")) with 17. change (QCiC.Mq1.zlength [10]) with 1. change (QCiC.Mq1.zlength (@nil Z)) with 0. lia. Qed.
Lemma len_readerr : forall str, QCiC.Mq1.zlength (concat (QdZp.pieces_read_error (strZ str))) = Z.of_nat (length str) + 20.
Proof. intros. unfold QdZp.pieces_read_error. cbn [concat]. rewrite !zlen_app, zlen_strZ. change (QCiC.Mq1.zlength (QdZp.str "cli: read error on ")) with 19. change (QCiC.Mq1.zlength [10]) with 1. change (QCiC.Mq1.zlength (@nil Z)) with 0. lia. Qed.

Lemma fprintf_s_core : forall (d : Qk8e.Mq0.diag_msg) (ps : list (list Z)) (msg : list byte)
(ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : QRjH.TSet) (lo fmt p : Z),
Qk8e.Mq0.s_diag (St:=unit) d = QdZp.stderr_fprintf ps -> QdZp.to_bytes (concat ps) = msg -> QCiC.Mq1.zlength (concat ps) < 2^64 ->
QQNJ.Mq1.diag_args d m (Z_to_bv 64 fmt) (Z_to_bv 64 p) lo (bv_unsigned sp) ->
QZsi.CK J cf -> QdM4.Mq0.STDERR0_A m -> Q9Ho.Mq0.ISH m ->
QWxq_c1.stk Q7UD.asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo + QdM4.Mq0.PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp + 16 <= 2^47 -> QZDE.mem_inv Q7UD.asegs m -> QCcH.frm0 fc -> K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
QWxq_c1.munch (QdM4.Mq0.PFW_ERR lo (bv_unsigned sp)) m m' -> QWxq_c1.wmono Q7UD.asegs m m' ->
QZDE.mem_inv Q7UD.asegs m' ->
QWxq_c1.stk Q7UD.asegs m' lo (bv_unsigned sp) -> QdM4.Mq0.STDERRC_A m' -> QCcH.fsaved F F' -> (QCcH.frm0 fc -> QCcH.frm0 fc') ->
QZsi.CNEXT J cf cf' -> Q0TL.same_io cf cf' ->
QZsi.AJ J K cf' (QEpW.MS
(QWxq_c1.mkR ra sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (QEpW.ret_pc ra) fc' None m' (QsjA.seg_rom Q7UD.asegs))) ->
QZsi.AJ J (QRjH.t_emit (QBxa.Mq5.W 2 msg) K) cf
(QEpW.MS
(QWxq_c1.mkR ra sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 Q2y2.F_STDERR) (Z_to_bv 64 fmt) (Z_to_bv 64 p)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 QdM4.Mq0.FPRINTF_V) fc None m (QsjA.seg_rom Q7UD.asegs)).
Proof.
intros d ps msg ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo fmt p
ESD EOUT ELEN DA HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK.
pose proof (@Qx6U.Mq0.fprintf_diag_proof BAND unit d
ra sp gp (Z_to_bv 64 Qwm6.Mq0.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 Q2y2.F_STDERR) (Z_to_bv 64 fmt) (Z_to_bv 64 p)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tt lo band_guard
(@QpzM.Mq0.fwritex_stderr_proof BAND) (@QpzM.Mq2.stdio_write_flush_proof BAND) (stderr_wfile_init m ERR0) RT eq_refl
DA STK ltac:(unfold QQNJ.Mq1.FPRINTF_DEPTH, QdM4.Mq0.PF_STACK_A in *; lia) BLO SP47 (ssp_of_ISH m RT) MI FRM) as IMPL.
rewrite ESD in IMPL.
pose proof (QgTJ.Mq3.mdet_stderr_fprintf ps tt ELEN) as MD.
assert (EO : QCrt.Mq3.wev 2 (concat ps) = QBxa.Mq5.W 2 msg) by (unfold QCrt.Mq3.wev, QBxa.Mq5.W; rewrite EOUT; reflexivity).
rewrite <- EO.
refine (QCrt.Mq3.implM_vj_det Q7UD.asegs LV Hwx Hsegs Hsh Hbx Hbc _ tt _ _ tt tt K cf _ IMPL (proj1 HCK) (QgTJ.Mq3.mio_stderr_fprintf _ tt) MD KN _).
intros c1 msv1 EV D C1 _.
apply (QNqr.vj_evt Q7UD.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes Q7UD.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SWF & SSP & _).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
exact (HK q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' (stderrc_of_wfile m' SWF) (fsaved_of F Ft FREG) (fun _ => FRM') CN SIO).
Time Qed.

Lemma diag_args_s : forall (m : word -> option byte) (p lo usp : Z) (str slack : list byte),
QZDE.bytes_at Q7UD.asegs m p (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
(- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length str) < 2^17 ->
0 <= p -> usp <= p -> p + Z.of_nat (length str) + 9 <= 2^47 -> band_lo <= lo -> lo + QdM4.Mq0.PF_STACK_A <= usp ->
exists slack' : list byte,
QZDE.bytes_at Q7UD.asegs m (bv_unsigned (Z_to_bv 64 p)) (QteI.Mq1.zb (strZ str) ++ Z_to_bv 8 0 :: slack')
/\ Forall (fun c => 0 < c < 256) (strZ str)
/\ ((- (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 1)) mod 8 <= QCiC.Mq1.zlength slack')
/\ (QCiC.Mq1.zlength (strZ str) <= QQNJ.Mq1.OUT_MAX)
/\ (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 1 + QCiC.Mq1.zlength slack' <= lo \/ usp <= bv_unsigned (Z_to_bv 64 p))
/\ (QQNJ.Mq1.GLOBALS_TOP + 64 <= bv_unsigned (Z_to_bv 64 p)) /\ (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 9 <= 2^47)
/\ (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 1 + QCiC.Mq1.zlength slack' <= 2^47).
Proof.
intros m p lo usp str slack BYT NZ SLK LEN P0 PSP P47 BLO LOS.
assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply QZDE.wa_unsigned; lia).
set (ns := Z.to_nat ((- (p + Z.of_nat (length str) + 1)) mod 8)).
assert (NS : Z.of_nat ns = (- (p + Z.of_nat (length str) + 1)) mod 8 /\ (ns <= 7)%nat /\ (ns <= length slack)%nat).
{ pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length str) + 1)) 8 ltac:(lia)) as B. unfold ns. split; [lia| split; lia]. }
destruct NS as (NS1 & NS2 & NS3).
exists (firstn ns slack). rewrite UP, zb_strZ, zlen_strZ. unfold QCiC.Mq1.zlength. rewrite firstn_length_le by exact NS3.
split.
{ rewrite <- (firstn_skipn ns slack) in BYT.
replace (str ++ Z_to_bv 8 0 :: firstn ns slack ++ skipn ns slack) with ((str ++ Z_to_bv 8 0 :: firstn ns slack) ++ skipn ns slack) in BYT
by (rewrite <- app_assoc; reflexivity).
exact (proj1 (proj1 (QZDE.bytes_at_app Q7UD.asegs m p _ _) BYT)). }
split.
{ unfold strZ. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
assert (bv_unsigned b <> 0). { intros E0. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
lia. }
unfold QQNJ.Mq1.OUT_MAX, QQNJ.Mq1.GLOBALS_TOP, QdM4.Mq0.PF_STACK_A in *. repeat split; lia.
Time Qed.

Theorem fprintf_s_inst : QdM4.Mq0.fprintf_s_stmt J (@Q9Ho.Mq0.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq0.fprintf_s_stmt.
intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo fmt p str slack
HCK FD2 HFMT -> -> -> BYT NZ SLK LEN UNP P0 PSP P47 ERR0 IMG RT STK CE BLO LOS A16 SP47 MI FRM RA2 KN HK.
pose proof (diag_args_s m p lo (bv_unsigned sp) str slack BYT NZ SLK LEN P0 PSP P47 BLO LOS) as DA.
destruct HFMT as [-> | [-> | ->]].
- refine (fprintf_s_core (Qk8e.Mq0.DUsage (strZ str)) (QdZp.pieces_usage (strZ str)) (QBxa.Mq5.msg_usage str) ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m cf K lo QdM4.Mq0.FMT_USAGE p eq_refl (out_usage str) _ (conj eq_refl DA) HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK).
rewrite len_usage. lia.
- refine (fprintf_s_core (Qk8e.Mq0.DCannotOpen (strZ str)) (QdZp.pieces_cannot_open (strZ str)) (QBxa.Mq5.msg_cannot_open str) ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m cf K lo QdM4.Mq0.FMT_CANNOT p eq_refl (out_cannot str) _ (conj eq_refl DA) HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK).
rewrite len_cannot. lia.
- refine (fprintf_s_core (Qk8e.Mq0.DReadError (strZ str)) (QdZp.pieces_read_error (strZ str)) (QBxa.Mq5.msg_read_error str) ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m cf K lo QdM4.Mq0.FMT_READERR p eq_refl (out_readerr str) _ (conj eq_refl DA) HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK).
rewrite len_readerr. lia.
Time Qed.
End Inst.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1jK.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qk8e.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLEB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjIq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnaW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8zl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition file_cellsO (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list QbVh.cell :=
[QbVh.C4 flags; QbVh.C4 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0xd4f48);
QbVh.C8 (Z_to_bv 64 wend); QbVh.C8 (Z_to_bv 64 wpos); QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 wbase); QbVh.C8 (Z_to_bv 64 0);
QbVh.C8 (Z_to_bv 64 writefn); QbVh.C8 (Z_to_bv 64 0xd508c); QbVh.C8 (Z_to_bv 64 buf); QbVh.C8 (Z_to_bv 64 bufsize);
QbVh.C8 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C4 (Z_to_bv 64 fd); QbVh.C4 (Z_to_bv 64 0); QbVh.C8 (Z_to_bv 64 0); QbVh.C4 mode; QbVh.C4 (Z_to_bv 64 0xffffffff); QbVh.C4 (Z_to_bv 64 lbf); QbVh.C4 (Z_to_bv 64 0);
QbVh.CB 80 tail].
Lemma file_cells_D : forall flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
map QmAH.cellD (file_cellsO flags wend wpos wbase writefn buf bufsize fd mode lbf tail) = Qu3b.Mq4.file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail.
Proof. reflexivity. Qed.

Definition Z80 : list byte := repeat (Z_to_bv 8 0) 80.
Definition Z1024 : list byte := repeat (Z_to_bv 8 0) 1024.

Lemma stdout_file_init : forall m, QdM4.Mq3.STDOUT0_A m -> Qu3b.Mq4.stdout_file m QdZp.stdout_init.
Proof.
intros m [P1 P2]. unfold QdM4.Mq3.STDOUT0_A, QupI.F_STDOUT in *.
exists (Z_to_bv 64 5), (Z_to_bv 64 0), Z80, Z1024. cbn [QdZp.stdout_init QdZp.so_active QdZp.so_buf QdZp.so_lbf_nl QdZp.so_first].
split.
{ rewrite <- file_cells_D. apply (proj1 (QmAH.rw_cells_D QbFI.asegs m 0xece30 _)).
refine (QdM4.Mq4.rw_cells_pristine_recast m 0xece30 (QbVh.cells_bytes (file_cellsO (Z_to_bv 64 5) 0 0 0 0xd5d80 0x645ca8 1024 1 (Z_to_bv 64 0) 10 Z80)) _ _ _ _ _ _ _ _);
[ exact P1 | vm_compute; reflexivity | lia | cbn; lia | cbn; tauto | reflexivity | reflexivity ]. }
split; [reflexivity|].
split.
{ change [QMow.CB 1024 Z1024] with (map QmAH.cellD [QbVh.CB 1024 Z1024]). apply (proj1 (QmAH.rw_cells_D QbFI.asegs m 0x645ca8 _)).
refine (QdM4.Mq4.rw_cells_pristine_recast m 0x645ca8 Z1024 _ _ _ _ _ _ _ _);
[ apply (QdM4.Mq4.pristine_sub m 0x645ca0 0x6460b0); [exact P2 | lia | cbn; lia] | vm_compute; reflexivity | lia | unfold Z1024; rewrite repeat_length; lia | cbn [QbVh.cells_wf QbVh.cell_wf]; unfold Z1024; rewrite repeat_length; tauto | cbn [QbVh.cells_bytes QbVh.cbytes]; apply app_nil_r | cbn [QbVh.cells_size QbVh.csize]; unfold Z1024; rewrite repeat_length; reflexivity ]. }
split; [reflexivity|]. split; [apply Z.leb_le; reflexivity|]. intros _. reflexivity.
Qed.

Lemma stderr_wfile0_init : forall m, QdM4.Mq3.STDERR0_A m -> QpzM.Mqo.stderr_wfile0 m.
Proof.
intros m P. unfold QdM4.Mq3.STDERR0_A, QupI.F_STDERR in *.
exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, Z80.
split.
{ rewrite <- file_cells_D. apply (proj1 (QmAH.rw_cells_D QbFI.asegs m 0xecd40 _)).
refine (QdM4.Mq4.rw_cells_pristine_recast m 0xecd40 (QbVh.cells_bytes (file_cellsO (Z_to_bv 64 5) 0 0 0 0xd5094 0x645ca0 0 2 (Z_to_bv 64 0) 0xffffffff Z80)) _ _ _ _ _ _ _ _);
[ exact P | vm_compute; reflexivity | lia | cbn; lia | cbn; tauto | reflexivity | reflexivity ]. }
split; [reflexivity|]. split; [left; reflexivity| lia].
Qed.

Lemma file_cells_clean : forall m f flags wend e w buf bsz fd mode lbf tail,
QmAH.DT.rw_cells QbFI.asegs m f (Qu3b.Mq4.file_cells flags wend e e w buf bsz fd mode lbf tail) ->
Q1jK.file_clean m f (Z_to_bv 64 e) (Z_to_bv 64 0).
Proof.
intros m f flags wend e w buf bsz fd mode lbf tail [[WF BA] _].
assert (LT : length tail = 80%nat) by (unfold Qu3b.Mq4.file_cells in WF; cbn [QMow.cells_wf QMow.cell_wf] in WF; tauto).
change (QZDE.bytes_at QbFI.asegs m f (QMow.cells_bytes (Qu3b.Mq4.file_cells flags wend e e w buf bsz fd mode lbf tail))) in BA.
assert (LEN : length (QMow.cells_bytes (Qu3b.Mq4.file_cells flags wend e e w buf bsz fd mode lbf tail)) = 232%nat).
{ unfold Qu3b.Mq4.file_cells. cbn [QMow.cells_bytes QMow.cbytes]. rewrite !length_app. cbn [length]. rewrite LT. reflexivity. }
assert (RD : forall k n, (k + n <= 232)%nat -> QsjA.rdn QbFI.asegs m (Z_to_bv 64 (f + Z.of_nat k)) n
= Some (firstn n (skipn k (QMow.cells_bytes (Qu3b.Mq4.file_cells flags wend e e w buf bsz fd mode lbf tail))))).
{ intros k n Hk. apply (QZDE.bytes_at_rdn QbFI.asegs m f _ k n BA). rewrite LEN. exact Hk. }
unfold Q1jK.file_clean.
split; [exact (RD 140%nat 4%nat ltac:(lia))|]. split; [exact (RD 40%nat 8%nat ltac:(lia))|]. split; [exact (RD 56%nat 8%nat ltac:(lia))|].
split; [exact (RD 8%nat 8%nat ltac:(lia))| exact (RD 16%nat 8%nat ltac:(lia))].
Qed.

Section Inst.
Context {RC__ : Q6q3.RunConsts}.
Context {BAND : Band}.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap QbFI.asegs.
Hypothesis Hsegs : segs_in_base LV QbFI.asegs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.
Local Notation J := (QRGF.aj_base_vj QbFI.asegs LV Hwx Hsegs).

Lemma ssp_of_ISH : forall m, Q9Ho.ISH m -> QnRU.ssp_cells m band_guard.
Proof.
intros m (_ & RC & _). split.
- pose proof (Q9Ho.rt_1589b8_guard m RC) as G.
change (QmAH.DT.ro_cells QbFI.asegs m 0xe8f90 (map QmAH.cellD [QbVh.C8 (Z_to_bv 64 0x645560)])) in G.
apply QmAH.ro_cells_D in G. apply QdM4.Mq4.rw_of_ro_img in G; [| vm_compute; reflexivity]. apply QmAH.rw_cells_D in G. exact G.
- pose proof (Q9Ho.rt_683ae0 m RC) as G.
change (QmAH.DT.ro_cells QbFI.asegs m 0x645560 (map QmAH.cellD [QbVh.C8 band_guard])) in G.
apply QmAH.ro_cells_D in G. apply QdM4.Mq4.rw_of_ro_img in G; [| vm_compute; reflexivity]. apply QmAH.rw_cells_D in G. exact G.
Qed.

Lemma cnext_of_drift : forall cf c1, QZsi.CK J cf -> drift LV (cfg_model cf) (cfg_model c1) -> cinvA LV (cfg_ms c1) (cfg_model c1) ->
QZsi.CNEXT J cf c1 /\ Qfub.same_io cf c1.
Proof.
intros cf c1 [HC HH] D C1. pose proof D as (P & _ & _ & E).
split; [split; [split; [exact C1| rewrite E; exact HH]| exact (QRGF.vmrel_drift LV _ _ D)]| split; rewrite E; reflexivity].
Qed.

Theorem pf1_inst : QdM4.Mq3.emitpf1_stmt J (@Q9Ho.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq3.emitpf1_stmt.
intros sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo
HCK FD1 OUT0 IMG RT STK CE BLO LOS A16 SP47 MI FRM KN HK.
pose proof (@QQ8H.Mq4.emit_printf_proof BAND QdZp.stdout_st (fun so => so) (fun so _ => so)
(Z_to_bv 64 0x91d7c) sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m QdZp.stdout_init lo band_guard 0
(fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (@QLEB.fwritex_stdout_proof BAND)
(stdout_file_init m OUT0) RT ltac:(lia) eq_refl STK ltac:(unfold QQNJ.Mq8.EMIT_DEPTH, QdM4.Mq3.PF_STACK_A in *; lia) BLO SP47
(ssp_of_ISH m RT) MI FRM) as IMPL.
pose proof (QgTJ.Mq3.sdet_stdout_vprintf (fun so : QdZp.stdout_st => so) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
(QdZp.pieces_emit_d 0) QdZp.stdout_init QdZp.stdout_init eq_refl ltac:(apply Z.leb_le; reflexivity)
ltac:(rewrite QgTJ.Mq3.pieces_emit_d_0; repeat constructor)) as SDET.
rewrite QgTJ.Mq3.so_vprintf_emit0_first in SDET. cbn [fst snd] in SDET.
refine (QgTJ.Mq3.implM_vj_sdet QbFI.asegs LV Hwx Hsegs Hsh Hbx Hbc (fun so : QdZp.stdout_st => so) (fun so _ => so) _ QdZp.stdout_init _ _ tt _ K cf _
IMPL (proj1 HCK) (QgTJ.Mq3.mio_stdout_vprintf _ _ _) SDET KN _).
intros st' c1 msv1 -> EV D C1 _.
apply (QNqr.vj_evt QbFI.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes QbFI.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SOF & SSP).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
replace (QUcd.ret_pc (Z_to_bv 64 597372)) with (Z_to_bv 64 597372 : word)
by (symmetry; apply QEpW.ret_pc_even; [lia| reflexivity]).
refine (HK (Z_to_bv 64 597372) q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' SOF _ (fun _ => FRM') CN SIO).
intros k Hk. apply FREG. unfold QCcH.FSAVED in Hk. cbn [In] in Hk.
repeat (destruct Hk as [<-|Hk]; [vm_compute; discriminate|]). destruct Hk.
Qed.

Lemma zl_snoc : forall k, QdM4.Mq3.zl k ++ [48; 10] = QdM4.Mq3.zl (S k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn [QdM4.Mq3.zl app]. rewrite IH. reflexivity. Qed.
Lemma zl_len : forall k, QCiC.Mq1.zlength (QdM4.Mq3.zl k) = 2 * Z.of_nat k.
Proof. induction k as [|k IH]; [reflexivity|]. unfold QCiC.Mq1.zlength in *. cbn [QdM4.Mq3.zl length]. lia. Qed.

Lemma t_emit_nil : forall K : QRjH.TSet, K [] ->
QRjH.t_eq (QRjH.t_emit [] K) K.
Proof.
intros K KN tr. unfold QRjH.t_emit. split.
- intros [HP|(tr' & -> & HT)]; [destruct tr; [exact KN| cbn in HP; contradiction]| exact HT].
- intros HT. right. exists tr. split; [reflexivity| exact HT].
Qed.

Theorem pfk_inst : QdM4.Mq3.emitpfk_stmt J (@Q9Ho.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq3.emitpfk_stmt.
intros k sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo
HCK Hk OUTW IMG RT STK CE BLO LOS A16 SP47 MI FRM KN HK.
unfold QdM4.Mq3.STDOUTW_A in OUTW.
pose proof (zl_len (Nat.pred k)) as ZL.
pose proof (@QQ8H.Mq4.emit_printf_proof BAND QdZp.stdout_st (fun so => so) (fun so _ => so)
(Z_to_bv 64 0x91d7c) sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m (QdM4.Mq3.so_w k) lo band_guard 0
(fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (@QLEB.fwritex_stdout_proof BAND)
OUTW RT ltac:(lia) eq_refl STK ltac:(unfold QQNJ.Mq8.EMIT_DEPTH, QdM4.Mq3.PF_STACK_A in *; lia) BLO SP47
(ssp_of_ISH m RT) MI FRM) as IMPL.
pose proof (QgTJ.Mq3.sdet_stdout_vprintf (fun so : QdZp.stdout_st => so) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
(QdZp.pieces_emit_d 0) (QdM4.Mq3.so_w k) (QdM4.Mq3.so_w k) eq_refl ltac:(unfold QdM4.Mq3.so_w, QdZp.STDOUT_BUFSIZ; cbn [QdZp.so_buf]; lia)
ltac:(rewrite QgTJ.Mq3.pieces_emit_d_0; repeat constructor)) as SDET.
unfold QdM4.Mq3.so_w in SDET. rewrite QgTJ.Mq3.so_vprintf_emit0_next in SDET by (unfold QdZp.STDOUT_BUFSIZ; lia). cbn [fst snd] in SDET.
rewrite zl_snoc in SDET.
apply (QRGF.AJv_conseq QbFI.asegs LV (QRjH.t_emit [] K) K); [| exact (t_emit_nil K KN)].
refine (QgTJ.Mq3.implM_vj_sdet QbFI.asegs LV Hwx Hsegs Hsh Hbx Hbc (fun so : QdZp.stdout_st => so) (fun so _ => so) _ (QdM4.Mq3.so_w k) _ _ tt _ K cf _
IMPL (proj1 HCK) (QgTJ.Mq3.mio_stdout_vprintf _ _ _) SDET KN _).
intros st' c1 msv1 -> EV D C1 _.
apply (QNqr.vj_evt QbFI.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes QbFI.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SOF & SSP).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
replace (QUcd.ret_pc (Z_to_bv 64 597372)) with (Z_to_bv 64 597372 : word)
by (symmetry; apply QEpW.ret_pc_even; [lia| reflexivity]).
refine (HK (Z_to_bv 64 597372) q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' _ _ (fun _ => FRM') CN SIO).
- unfold QdM4.Mq3.STDOUTW_A, QdM4.Mq3.so_w. replace (Nat.pred (S k)) with (S (Nat.pred k)) by lia. exact SOF.
- intros j Hj. apply FREG. unfold QCcH.FSAVED in Hj. cbn [In] in Hj.
repeat (destruct Hj as [<-|Hj]; [vm_compute; discriminate|]). destruct Hj.
Qed.

Definition msgZ (msg : Z) : list Z := map bv_unsigned (QdM4.Mq3.fwrite_msg msg).
Lemma zb_msgZ : forall msg, QteI.Mqb.zb (msgZ msg) = QdM4.Mq3.fwrite_msg msg.
Proof.
intros msg. unfold msgZ, QteI.Mqb.zb. rewrite map_map.
rewrite (map_ext _ (fun b => b)); [apply map_id| intros b; apply Z_to_bv_bv_unsigned].
Qed.

Theorem fwrite_inst : QdM4.Mq3.fwrite_stmt J (@Q9Ho.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq3.fwrite_stmt.
intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo msg
HCK FD2 HMSG -> -> -> -> ERR0 IMG RT SHZ STK CE BLO LOS A16 SP47 MI RA2 KN HK.
pose proof (@Q6q3.alloc_ceiling_range RC__) as ACR.
assert (MSGF : 0x10000 <= msg /\ msg + Z.of_nat (length (QdM4.Mq3.fwrite_msg msg)) <= 0x230c0 /\ 0 < Z.of_nat (length (QdM4.Mq3.fwrite_msg msg)) <= 31
/\ QZDE.bytes_at QbFI.asegs m msg (QdM4.Mq3.fwrite_msg msg)).
{ destruct HMSG as [-> | [-> | ->]]; (split; [unfold QdM4.Mq3.MSG_SHORT, QdM4.Mq3.MSG_OVERRUN, QdM4.Mq3.MSG_OOM; lia|]); (split; [vm_compute; discriminate|]); (split; [vm_compute; split; [reflexivity| discriminate]|]);
(apply (QZDE.ro_bytes_at QbFI.asegs m _ _ MI); [vm_compute; discriminate | vm_compute; discriminate |]);
vm_compute; repeat split. }
destruct MSGF as (MS1 & MS2 & MS3 & MSB).
assert (LZ : QCiC.Mq1.zlength (msgZ msg) = Z.of_nat (length (QdM4.Mq3.fwrite_msg msg))) by (unfold QCiC.Mq1.zlength, msgZ; rewrite length_map; reflexivity).
assert (UM : bv_unsigned (Z_to_bv 64 msg) = msg) by (apply QZDE.wa_unsigned; lia).
pose proof (@Q8zl.Mq3.fwrite_icpt_proof BAND unit (@QjIq.fwrite_diag_proof BAND unit)
ra sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 msg) (Z_to_bv 64 (Z.of_nat (length (QdM4.Mq3.fwrite_msg msg)))) (Z_to_bv 64 1) (Z_to_bv 64 QupI.F_STDERR)
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tt lo band_guard (msgZ msg)
QnaW.towrite_proof (stderr_wfile0_init m ERR0)) as IMPL.
rewrite UM, zb_msgZ, LZ in IMPL.
specialize (IMPL MSB).
assert (FA : Forall (fun c : Z => 0 <= c < 256) (msgZ msg)).
{ unfold msgZ. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. }
specialize (IMPL FA ltac:(unfold QQNJ.Mq8.OUT_MAX; lia) eq_refl eq_refl eq_refl STK
ltac:(unfold Q8zl.Mq3.FWRITE_ICPT_DEPTH, QpzM.Mqo.FWRITE_DEPTH, QdM4.Mq3.PF_STACK_A in *; lia) BLO ltac:(left; lia) ltac:(left; lia)
(ssp_of_ISH m RT) MI RT ltac:(left; lia) ltac:(lia)).
pose proof (QgTJ.Mq3.mdet_stderr_fwrite (msgZ msg) tt ltac:(rewrite LZ; lia)) as MD.
assert (EO : QCrt.Mq3.wev 2 (msgZ msg) = QBxa.Mq5.W 2 (QdM4.Mq3.fwrite_msg msg)).
{ unfold QCrt.Mq3.wev, QBxa.Mq5.W, QdZp.to_bytes. rewrite <- (zb_msgZ msg). reflexivity. }
rewrite <- EO.
refine (QCrt.Mq3.implM_vj_det QbFI.asegs LV Hwx Hsegs Hsh Hbx Hbc _ tt _ _ tt tt K cf _ IMPL (proj1 HCK) (QgTJ.Mq3.mio_stderr_fwrite _ tt) MD KN _).
intros c1 msv1 EV D C1 _.
apply (QNqr.vj_evt QbFI.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes QbFI.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & m' & -> & MU & WM & MI' & STK' & SWF & SSP & _).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
refine (HK q0 q1 q2 (Z_to_bv 64 1) r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F fc m' c1 MU WM MI' STK' _ (fun _ _ => eq_refl) (fun H => H) CN SIO).
destruct SWF as (flags & mode & e & wend & tail & FC & _). exists (Z_to_bv 64 e), (Z_to_bv 64 0).
exact (file_cells_clean m' QupI.F_STDERR _ _ _ _ _ _ _ _ _ _ FC).
Qed.

Lemma stderr_wfile_init : forall m, QdM4.Mq3.STDERR0_A m -> QQNJ.Mq8.stderr_wfile m.
Proof. intros m P. exact (QpzM.Mqo.stderr_wfile0_wfile m (stderr_wfile0_init m P)). Qed.

Lemma fsaved_of : forall (F Ft : bvmap 5 word), (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get Ft k = Sem.reg_get F k) -> QCcH.fsaved F Ft.
Proof.
intros F Ft FREG j Hj. apply FREG. unfold QCcH.FSAVED in Hj. cbn [In] in Hj.
repeat (destruct Hj as [<-|Hj]; [vm_compute; discriminate|]). destruct Hj.
Qed.

Lemma stderrc_of_wfile : forall m, QQNJ.Mq8.stderr_wfile m -> QdM4.Mq3.STDERRC_A m.
Proof.
intros m (flags & mode & e & wend & tail & FC & _). exists (Z_to_bv 64 e), (Z_to_bv 64 0).
exact (file_cells_clean m QupI.F_STDERR _ _ _ _ _ _ _ _ _ _ FC).
Qed.

Theorem fprintf_u_inst : QdM4.Mq3.fprintf_u_stmt J (@Q9Ho.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq3.fprintf_u_stmt.
intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo
HCK FD2 -> -> -> ERR0 IMG RT STK CE BLO LOS A16 SP47 MI FRM RA2 KN HK.
pose proof (@Qx6U.fprintf_diag_proof BAND unit Qk8e.Mq0.DTooBig
ra sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 QupI.F_STDERR) (Z_to_bv 64 QdM4.Mq3.FMT_REFUSED) (Z_to_bv 64 67108864)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tt lo band_guard
(@QpzM.Mqd.fwritex_stderr_proof BAND) (@QpzM.Mqf.stdio_write_flush_proof BAND) (stderr_wfile_init m ERR0) RT eq_refl
(conj eq_refl eq_refl) STK ltac:(unfold QQNJ.Mq8.FPRINTF_DEPTH, QdM4.Mq3.PF_STACK_A in *; lia) BLO SP47 (ssp_of_ISH m RT) MI FRM) as IMPL.
pose proof (QgTJ.Mq3.mdet_stderr_fprintf QdZp.pieces_too_big tt ltac:(vm_compute; reflexivity)) as MD.
assert (EO : QCrt.Mq3.wev 2 (concat QdZp.pieces_too_big) = QBxa.Mq5.W 2 QBxa.Mq5.msg_refused) by (vm_compute; reflexivity).
rewrite <- EO.
refine (QCrt.Mq3.implM_vj_det QbFI.asegs LV Hwx Hsegs Hsh Hbx Hbc _ tt _ _ tt tt K cf _ IMPL (proj1 HCK) (QgTJ.Mq3.mio_stderr_fprintf _ tt) MD KN _).
intros c1 msv1 EV D C1 _.
apply (QNqr.vj_evt QbFI.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes QbFI.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SWF & SSP & _).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
exact (HK q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' (stderrc_of_wfile m' SWF) (fsaved_of F Ft FREG) (fun _ => FRM') CN SIO).
Qed.

Definition strZ (str : list byte) : list Z := map bv_unsigned str.
Lemma zb_strZ : forall str, QteI.Mqb.zb (strZ str) = str.
Proof.
intros str. unfold strZ, QteI.Mqb.zb. rewrite map_map.
rewrite (map_ext _ (fun b => b)); [apply map_id| intros b; apply Z_to_bv_bv_unsigned].
Qed.
Lemma to_bytes_strZ : forall str, QdZp.to_bytes (strZ str) = str.
Proof. exact zb_strZ. Qed.

Definition diag_of (fmt : Z) (str : list byte) : Qk8e.Mq0.diag_msg :=
if Z.eqb fmt QdM4.Mq3.FMT_USAGE then Qk8e.Mq0.DUsage (strZ str) else if Z.eqb fmt QdM4.Mq3.FMT_CANNOT then Qk8e.Mq0.DCannotOpen (strZ str) else Qk8e.Mq0.DReadError (strZ str).

Lemma out_usage : forall str, QdZp.to_bytes (concat (QdZp.pieces_usage (strZ str))) = QBxa.Mq5.msg_usage str.
Proof. intros. unfold QdZp.pieces_usage, QBxa.Mq5.msg_usage. cbn [concat]. unfold QdZp.to_bytes. rewrite !map_app. fold (QdZp.to_bytes (strZ str)). rewrite to_bytes_strZ. reflexivity. Qed.
Lemma out_cannot : forall str, QdZp.to_bytes (concat (QdZp.pieces_cannot_open (strZ str))) = QBxa.Mq5.msg_cannot_open str.
Proof. intros. unfold QdZp.pieces_cannot_open, QBxa.Mq5.msg_cannot_open. cbn [concat]. unfold QdZp.to_bytes. rewrite !map_app. fold (QdZp.to_bytes (strZ str)). rewrite to_bytes_strZ. reflexivity. Qed.
Lemma out_readerr : forall str, QdZp.to_bytes (concat (QdZp.pieces_read_error (strZ str))) = QBxa.Mq5.msg_read_error str.
Proof. intros. unfold QdZp.pieces_read_error, QBxa.Mq5.msg_read_error. cbn [concat]. unfold QdZp.to_bytes. rewrite !map_app. fold (QdZp.to_bytes (strZ str)). rewrite to_bytes_strZ. reflexivity. Qed.
Lemma zlen_app : forall (a b : list Z), QCiC.Mq1.zlength (a ++ b) = QCiC.Mq1.zlength a + QCiC.Mq1.zlength b.
Proof. intros; unfold QCiC.Mq1.zlength; rewrite length_app; lia. Qed.
Lemma zlen_strZ : forall str, QCiC.Mq1.zlength (strZ str) = Z.of_nat (length str).
Proof. intros. unfold QCiC.Mq1.zlength, strZ. rewrite length_map. reflexivity. Qed.
Lemma len_usage : forall str, QCiC.Mq1.zlength (concat (QdZp.pieces_usage (strZ str))) = Z.of_nat (length str) + 14.
Proof. intros. unfold QdZp.pieces_usage. cbn [concat]. rewrite !zlen_app, zlen_strZ. change (QCiC.Mq1.zlength (QdZp.str "usage: ")) with 7. change (QCiC.Mq1.zlength (QdZp.str " INPUT")) with 6. change (QCiC.Mq1.zlength [10]) with 1. change (QCiC.Mq1.zlength (@nil Z)) with 0. lia. Qed.
Lemma len_cannot : forall str, QCiC.Mq1.zlength (concat (QdZp.pieces_cannot_open (strZ str))) = Z.of_nat (length str) + 18.
Proof. intros. unfold QdZp.pieces_cannot_open. cbn [concat]. rewrite !zlen_app, zlen_strZ. change (QCiC.Mq1.zlength (QdZp.str "cli: cannot open ")) with 17. change (QCiC.Mq1.zlength [10]) with 1. change (QCiC.Mq1.zlength (@nil Z)) with 0. lia. Qed.
Lemma len_readerr : forall str, QCiC.Mq1.zlength (concat (QdZp.pieces_read_error (strZ str))) = Z.of_nat (length str) + 20.
Proof. intros. unfold QdZp.pieces_read_error. cbn [concat]. rewrite !zlen_app, zlen_strZ. change (QCiC.Mq1.zlength (QdZp.str "cli: read error on ")) with 19. change (QCiC.Mq1.zlength [10]) with 1. change (QCiC.Mq1.zlength (@nil Z)) with 0. lia. Qed.

Lemma fprintf_s_core : forall (d : Qk8e.Mq0.diag_msg) (ps : list (list Z)) (msg : list byte)
(ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : QRjH.TSet) (lo fmt p : Z),
Qk8e.Mq0.s_diag (St:=unit) d = QdZp.stderr_fprintf ps -> QdZp.to_bytes (concat ps) = msg -> QCiC.Mq1.zlength (concat ps) < 2^64 ->
QQNJ.Mq8.diag_args d m (Z_to_bv 64 fmt) (Z_to_bv 64 p) lo (bv_unsigned sp) ->
QZsi.CK J cf -> QdM4.Mq3.STDERR0_A m -> Q9Ho.ISH m ->
QWxq_c1.stk QbFI.asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo + QdM4.Mq3.PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp + 16 <= 2^47 -> QZDE.mem_inv QbFI.asegs m -> QCcH.frm0 fc -> K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
QWxq_c1.munch (QdM4.Mq3.PFW_ERR lo (bv_unsigned sp)) m m' -> QWxq_c1.wmono QbFI.asegs m m' ->
QZDE.mem_inv QbFI.asegs m' ->
QWxq_c1.stk QbFI.asegs m' lo (bv_unsigned sp) -> QdM4.Mq3.STDERRC_A m' -> QCcH.fsaved F F' -> (QCcH.frm0 fc -> QCcH.frm0 fc') ->
QZsi.CNEXT J cf cf' -> Qfub.same_io cf cf' ->
QZsi.AJ J K cf' (QEpW.MS
(QWxq_c1.mkR ra sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (QEpW.ret_pc ra) fc' None m' (QsjA.seg_rom QbFI.asegs))) ->
QZsi.AJ J (QRjH.t_emit (QBxa.Mq5.W 2 msg) K) cf
(QEpW.MS
(QWxq_c1.mkR ra sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 QupI.F_STDERR) (Z_to_bv 64 fmt) (Z_to_bv 64 p)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 QdM4.Mq3.FPRINTF_V) fc None m (QsjA.seg_rom QbFI.asegs)).
Proof.
intros d ps msg ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo fmt p
ESD EOUT ELEN DA HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK.
pose proof (@Qx6U.fprintf_diag_proof BAND unit d
ra sp gp (Z_to_bv 64 Qwm6.Mq4.A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 QupI.F_STDERR) (Z_to_bv 64 fmt) (Z_to_bv 64 p)
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m tt lo band_guard
(@QpzM.Mqd.fwritex_stderr_proof BAND) (@QpzM.Mqf.stdio_write_flush_proof BAND) (stderr_wfile_init m ERR0) RT eq_refl
DA STK ltac:(unfold QQNJ.Mq8.FPRINTF_DEPTH, QdM4.Mq3.PF_STACK_A in *; lia) BLO SP47 (ssp_of_ISH m RT) MI FRM) as IMPL.
rewrite ESD in IMPL.
pose proof (QgTJ.Mq3.mdet_stderr_fprintf ps tt ELEN) as MD.
assert (EO : QCrt.Mq3.wev 2 (concat ps) = QBxa.Mq5.W 2 msg) by (unfold QCrt.Mq3.wev, QBxa.Mq5.W; rewrite EOUT; reflexivity).
rewrite <- EO.
refine (QCrt.Mq3.implM_vj_det QbFI.asegs LV Hwx Hsegs Hsh Hbx Hbc _ tt _ _ tt tt K cf _ IMPL (proj1 HCK) (QgTJ.Mq3.mio_stderr_fprintf _ tt) MD KN _).
intros c1 msv1 EV D C1 _.
apply (QNqr.vj_evt QbFI.asegs LV Hwx Hsegs _ (QNqr.silent_closed_srealizes QbFI.asegs LV K)).
eapply QwAs.Mq0.evt_mono; [exact EV|]. intros ms' Q.
destruct Q as (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & STK' & SWF & SSP & _).
destruct (cnext_of_drift cf c1 HCK D C1) as [CN SIO].
exact (HK q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 Ft fc' m' c1 MU WM MI' STK' (stderrc_of_wfile m' SWF) (fsaved_of F Ft FREG) (fun _ => FRM') CN SIO).
Time Qed.

Lemma diag_args_s : forall (m : word -> option byte) (p lo usp : Z) (str slack : list byte),
QZDE.bytes_at QbFI.asegs m p (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
(- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length str) < 2^17 ->
0 <= p -> usp <= p -> p + Z.of_nat (length str) + 9 <= 2^47 -> band_lo <= lo -> lo + QdM4.Mq3.PF_STACK_A <= usp ->
exists slack' : list byte,
QZDE.bytes_at QbFI.asegs m (bv_unsigned (Z_to_bv 64 p)) (QteI.Mqb.zb (strZ str) ++ Z_to_bv 8 0 :: slack')
/\ Forall (fun c => 0 < c < 256) (strZ str)
/\ ((- (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 1)) mod 8 <= QCiC.Mq1.zlength slack')
/\ (QCiC.Mq1.zlength (strZ str) <= QQNJ.Mq8.OUT_MAX)
/\ (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 1 + QCiC.Mq1.zlength slack' <= lo \/ usp <= bv_unsigned (Z_to_bv 64 p))
/\ (QQNJ.Mq8.GLOBALS_TOP + 64 <= bv_unsigned (Z_to_bv 64 p)) /\ (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 9 <= 2^47)
/\ (bv_unsigned (Z_to_bv 64 p) + QCiC.Mq1.zlength (strZ str) + 1 + QCiC.Mq1.zlength slack' <= 2^47).
Proof.
intros m p lo usp str slack BYT NZ SLK LEN P0 PSP P47 BLO LOS.
assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply QZDE.wa_unsigned; lia).
set (ns := Z.to_nat ((- (p + Z.of_nat (length str) + 1)) mod 8)).
assert (NS : Z.of_nat ns = (- (p + Z.of_nat (length str) + 1)) mod 8 /\ (ns <= 7)%nat /\ (ns <= length slack)%nat).
{ pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length str) + 1)) 8 ltac:(lia)) as B. unfold ns. split; [lia| split; lia]. }
destruct NS as (NS1 & NS2 & NS3).
exists (firstn ns slack). rewrite UP, zb_strZ, zlen_strZ. unfold QCiC.Mq1.zlength. rewrite firstn_length_le by exact NS3.
split.
{ rewrite <- (firstn_skipn ns slack) in BYT.
replace (str ++ Z_to_bv 8 0 :: firstn ns slack ++ skipn ns slack) with ((str ++ Z_to_bv 8 0 :: firstn ns slack) ++ skipn ns slack) in BYT
by (rewrite <- app_assoc; reflexivity).
exact (proj1 (proj1 (QZDE.bytes_at_app QbFI.asegs m p _ _) BYT)). }
split.
{ unfold strZ. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
assert (bv_unsigned b <> 0). { intros E0. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
lia. }
unfold QQNJ.Mq8.OUT_MAX, QQNJ.Mq8.GLOBALS_TOP, QdM4.Mq3.PF_STACK_A in *. repeat split; lia.
Time Qed.

Theorem fprintf_s_inst : QdM4.Mq3.fprintf_s_stmt J (@Q9Ho.ISH BAND) (@band_lo BAND).
Proof.
unfold QdM4.Mq3.fprintf_s_stmt.
intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cf K lo fmt p str slack
HCK FD2 HFMT -> -> -> BYT NZ SLK LEN UNP P0 PSP P47 ERR0 IMG RT STK CE BLO LOS A16 SP47 MI FRM RA2 KN HK.
pose proof (diag_args_s m p lo (bv_unsigned sp) str slack BYT NZ SLK LEN P0 PSP P47 BLO LOS) as DA.
destruct HFMT as [-> | [-> | ->]].
- refine (fprintf_s_core (Qk8e.Mq0.DUsage (strZ str)) (QdZp.pieces_usage (strZ str)) (QBxa.Mq5.msg_usage str) ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m cf K lo QdM4.Mq3.FMT_USAGE p eq_refl (out_usage str) _ (conj eq_refl DA) HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK).
rewrite len_usage. lia.
- refine (fprintf_s_core (Qk8e.Mq0.DCannotOpen (strZ str)) (QdZp.pieces_cannot_open (strZ str)) (QBxa.Mq5.msg_cannot_open str) ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m cf K lo QdM4.Mq3.FMT_CANNOT p eq_refl (out_cannot str) _ (conj eq_refl DA) HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK).
rewrite len_cannot. lia.
- refine (fprintf_s_core (Qk8e.Mq0.DReadError (strZ str)) (QdZp.pieces_read_error (strZ str)) (QBxa.Mq5.msg_read_error str) ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m cf K lo QdM4.Mq3.FMT_READERR p eq_refl (out_readerr str) _ (conj eq_refl DA) HCK ERR0 RT STK BLO LOS SP47 MI FRM KN HK).
rewrite len_readerr. lia.
Time Qed.
End Inst.
