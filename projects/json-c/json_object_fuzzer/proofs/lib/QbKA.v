(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD Qhd4 QZsi Q0TL QCKW QsRG Qnhz QBxa QRjH QsV0 Qn1e QMz4 Q9ox QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn Qwm6 QlKV QsKa QJZd Qw5U Qujl QnXa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD Qhd4.
Import QZsi.
Import Q0TL QCKW.Mq0.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq8 Qw5U.Mq4.
Import Qujl QnXa.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section AReadDirA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Lemma aread_dir_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet)
(junk : list byte) (cnt lo : Z) (errv : word),
CK J cf ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 RSTAGE -> a2 = Z_to_bv 64 cnt -> tp = Z_to_bv 64 A_TP ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = Some FdDir ->
1 <= cnt <= 65536 ->
rw_cells asegs m RSTAGE [CB (Z.to_nat cnt) junk] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 2272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 ->
asan_rt_ok m -> ro_cells asegs m REAL_READ_CELL [C8 (Z_to_bv 64 READ_SYM)] ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (cf' : config),
munch [(lo, bv_unsigned sp); (RSTAGE, RSTAGE + cnt); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 EISDIR)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AREAD) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HCK -> -> -> -> Hfd Hcnt DST ERR ST CEIL LO AL SPH RT RR MI RA HK.
unfold AREAD, RSTAGE, REAL_READ_CELL, A_TP in *.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (0x612150, 0x612150 + cnt); (6434400 - 164, 6434400 - 160)] m) as MU.

pose proof (proj1 (Forall_forall _ _) RT (0xf07d8, [Z_to_bv 8 1])
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (try (left; reflexivity); right))) as INITED.
pose proof (proj1 (Forall_forall _ _) RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL))
ltac:(unfold a4_rt_cells; apply in_or_app; right; left; reflexivity)) as GOT.
pose proof (proj1 (Forall_forall _ _) RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB))
ltac:(unfold a4_rt_cells; apply in_or_app; right; right; left; reflexivity)) as CELL.
cbn [fst snd] in INITED, GOT, CELL. unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL.
apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (INITEDc : ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact INITED]). clear INITED.
assert (CW : forall A0 cs x, rw_cells asegs m A0 cs -> A0 <= x < A0 + Z.of_nat (cells_size cs) -> wview asegs m (wa x) <> None).
{ intros A0 cs x [_ (W1 & W2 & W3)] Hx. replace x with (A0 + (x - A0)) by lia. apply W3. lia. }
apply (aj_evt J).
carve_frame 2128%nat ST.
do 12 step.
step.
eapply try_asan_init_spec; [assumption | exact INITEDc | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x5279c)) with (Z_to_bv 64 0x5279c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 6 step.
step.
replace (ret_pc (Z_to_bv 64 READ_SYM)) with (Z_to_bv 64 READ_SYM) by (symmetry; apply ret_pc_even; [unfold READ_SYM; lia|reflexivity]).
apply evt_done.

eapply (read_dir_cps_A J SYS) with (lo := lo) (dst := 0x612150) (cnt := cnt);
[ exact HCK | reflexivity | reflexivity | reflexivity | exact Hfd | lia | lia | rc_lia_prep; lia | rc_lia_prep; lia
| eexists; exact DST | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; exact ERR | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros a1y a2y a3y a4y a5y a6y a7y m3 c3 MU3 WM3 MI3 ST3 ERR3 HN3 SIO3.
rc_lia_prep. unfold alloc_ceiling in CEIL.
clear DST.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end; clear MU3 WM3.
apply (aj_evt J).
replace (ret_pc (Z_to_bv 64 337848)) with (Z_to_bv 64 337848) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_falsex.
step.
match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; vm_compute; reflexivity) | _ => idtac end.
cbv iota.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with m3 => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with m3 => fail | _ => clear H end end.
do 9 step.
apply evt_done.
eapply HK; [exact MU | exact WM | exact MI3 | release_frame FR ST3 (bv_unsigned sp); exact ST3 | exact ERR3 | exact HN3 | exact SIO3].
Qed.
End AReadDirA.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi Uaccess.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei Open.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi Qc6I QJFf Qsn5 QBrp Q2ui Q1KO QRGF QTgd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.

Import QQIi.
Import Qc6I QJFf Qsn5 QBrp Q2ui Q1KO.
Import QRGF.
Import QTgd.Mq0 Q0TL.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section Inst.
Context {fF : QsRG.Mq0.FPF} {fC : QsRG.Mq0.FPC}.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Local Notation J := (aj_base_vj segs LV Hwx Hsegs).

Lemma areg_epend : forall regs pc mem rom x8 (r : bv 5), r <> 0%bv -> areg (Q9ox.Mq0.epend regs pc mem rom x8) r = QsRG.Mq0.getr regs r.
Proof.
intros regs pc mem rom x8 r Hr. unfold areg, QsRG.Mq0.getr. cbn [ms_regs Q9ox.Mq0.epend].
destruct (bv_eqb r 0) eqn:E; [apply Fs.bv_eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma nret_epend_ret : forall regs pc mem rom x8 r,
nret (Q9ox.Mq0.epend regs pc mem rom x8) (eff0 r) = QsRG.Mq0.mkst (QsRG.Mq0.regupd regs 10 r) (QsRG.Mq0.v_addi pc 4) mem rom.
Proof. intros. unfold nret, eff0. apply Q9ox.Mq0.adv_eff_ret_epend. Qed.

Theorem aj_sys_vj : aj_sys segs J.
Proof.
constructor.
-
intros regs pc mem rom c fd e T HCK H17 H10 Hfd Hlk HK.
apply (ajv_close segs LV Hwx Hsegs Hsh Hbx Hbc T fd e c _); [| exact HCK | exact Hlk |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|]. rewrite areg_epend by discriminate. exact H10.
+ intros c' HN F S. rewrite nret_epend_ret. exact (HK c' HN F S).
-
intros regs pc mem rom c fd T HCK H17 H10 Hfd H11 HK.
apply (ajv_ioctl_winsz segs LV Hwx Hsegs Hsh Hbx Hbc T fd 21523 c _); [| exact HCK |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|]. split; [reflexivity|].
rewrite !areg_epend by discriminate. split; assumption.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem rom c fd buf cnt p off data T HCK H17 H10 Hfd H11 H12 Hcnt Htop Hwr Hlk Hfs bs HK.
apply (ajv_read_file segs LV Hwx Hsegs Hsh Hbx Hbc T fd buf cnt p off data c _); [| exact HCK | exact Hlk | exact Hfs |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|].
rewrite !areg_epend by discriminate. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact Hcnt|]. split; [exact Htop | exact Hwr].
+ intros c' HN F S. exact (HK c' HN F S).
-
intros regs pc mem rom c fd buf cnt T HCK H17 H10 Hfd H11 H12 Hcnt Htop Hwr Hlk HK.
apply (ajv_read_dir segs LV Hwx Hsegs Hsh Hbx Hbc T fd buf cnt c _); [| exact HCK | exact Hlk |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|].
rewrite !areg_epend by discriminate. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact Hcnt|]. split; [exact Htop | exact Hwr].
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c path T HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hlen HK.
apply (ajv_open_toolong segs LV Hwx Hsegs Hsh Hbx Hbc T path c _); [| exact HCK | exact Hlen |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c T HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) HK.
apply (ajv_open_empty segs LV Hwx Hsegs Hsh Hbx Hbc T c _); [| exact HCK |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c path T HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hlen Hne Hdot Hfs HK.
apply (ajv_open_absent segs LV Hwx Hsegs Hsh Hbx Hbc T path c _); [| exact HCK | exact Hlen | exact Hne | exact Hdot | exact Hfs |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c path d TA TB HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hlen Hne Hdot Hfs Hfree HA0 HB0 KA KB.
refine (ajv_open_file segs LV Hsegs Hsh Hbx Hbc TA TB path d c _ _ HCK Hlen Hne Hdot Hfs Hfree HA0 HB0 _ _).
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros e c' He HN F S. unfold efferr. rewrite nret_epend_ret. exact (KA e c' He HN (conj F S)).
+ intros c' HN F S. rewrite nret_epend_ret. exact (KB c' HN F S).
-
intros regs pc mem c TA TB HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hfree HA0 HB0 KA KB.
refine (ajv_open_dot segs LV Hsegs Hsh Hbx Hbc TA TB c _ _ HCK Hfree HA0 HB0 _ _).
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros e c' He HN F S. unfold efferr. rewrite nret_epend_ret. exact (KA e c' He HN (conj F S)).
+ intros c' HN F S. rewrite nret_epend_ret. exact (KB c' HN F S).
-
intros regs pc mem c fd iovs bufs T HCK H17 Hfd H10 H12 Hnb Hmax Harr Hbufs Htop Htops Hne HK.
apply (ajv_writev segs LV Hsegs Hsh Hbx Hbc fd bufs T c _); [| exact HCK | exact Hne |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate.
split; [reflexivity|]. split; [exact Hfd|]. split; [exact H10|]. split; [exact H12|]. split; [exact Hnb|]. split; [exact Hmax|]. split; [reflexivity|].
exists iovs. split; [exact Harr|]. split; [exact Hbufs|]. split; [exact Htop | exact Htops].
+ intros k c' Hk1 Hk2 HN F S. rewrite nret_epend_ret. exact (HK k c' Hk1 Hk2 HN (conj F S)).
-
intros regs pc mem c fd iovs bufs T HCK H17 Hfd H10 H12 Hnb Hnil Harr Hbufs Htop Htops HK.
apply (ajv_writev0 segs LV Hwx Hsegs Hsh Hbx Hbc T fd bufs c _); [| exact HCK | exact Hnil |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate.
split; [reflexivity|]. split; [exact Hfd|]. split; [exact H10|]. split; [exact H12|]. split; [exact Hnb|]. split; [rewrite Hnil; cbn; unfold writev_bytes_max; lia|]. split; [reflexivity|].
exists iovs. split; [exact Harr|]. split; [exact Hbufs|]. split; [exact Htop | exact Htops].
+ intros c' HN F S. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem rom c code HCK H17 H10.
apply (ajv_exit segs LV Hsegs Hsh Hbx Hbc code c _); [| exact HCK].
cbn [at_nodeA at_node]. rewrite !areg_epend by discriminate. split; [| exact H10].
destruct H17 as [-> | ->]; [left | right]; reflexivity.
Qed.
End Inst.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek QRUw Q3Gm QGm2 QhtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq8.
Import Q3Gm.Mq0.
Import QGm2.Mq0 QhtD.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lbu_le8_z : forall z, 0 <= z < 2^64 ->
zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn 0 (le8 (Z_to_bv 64 z)))))) = Z_to_bv 64 (z mod 256).
Proof.
intros z Hz. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia.
cbn [Z_to_le_bytes firstn skipn].
rewrite zext_extract_byte. unfold zxb. f_equal.
Qed.
Section Body.
Context {RC__ : Q6q3.RunConsts}.

Lemma unreg_body : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p beg sz szrz nm mo dyn loc odr k : Z) (junk : list byte),
mem_inv asegs m ->
ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xed310 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xef35c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
ro_cells asegs m p [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); CB 8 (le8 (Z_to_bv 64 szrz)); C8 (Z_to_bv 64 nm);
C8 (Z_to_bv 64 mo); C8 (Z_to_bv 64 dyn); C8 (Z_to_bv 64 loc); C8 (Z_to_bv 64 odr)] ->
0xea960 <= p -> p + 64 <= 0xec420 -> p mod 8 = 0 ->
0x10000 <= beg -> beg mod 8 = 0 -> szrz mod 8 = 0 -> 8 <= szrz <= 4096 -> beg + szrz <= 0x645000 ->
rw_cells asegs m (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) junk] ->
(odr = 0 \/ odr = 2^64 - 1) ->
1 <= k < 2^32 ->
(forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
munch [(0x7fff8000 + beg / 8, 0x7fff8000 + beg / 8 + szrz / 8)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (szrz / 8)))] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x181628) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64)) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
F (Z_to_bv 64 (if Z.eqb k 1 then 0x4d680 else 0x4d47c)) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x181628) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 p) s5 s6 (Z_to_bv 64 0xe7db0) s8 (Z_to_bv 64 0xed2f8) (Z_to_bv 64 0xefaf8) (Z_to_bv 64 k) t3 t4 t5 t6)
F (Z_to_bv 64 0x4d47c) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros MI INITED RG SB CP THR RM REC Hp1 Hp2 Hp8 Hb1 Hb8 Hz8 Hz1 Hbe SH ODR Hk K.
step.
eapply asan_inited_spec; [exact MI | exact INITED |].
replace (ret_pc (Z_to_bv 64 316544)) with (Z_to_bv 64 316544 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. rewrite ?sxb_small by lia.
if_falsex.
step.
match goal with |- context [sx32 (Z_to_bv 64 1)] => replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
step. if_truex.
step. if_falsex.
step. step. step. step. step. step.
Ltac fold_closed_bv :=
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac | Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac
end;
let v := eval vm_compute in e in
lazymatch v with
| Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
end;
change (Z_to_bv 64 e) with (Z_to_bv 64 v)
end
end.
fold_closed_bv.
step. if_truex.
step.
replace (Z.land (bv_unsigned (Z_to_bv 64 beg)) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step. rewrite lbu_le8_z by lia.
step. replace (Z.land (bv_unsigned (Z_to_bv 64 (szrz mod 256))) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step.
eapply can_poison_spec; [exact MI | exact CP |].
replace (ret_pc (Z_to_bv 64 316852)) with (Z_to_bv 64 316852 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_falsex.
do 12 step.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite !(unsigned_lit beg) by lia.
rewrite !(unsigned_lit (beg + szrz + -8)) by lia.
replace ((beg + szrz + -8) / 8) with (beg / 8 + szrz / 8 - 1) by lia.
rewrite !unsigned_lit by lia.
replace (2147450880 + (beg / 8 + szrz / 8 - 1) + 1 - (2147450880 + beg / 8)) with (szrz / 8) by lia.
step. if_truex.
step. step. step.

eapply evt_cut; [eapply Q3Gm.Mq0.memset_spec; [rewrite !unsigned_lit by lia; exact SH | exact MI] |].
intros ms' PO. unfold memset_post in PO.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & E & MU & WM & MI1 & SH1). subst ms'.
rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in SH1 by lia.
replace (ret_pc (Z_to_bv 64 0x4d464)) with (Z_to_bv 64 0x4d464 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (DJ : forall A n, A + n <= 0x7fffa000 -> disjoint_from [(2147450880 + beg / 8, 2147450880 + beg / 8 + szrz / 8)] A n).
{ intros A n HA. cbn [disjoint_from]. split; [|exact I]. left. lia. }
apply (ro_cells_transport rsegs _ m m1 _ _ REC MU) in REC || pose proof (ro_cells_transport rsegs _ m m1 _ _ REC MU ltac:(apply DJ; cbn; lia)) as REC1.
clear REC. rename REC1 into REC.
step. step. step.
assert (CND : negb (bv_ltu (Z_to_bv 64 (odr + 1)) (Z_to_bv 64 2)) = false) by (destruct ODR as [-> | ->]; vm_compute; reflexivity).
rewrite CND. try match goal with |- context [if false then ?a else ?b] => change (if false then a else b) with b end.
step. step.
replace (Z_to_bv 64 (k + -1) : word) with (Z_to_bv 64 (k - 1) : word) by (f_equal; lia).
step.
destruct (Z.eqb_spec k 1) as [Hk1|Hk1].
- subst k. if_truex. cbn [Z.eqb Pos.eqb] in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1].
- if_falsex.
try rewrite (proj2 (Z.eqb_neq k 1) Hk1) in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1].
Qed.
End Body.

Definition g_beg (r : list Z) : Z := nth 0 r 0.
Definition g_szrz (r : list Z) : Z := nth 2 r 0.
Definition g_odr (r : list Z) : Z := nth 7 r 0.

Definition g_cells (r : list Z) : list cell :=
[C8 (Z_to_bv 64 (nth 0 r 0)); C8 (Z_to_bv 64 (nth 1 r 0)); CB 8 (le8 (Z_to_bv 64 (nth 2 r 0))); C8 (Z_to_bv 64 (nth 3 r 0));
C8 (Z_to_bv 64 (nth 4 r 0)); C8 (Z_to_bv 64 (nth 5 r 0)); C8 (Z_to_bv 64 (nth 6 r 0)); C8 (Z_to_bv 64 (nth 7 r 0))].
Definition g_sh (r : list Z) : Z * Z := (2147450880 + g_beg r / 8, 2147450880 + g_beg r / 8 + g_szrz r / 8).
Definition g_ok (r : list Z) : Prop :=
0x10000 <= g_beg r /\ g_beg r mod 8 = 0 /\ g_szrz r mod 8 = 0 /\ 8 <= g_szrz r <= 4096 /\ g_beg r + g_szrz r <= 0x645000
/\ (g_odr r = 0 \/ g_odr r = 2^64 - 1).
Fixpoint chained (l : list (list Z)) : Prop :=
match l with
| [] => True
| r :: l' => Forall (fun r' => g_beg r + g_szrz r <= g_beg r') l' /\ chained l'
end.

Section Loop.
Context {RC__ : Q6q3.RunConsts}.

Fixpoint recs_ro (m : word -> option byte) (p : Z) (l : list (list Z)) : Prop :=
match l with
| [] => True
| r :: l' => ro_cells asegs m p (g_cells r) /\ recs_ro m (p + 64) l'
end.
Definition shadows_rw (m : word -> option byte) (l : list (list Z)) : Prop :=
Forall (fun r => exists junk, rw_cells asegs m (fst (g_sh r)) [CB (Z.to_nat (g_szrz r / 8)) junk]) l.

Lemma recs_ro_transport : forall l W m m' p,
recs_ro m p l -> munch W m m' -> (forall q, p <= q -> q + 64 <= p + 64 * Z.of_nat (length l) -> disjoint_from W q 64) ->
recs_ro m' p l.
Proof.
induction l as [|r l IH]; intros W m m' p H MU HD; cbn [recs_ro] in *; [exact I|].
destruct H as [H1 H2]. split.
- eapply ro_cells_transport; [exact H1 | exact MU |]. cbn [cells_size csize g_cells Nat.add length]. rewrite ?length_le8. cbn. apply HD; cbn [length] in *; lia.
- eapply IH; [exact H2 | exact MU |]. intros q Hq1 Hq2. apply HD; cbn [length] in *; lia.
Qed.

End Loop.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QZsi.
Import Qfub QCKW.Mq5.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QJZd.Mqg Qw5U.
Import Qujl.Mq4 QnXa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section AReadDirA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Lemma aread_dir_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet)
(junk : list byte) (cnt lo : Z) (errv : word),
CK J cf ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 RSTAGE -> a2 = Z_to_bv 64 cnt -> tp = Z_to_bv 64 A_TP ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = Some FdDir ->
1 <= cnt <= 65536 ->
rw_cells asegs m RSTAGE [CB (Z.to_nat cnt) junk] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 2272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 2^47 ->
asan_rt_ok m -> ro_cells asegs m REAL_READ_CELL [C8 (Z_to_bv 64 READ_SYM)] ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (cf' : config),
munch [(lo, bv_unsigned sp); (RSTAGE, RSTAGE + cnt); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 EISDIR)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AREAD) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HCK -> -> -> -> Hfd Hcnt DST ERR ST CEIL LO AL SPH RT RR MI RA HK.
unfold AREAD, RSTAGE, REAL_READ_CELL, A_TP in *.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (0x614810, 0x614810 + cnt); (6444320 - 164, 6444320 - 160)] m) as MU.

pose proof (proj1 (Forall_forall _ _) RT (0xf2e98, [Z_to_bv 8 1])
ltac:(unfold a4_rt_cells, a4_rt_consts; cbn [app]; repeat (try (left; reflexivity); right))) as INITED.
pose proof (proj1 (Forall_forall _ _) RT (A_GOT_SB, le8 (Z_to_bv 64 A_SB_CELL))
ltac:(unfold a4_rt_cells; apply in_or_app; right; left; reflexivity)) as GOT.
pose proof (proj1 (Forall_forall _ _) RT (A_SB_CELL, le8 (Z_to_bv 64 A_SB))
ltac:(unfold a4_rt_cells; apply in_or_app; right; right; left; reflexivity)) as CELL.
cbn [fst snd] in INITED, GOT, CELL. unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL.
apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (INITEDc : ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact INITED]). clear INITED.
assert (CW : forall A0 cs x, rw_cells asegs m A0 cs -> A0 <= x < A0 + Z.of_nat (cells_size cs) -> wview asegs m (wa x) <> None).
{ intros A0 cs x [_ (W1 & W2 & W3)] Hx. replace x with (A0 + (x - A0)) by lia. apply W3. lia. }
apply (aj_evt J).
carve_frame 2128%nat ST.
do 12 step.
step.
eapply try_asan_init_spec; [assumption | exact INITEDc | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST2.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x52b74)) with (Z_to_bv 64 0x52b74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 6 step.
step.
replace (ret_pc (Z_to_bv 64 READ_SYM)) with (Z_to_bv 64 READ_SYM) by (symmetry; apply ret_pc_even; [unfold READ_SYM; lia|reflexivity]).
apply evt_done.

eapply (read_dir_cps_A J SYS) with (lo := lo) (dst := 0x614810) (cnt := cnt);
[ exact HCK | reflexivity | reflexivity | reflexivity | exact Hfd | lia | lia | rc_lia_prep; lia | rc_lia_prep; lia
| eexists; exact DST | rewrite unsigned_lit by lia; exact ST2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; exact ERR | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros a1y a2y a3y a4y a5y a6y a7y m3 c3 MU3 WM3 MI3 ST3 ERR3 HN3 SIO3.
rc_lia_prep. unfold alloc_ceiling in CEIL.
clear DST.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end; clear MU3 WM3.
apply (aj_evt J).
replace (ret_pc (Z_to_bv 64 338832)) with (Z_to_bv 64 338832) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_falsex.
step.
match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; vm_compute; reflexivity) | _ => idtac end.
cbv iota.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with m3 => fail | _ => clear H end end.
repeat match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with m3 => fail | _ => clear H end end.
do 9 step.
apply evt_done.
eapply HK; [exact MU | exact WM | exact MI3 | release_frame FR ST3 (bv_unsigned sp); exact ST3 | exact ERR3 | exact HN3 | exact SIO3].
Qed.
End AReadDirA.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.

Import QQIi.
Import Qc6I QJFf Qsn5 QBrp Q2ui Q1KO.
Import QRGF.
Import QTgd Qfub.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Section Inst.
Context {fF : QsRG.Mq0.FPF} {fC : QsRG.Mq0.FPC}.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Local Notation J := (aj_base_vj segs LV Hwx Hsegs).

Lemma areg_epend : forall regs pc mem rom x8 (r : bv 5), r <> 0%bv -> areg (Q9ox.Mq0.epend regs pc mem rom x8) r = QsRG.Mq0.getr regs r.
Proof.
intros regs pc mem rom x8 r Hr. unfold areg, QsRG.Mq0.getr. cbn [ms_regs Q9ox.Mq0.epend].
destruct (bv_eqb r 0) eqn:E; [apply Fs.bv_eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma nret_epend_ret : forall regs pc mem rom x8 r,
nret (Q9ox.Mq0.epend regs pc mem rom x8) (eff0 r) = QsRG.Mq0.mkst (QsRG.Mq0.regupd regs 10 r) (QsRG.Mq0.v_addi pc 4) mem rom.
Proof. intros. unfold nret, eff0. apply Q9ox.Mq0.adv_eff_ret_epend. Qed.

Theorem aj_sys_vj : aj_sys segs J.
Proof.
constructor.
-
intros regs pc mem rom c fd e T HCK H17 H10 Hfd Hlk HK.
apply (ajv_close segs LV Hwx Hsegs Hsh Hbx Hbc T fd e c _); [| exact HCK | exact Hlk |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|]. rewrite areg_epend by discriminate. exact H10.
+ intros c' HN F S. rewrite nret_epend_ret. exact (HK c' HN F S).
-
intros regs pc mem rom c fd T HCK H17 H10 Hfd H11 HK.
apply (ajv_ioctl_winsz segs LV Hwx Hsegs Hsh Hbx Hbc T fd 21523 c _); [| exact HCK |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|]. split; [reflexivity|].
rewrite !areg_epend by discriminate. split; assumption.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem rom c fd buf cnt p off data T HCK H17 H10 Hfd H11 H12 Hcnt Htop Hwr Hlk Hfs bs HK.
apply (ajv_read_file segs LV Hwx Hsegs Hsh Hbx Hbc T fd buf cnt p off data c _); [| exact HCK | exact Hlk | exact Hfs |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|].
rewrite !areg_epend by discriminate. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact Hcnt|]. split; [exact Htop | exact Hwr].
+ intros c' HN F S. exact (HK c' HN F S).
-
intros regs pc mem rom c fd buf cnt T HCK H17 H10 Hfd H11 H12 Hcnt Htop Hwr Hlk HK.
apply (ajv_read_dir segs LV Hwx Hsegs Hsh Hbx Hbc T fd buf cnt c _); [| exact HCK | exact Hlk |].
+ cbn [at_nodeA at_node]. rewrite H17. split; [reflexivity|]. split; [exact Hfd|].
rewrite !areg_epend by discriminate. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact Hcnt|]. split; [exact Htop | exact Hwr].
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c path T HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hlen HK.
apply (ajv_open_toolong segs LV Hwx Hsegs Hsh Hbx Hbc T path c _); [| exact HCK | exact Hlen |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c T HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) HK.
apply (ajv_open_empty segs LV Hwx Hsegs Hsh Hbx Hbc T c _); [| exact HCK |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c path T HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hlen Hne Hdot Hfs HK.
apply (ajv_open_absent segs LV Hwx Hsegs Hsh Hbx Hbc T path c _); [| exact HCK | exact Hlen | exact Hne | exact Hdot | exact Hfs |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros c' HN F S. unfold efferr. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem c path d TA TB HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hlen Hne Hdot Hfs Hfree HA0 HB0 KA KB.
refine (ajv_open_file segs LV Hsegs Hsh Hbx Hbc TA TB path d c _ _ HCK Hlen Hne Hdot Hfs Hfree HA0 HB0 _ _).
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros e c' He HN F S. unfold efferr. rewrite nret_epend_ret. exact (KA e c' He HN (conj F S)).
+ intros c' HN F S. rewrite nret_epend_ret. exact (KB c' HN F S).
-
intros regs pc mem c TA TB HCK (H17 & H10 & Hfl & Hnz & Hsl & Hdd & Hby) Hfree HA0 HB0 KA KB.
refine (ajv_open_dot segs LV Hsegs Hsh Hbx Hbc TA TB c _ _ HCK Hfree HA0 HB0 _ _).
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate. repeat (split; [first [reflexivity | assumption]|]). exact Hby.
+ intros e c' He HN F S. unfold efferr. rewrite nret_epend_ret. exact (KA e c' He HN (conj F S)).
+ intros c' HN F S. rewrite nret_epend_ret. exact (KB c' HN F S).
-
intros regs pc mem c fd iovs bufs T HCK H17 Hfd H10 H12 Hnb Hmax Harr Hbufs Htop Htops Hne HK.
apply (ajv_writev segs LV Hsegs Hsh Hbx Hbc fd bufs T c _); [| exact HCK | exact Hne |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate.
split; [reflexivity|]. split; [exact Hfd|]. split; [exact H10|]. split; [exact H12|]. split; [exact Hnb|]. split; [exact Hmax|]. split; [reflexivity|].
exists iovs. split; [exact Harr|]. split; [exact Hbufs|]. split; [exact Htop | exact Htops].
+ intros k c' Hk1 Hk2 HN F S. rewrite nret_epend_ret. exact (HK k c' Hk1 Hk2 HN (conj F S)).
-
intros regs pc mem c fd iovs bufs T HCK H17 Hfd H10 H12 Hnb Hnil Harr Hbufs Htop Htops HK.
apply (ajv_writev0 segs LV Hwx Hsegs Hsh Hbx Hbc T fd bufs c _); [| exact HCK | exact Hnil |].
+ cbn [at_nodeA at_node]. rewrite H17. rewrite !areg_epend by discriminate.
split; [reflexivity|]. split; [exact Hfd|]. split; [exact H10|]. split; [exact H12|]. split; [exact Hnb|]. split; [rewrite Hnil; cbn; unfold writev_bytes_max; lia|]. split; [reflexivity|].
exists iovs. split; [exact Harr|]. split; [exact Hbufs|]. split; [exact Htop | exact Htops].
+ intros c' HN F S. rewrite nret_epend_ret. exact (HK c' HN (conj F S)).
-
intros regs pc mem rom c code HCK H17 H10.
apply (ajv_exit segs LV Hsegs Hsh Hbx Hbc code c _); [| exact HCK].
cbn [at_nodeA at_node]. rewrite !areg_epend by discriminate. split; [| exact H10].
destruct H17 as [-> | ->]; [left | right]; reflexivity.
Qed.
End Inst.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3Gm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3Gm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhtD.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lbu_le8_z : forall z, 0 <= z < 2^64 ->
zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn 0 (le8 (Z_to_bv 64 z)))))) = Z_to_bv 64 (z mod 256).
Proof.
intros z Hz. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia.
cbn [Z_to_le_bytes firstn skipn].
rewrite zext_extract_byte. unfold zxb. f_equal.
Qed.
Section Body.
Context {RC__ : Q6q3.RunConsts}.

Lemma unreg_body : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(p beg sz szrz nm mo dyn loc odr k : Z) (junk : list byte),
mem_inv asegs m ->
ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xef9d0 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xf1a1c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
ro_cells asegs m p [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); CB 8 (le8 (Z_to_bv 64 szrz)); C8 (Z_to_bv 64 nm);
C8 (Z_to_bv 64 mo); C8 (Z_to_bv 64 dyn); C8 (Z_to_bv 64 loc); C8 (Z_to_bv 64 odr)] ->
0xed040 <= p -> p + 64 <= 0xeeb00 -> p mod 8 = 0 ->
0x10000 <= beg -> beg mod 8 = 0 -> szrz mod 8 = 0 -> 8 <= szrz <= 4096 -> beg + szrz <= 0x647000 ->
rw_cells asegs m (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) junk] ->
(odr = 0 \/ odr = 2^64 - 1) ->
1 <= k < 2^32 ->
(forall (ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
munch [(0x7fff8000 + beg / 8, 0x7fff8000 + beg / 8 + szrz / 8)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' (0x7fff8000 + beg / 8) [CB (Z.to_nat (szrz / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (szrz / 8)))] ->
evt asegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x183ce8) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3 (Z_to_bv 64 (p + 64)) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
F (Z_to_bv 64 (if Z.eqb k 1 then 0x4da58 else 0x4d854)) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x183ce8) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) s3 (Z_to_bv 64 p) s5 s6 (Z_to_bv 64 0xea1d0) s8 (Z_to_bv 64 0xef9b8) (Z_to_bv 64 0xf21b8) (Z_to_bv 64 k) t3 t4 t5 t6)
F (Z_to_bv 64 0x4d854) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros MI INITED RG SB CP THR RM REC Hp1 Hp2 Hp8 Hb1 Hb8 Hz8 Hz1 Hbe SH ODR Hk K.
step.
eapply asan_inited_spec; [exact MI | exact INITED |].
replace (ret_pc (Z_to_bv 64 317528)) with (Z_to_bv 64 317528 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. rewrite ?sxb_small by lia.
if_falsex.
step.
match goal with |- context [sx32 (Z_to_bv 64 1)] => replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
step. if_truex.
step. if_falsex.
step. step. step. step. step. step.
Ltac fold_closed_bv :=
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac | Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac
end;
let v := eval vm_compute in e in
lazymatch v with
| Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
end;
change (Z_to_bv 64 e) with (Z_to_bv 64 v)
end
end.
fold_closed_bv.
step. if_truex.
step.
replace (Z.land (bv_unsigned (Z_to_bv 64 beg)) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step. rewrite lbu_le8_z by lia.
step. replace (Z.land (bv_unsigned (Z_to_bv 64 (szrz mod 256))) 7) with 0 by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
step. if_falsex.
step.
eapply can_poison_spec; [exact MI | exact CP |].
replace (ret_pc (Z_to_bv 64 317836)) with (Z_to_bv 64 317836 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_falsex.
do 12 step.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite !(unsigned_lit beg) by lia.
rewrite !(unsigned_lit (beg + szrz + -8)) by lia.
replace ((beg + szrz + -8) / 8) with (beg / 8 + szrz / 8 - 1) by lia.
rewrite !unsigned_lit by lia.
replace (2147450880 + (beg / 8 + szrz / 8 - 1) + 1 - (2147450880 + beg / 8)) with (szrz / 8) by lia.
step. if_truex.
step. step. step.

eapply evt_cut; [eapply Q3Gm.memset_spec; [rewrite !unsigned_lit by lia; exact SH | exact MI] |].
intros ms' PO. unfold memset_post in PO.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & E & MU & WM & MI1 & SH1). subst ms'.
rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in SH1 by lia.
replace (ret_pc (Z_to_bv 64 0x4d83c)) with (Z_to_bv 64 0x4d83c : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (DJ : forall A n, A + n <= 0x7fffa000 -> disjoint_from [(2147450880 + beg / 8, 2147450880 + beg / 8 + szrz / 8)] A n).
{ intros A n HA. cbn [disjoint_from]. split; [|exact I]. left. lia. }
apply (ro_cells_transport rsegs _ m m1 _ _ REC MU) in REC || pose proof (ro_cells_transport rsegs _ m m1 _ _ REC MU ltac:(apply DJ; cbn; lia)) as REC1.
clear REC. rename REC1 into REC.
step. step. step.
assert (CND : negb (bv_ltu (Z_to_bv 64 (odr + 1)) (Z_to_bv 64 2)) = false) by (destruct ODR as [-> | ->]; vm_compute; reflexivity).
rewrite CND. try match goal with |- context [if false then ?a else ?b] => change (if false then a else b) with b end.
step. step.
replace (Z_to_bv 64 (k + -1) : word) with (Z_to_bv 64 (k - 1) : word) by (f_equal; lia).
step.
destruct (Z.eqb_spec k 1) as [Hk1|Hk1].
- subst k. if_truex. cbn [Z.eqb Pos.eqb] in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1].
- if_falsex.
try rewrite (proj2 (Z.eqb_neq k 1) Hk1) in K.
eapply K; [exact MU | exact WM | exact MI1 | exact SH1].
Qed.
End Body.

Definition g_beg (r : list Z) : Z := nth 0 r 0.
Definition g_szrz (r : list Z) : Z := nth 2 r 0.
Definition g_odr (r : list Z) : Z := nth 7 r 0.

Definition g_cells (r : list Z) : list cell :=
[C8 (Z_to_bv 64 (nth 0 r 0)); C8 (Z_to_bv 64 (nth 1 r 0)); CB 8 (le8 (Z_to_bv 64 (nth 2 r 0))); C8 (Z_to_bv 64 (nth 3 r 0));
C8 (Z_to_bv 64 (nth 4 r 0)); C8 (Z_to_bv 64 (nth 5 r 0)); C8 (Z_to_bv 64 (nth 6 r 0)); C8 (Z_to_bv 64 (nth 7 r 0))].
Definition g_sh (r : list Z) : Z * Z := (2147450880 + g_beg r / 8, 2147450880 + g_beg r / 8 + g_szrz r / 8).
Definition g_ok (r : list Z) : Prop :=
0x10000 <= g_beg r /\ g_beg r mod 8 = 0 /\ g_szrz r mod 8 = 0 /\ 8 <= g_szrz r <= 4096 /\ g_beg r + g_szrz r <= 0x647000
/\ (g_odr r = 0 \/ g_odr r = 2^64 - 1).
Fixpoint chained (l : list (list Z)) : Prop :=
match l with
| [] => True
| r :: l' => Forall (fun r' => g_beg r + g_szrz r <= g_beg r') l' /\ chained l'
end.

Section Loop.
Context {RC__ : Q6q3.RunConsts}.

Fixpoint recs_ro (m : word -> option byte) (p : Z) (l : list (list Z)) : Prop :=
match l with
| [] => True
| r :: l' => ro_cells asegs m p (g_cells r) /\ recs_ro m (p + 64) l'
end.
Definition shadows_rw (m : word -> option byte) (l : list (list Z)) : Prop :=
Forall (fun r => exists junk, rw_cells asegs m (fst (g_sh r)) [CB (Z.to_nat (g_szrz r / 8)) junk]) l.

Lemma recs_ro_transport : forall l W m m' p,
recs_ro m p l -> munch W m m' -> (forall q, p <= q -> q + 64 <= p + 64 * Z.of_nat (length l) -> disjoint_from W q 64) ->
recs_ro m' p l.
Proof.
induction l as [|r l IH]; intros W m m' p H MU HD; cbn [recs_ro] in *; [exact I|].
destruct H as [H1 H2]. split.
- eapply ro_cells_transport; [exact H1 | exact MU |]. cbn [cells_size csize g_cells Nat.add length]. rewrite ?length_le8. cbn. apply HD; cbn [length] in *; lia.
- eapply IH; [exact H2 | exact MU |]. intros q Hq1 Hq2. apply HD; cbn [length] in *; lia.
Qed.

End Loop.
