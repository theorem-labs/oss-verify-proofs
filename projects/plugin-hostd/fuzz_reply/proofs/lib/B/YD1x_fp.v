(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, the fuzz_reply.asan-ubsan twin of lib/A/AD1x_fp.v (RelocA-2,
   a working branch 50f0c528115): the exit's after-loop view IMG_XLF built on B/YD2f_fp.v's clipped
   after-call view IMG_LF instead of IMG_L, so that the exit premise does not assert a byte of fuzz_reply's program globals
   G_fr_c TfibB; its data checks, the exit state S_JXF that starts from it (at B's exit 0x8cb34, return 0x8cb38: B/YD28.v
   S_JX), and ex_consts_chkF over B/YE23.v's ex_consts. Text copied from B/YD1x.v, YD28.v and YD1j.v as AD1x_fp copies
   their A twins; the count is read by vm_compute on this image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK14 YP0m YP09 YP02 YP0l YP06 YP03 YP01 YN3v YI04 YL09 YK04 YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD2j YD2i YD1t YD1y YD20 YD26 YD2h YD2f YD1s YD1w YD1x YF0m YD28.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2f_fp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the exit's after-loop view (AD1x.v:23-27) ---- *)
Definition IMG_XLF : smem := Eval vm_compute in clipX IMG_LF.
Lemma IMG_XLF_wf : mem_atoms_lt K_M1 IMG_LF = true
/\ IMG_XLF = flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1)) (flat_map (clip_out F_STDERR_LO F_STDERR_HI) IMG_LF)
/\ regions_wf IMG_XLF = true /\ mem_atoms_lt K_M1 IMG_XLF = true /\ length IMG_XLF = 42%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- its data checks (AD28.v:133-142) ---- *)
Lemma IMG_XLF_keep : forallb (drv_keep_ok (-128)) IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XLF_abs : forallb is_abs IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XLF_se : forallb se_ext_ok IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XLF_nocdata : no_cdata IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XLF_atM1 : mem_atoms_lt K_M1 IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XLF_atKJ : mem_atoms_lt KJ IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_XLF_wf' : regions_wf IMG_XLF = true. Proof. vm_compute. reflexivity. Qed.
(* the two exit views the cf exit takes: the donor's IMG_X (exits before target_run's first call, k = 0) and IMG_XLF *)
Definition XIokF (I : smem) : Prop := I = IMG_X \/ I = IMG_XLF.
Lemma XI_checksF : forall I, XIokF I -> forallb (drv_keep_ok (-128)) I = true /\ forallb is_abs I = true /\ forallb se_ext_ok I = true /\ no_cdata I = true
/\ mem_atoms_lt K_M1 I = true /\ mem_atoms_lt KJ I = true /\ regions_wf I = true.
Proof. intros I [-> | ->]; repeat split; vm_compute; reflexivity. Qed.
Lemma jmemI_checksF : forall I spo wf, XIokF I -> (spo = -128 \/ spo = -48) ->
forallb drv_win_ok (jmemI I spo wf) = true /\ forallb se_win_ok (jmemI I spo wf) = true /\ forallb sx_win_ok (jmemI I spo wf) = true /\ regions_wf (jmemI I spo wf) = true
/\ mem_atoms_lt KJ (jmemI I spo wf) = true.
Proof. intros I spo wf [-> | ->] [-> | ->]; destruct wf; vm_compute; repeat split; reflexivity. Qed.

(* ---- IMG_XLF refines IMG_LF (AD28.v:156-185) ---- *)
Definition XL_piecesF : list smem := Eval vm_compute in map (fun r => flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1)) (clip_out F_STDERR_LO F_STDERR_HI r)) IMG_LF.
Lemma XL_piecesF_eq : concat XL_piecesF = IMG_XLF. Proof. vm_compute. reflexivity. Qed.
Lemma XL_piecesF_unfold : XL_piecesF = map (fun r => flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1)) (clip_out F_STDERR_LO F_STDERR_HI r)) IMG_LF.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_LF_lohi : forallb (fun r => r_lo r <=? r_hi r) IMG_LF = true. Proof. vm_compute. reflexivity. Qed.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k YD1u.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma refines_LF_XF : forall E3 (m : word -> option byte), refines E3 m IMG_LF XL_piecesF.
Proof.
intros E3 m. rewrite XL_piecesF_unfold. apply refines_map. intros r Hr.
pose proof (proj1 (forallb_forall _ _) IMG_LF_lohi r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply flat_map_pieces_ok; [| intros q _ Hq; apply clip_out_ok; [unfold A_INITFLAGB, A_INITFLAG; lia | exact Hq]].
apply clip_out_ok; [unfold F_STDERR_LO, F_STDERR_HI; lia | exact Hlh].
Qed.
Lemma mem_ok_XLF_of_LF : forall E (m : word -> option byte), mem_ok tfibsegs E m IMG_LF -> mem_ok tfibsegs E m IMG_XLF.
Proof. intros E m HM. rewrite <- XL_piecesF_eq. apply (mem_ok_refine E m IMG_LF XL_piecesF HM (refines_LF_XF E m)). rewrite XL_piecesF_eq. exact IMG_XLF_wf'. Qed.
End d.

(* ---- the exit state that starts from it (AD28.v:34, 50, 57) ---- *)
Definition jmemLF (spo : Z) (wf : bool) : smem := jmemI IMG_XLF spo wf.
Definition S_JXF : sstate := Eval vm_compute in mkSS 0x8cb34 (jregs (-48)) (jmemLF (-48) false) None noG.
Definition S_JXxF : sstate := Eval vm_compute in run_x S_JXF.
Lemma S_JXF_eq : run_x S_JXF = S_JXxF /\ S_JXF = mkSS 0x8cb34 (jregs (-48)) (jmemI IMG_XLF (-48) false) None noG.
Proof. vm_compute. split; reflexivity. Qed.
Lemma S_JXxF_facts : ss_pc S_JXxF = A_exit /\ sr_get (ss_regs S_JXxF) 3%bv = SLit TFIB_GP /\ sr_get (ss_regs S_JXxF) 4%bv = SLit TFIB_TP /\ ss_resv S_JXxF = None
/\ atom_lookup (f_atoms (ss_facts S_JXxF)) 8%nat = None
/\ sr_get (ss_regs S_JXxF) 10%bv = SOff 206 0 /\ sr_get (ss_regs S_JXxF) 2%bv = SOff 0 (-48) /\ sr_get (ss_regs S_JXxF) 1%bv = SLit 0x8cb38
/\ ss_mem S_JXxF = jmemLF (-48) false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- the exit cells are image cells of the clipped view (YD1j.v:84-89) ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE23 YD1j.
(* every cell of ex_consts (count 2: the driver registered oft_exit_guard) is an image cell of IMG_XLF, and every cell of
   ex_consts1 (count 1: exit before target_run's first call) of IMG_X; so no exit cell is a G_fr_c byte *)
Lemma ex_consts_chkF : ex_chk IMG_XLF ex_consts = true /\ ex_chk IMG_X ex_consts1 = true.
Proof. vm_compute. split; reflexivity. Qed.
Definition XCF (XI : smem) (cells : list (Z * N * Z)) : Prop := (XI = IMG_X /\ cells = ex_consts1) \/ (XI = IMG_XLF /\ cells = ex_consts).
