(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_mul_stmt P_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals A_alloc_lib A_mpi_stmtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_stmtA_sz () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "exp_mod_PHIn"; "Corelib.Init.Logic.and"; "mod_mpi_FRn"; "exp_mod_FRn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "mpd_imgA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "exp_mod_Rsz"; "mpi_binop_stmtA_sz"; "C24_SUB_ABS"; "Corelib.Init.Datatypes.false"; "sub_abs_PHIn"; "sub_abs_FRn"; "sub_abs_Rsz"; "C24_ADDSUB"; "addsub_PHIn"; "addsub_FRn"; "add_abs_Rsz"; "add_mpi_Rsz"; "sub_mpi_Rsz"; "mpi_intop_stmtA_sz"; "C24_INTOP"; "intop_PHIn"; "intop_FRn"; "add_int_Rsz"; "sub_int_Rsz"; "C24_MUL_MPI"; "mul_mpi_PHIn"; "mul_mpi_FRn"; "mul_mpi_Rsz"; "C24_MOD_MPI"; "mod_mpi_PHIn"; "mod_mpi_Rsz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.calls_FR"; "C24_GROW"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_grow.grow_R"].


(* [comment removed for export] *)
Definition arl_need_ecp (R : art_layout) : Z := Z.max (arl_need_rt R) (arl_need_smalloc R).
Lemma arl_need_ecp_rt : forall R, arl_need_rt R <= arl_need_ecp R.
Proof. intros; unfold arl_need_ecp; lia. Qed.
Lemma arl_need_ecp_smalloc : forall R, arl_need_smalloc R <= arl_need_ecp R.
Proof. intros; unfold arl_need_ecp; lia. Qed.

(* [comment removed for export] *)
Definition mpd_imgA (d : mpd) : Prop := md_own d = LStatic -> img_norz (md_p d) (4 * md_n d) = true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sub_abs_nz (nX nA nB : Z) : Z := Z.max nX nA.
Definition addsub_nz (nX nA nB : Z) : Z := Z.max nX (Z.max nA nB + 1).          (* [comment removed for export] *)
Definition intop_nz (nX nA : Z) : Z := Z.max nX (Z.max nA 1 + 1).                (* [comment removed for export] *)
Definition mul_mpi_nz (nX nA nB : Z) : Z := Z.max nX (Z.max (nA + nB) 1).   (* [comment removed for export] *)
Definition mod_mpi_nz (nX nA nB : Z) : Z := Z.max nX (Z.max nA nB + 2).         (* [comment removed for export] *)
Definition exp_mod_nz (nX nA nN : Z) : Z := Z.max (Z.max nX nA) nN + 3.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sub_abs_PHIn (nA : Z) : Z := grow_PHI nA.
Definition addsub_PHIn (nA nB : Z) : Z := grow_PHI nA + 3 * grow_PHI (Z.max nA nB + 2).
Definition intop_PHIn (nA : Z) : Z := grow_PHI nA + 3 * grow_PHI (Z.max nA 1 + 2).
Definition mul_mpi_PHIn (nA nB : Z) : Z := grow_PHI nA + grow_PHI nB + grow_PHI (nA + nB + 1) + 2 * AVOL_CALL.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition mod_mpi_PHIn (nA nB : Z) : Z := 1200136 * nA + 48 * nB + 80088.   (* [comment removed for export] *)
Definition exp_mod_PHIn (nA nE nN : Z) : Z := 1200136 * (nA + 2 * nN + 2) + 96 * grow_PHI (nA + nN + 4).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sub_abs_FRn (d : Z) : Z := calls_FR 2 d.
Definition addsub_FRn (d : Z) : Z := calls_FR 8 d.
Definition intop_FRn (d : Z) : Z := calls_FR 8 (d + 1).
Definition mul_mpi_FRn (d : Z) : Z := calls_FR 5 0 + calls_FR 4 (d + 1).
Definition mod_mpi_FRn (nA nB d : Z) : Z := calls_FR (64 + 24 * nA) (d + 2).        (* [comment removed for export] *)
Definition exp_mod_FRn (nA nE nN d : Z) : Z := calls_FR (256 + 24 * (nA + 2 * Z.max 0 nN)) (d + 31).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition C24_SUB_ABS : Z := 2.
Definition C24_ADDSUB : Z := 4.
Definition C24_INTOP : Z := 8.
Definition C24_MUL_MPI : Z := 8.
Definition C24_MOD_MPI : Z := 16.
Definition C24_EXP_MOD : Z := 32.   (* [comment removed for export] *)

Lemma grow_PHI_mono : forall a b, a <= b -> grow_PHI a <= grow_PHI b.
Proof. intros; unfold grow_PHI; lia. Qed.
Lemma grow_PHI_nonneg : forall a, 0 <= a -> 0 <= grow_PHI a.
Proof. intros; unfold grow_PHI, AVOL_CALL; lia. Qed.
Lemma addsub_PHIn_mono : forall a b a' b', a <= a' -> b <= b' -> addsub_PHIn a b <= addsub_PHIn a' b'.
Proof. intros; unfold addsub_PHIn, grow_PHI; lia. Qed.
Lemma intop_PHIn_mono : forall a a', a <= a' -> intop_PHIn a <= intop_PHIn a'.
Proof. intros; unfold intop_PHIn, grow_PHI; lia. Qed.
Lemma mul_mpi_PHIn_mono : forall a b a' b', a <= a' -> b <= b' -> mul_mpi_PHIn a b <= mul_mpi_PHIn a' b'.
Proof. intros; unfold mul_mpi_PHIn, grow_PHI; lia. Qed.
Lemma mod_mpi_PHIn_mono : forall a b a' b', a <= a' -> b <= b' -> mod_mpi_PHIn a b <= mod_mpi_PHIn a' b'.
Proof. intros; unfold mod_mpi_PHIn, grow_PHI; lia. Qed.
Lemma exp_mod_PHIn_mono : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Pa,$0.Pe,$0.Pn,$0.Pa',$0.Pe',$0.Pn',$0.P,(1.R6.R3.)P,(1.R6.R3.)P,(1.R6.R3.)(1.(2.R9.R8.R7.)(2.R6.R5.R4.))")
(* [comment removed for export] *).
Proof. intros; unfold exp_mod_PHIn, grow_PHI; lia. Qed.
Lemma mod_mpi_FRn_mono : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Pa,$0.Pb,$0.Pd,$0.Pa',$0.Pb',$0.Pd',$0.P,(3.(1.=R6.)(1.R6.R3.))P,(1.R6.R3.)P,(3.(1.=R6.)(1.R6.R3.))(1.(4.R9.R8.R7.)(4.R6.R5.R4.))")
(* [comment removed for export] *).
Proof. intros; unfold mod_mpi_FRn, calls_FR, fr_charge; nia. Qed.
Lemma mod_mpi_FRn_nonneg : forall a b d, 0 <= a -> 0 <= d -> 0 <= mod_mpi_FRn a b d.
Proof. intros; unfold mod_mpi_FRn, calls_FR, fr_charge; nia. Qed.
Lemma exp_mod_FRn_mono : ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Pa,$0.Pe,$0.Pn,$0.Pd,$0.Pa',$0.Pe',$0.Pn',$0.Pd',$0.P,(3.(1.=R8.)(1.R8.R4.))P,(1.R8.R4.)P,(1.R8.R4.)P,(3.(1.=R8.)(1.R8.R4.))(1.(5.R<.R;.R:.R9.)(5.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros a e n d a' e' n' d' Ha He Hn Hd. unfold exp_mod_FRn, calls_FR, fr_charge.
  assert (M : 0 <= Z.max 0 n <= Z.max 0 n') by lia. set (x := Z.max 0 n) in *. set (x' := Z.max 0 n') in *. nia.
Qed.
Lemma exp_mod_FRn_nonneg : forall a e n d, 0 <= a -> 0 <= d -> 0 <= exp_mod_FRn a e n d.
Proof.
  intros a e n d Ha Hd. unfold exp_mod_FRn, calls_FR, fr_charge.
  assert (M : 0 <= Z.max 0 n) by lia. set (x := Z.max 0 n) in *. nia.
Qed.
Lemma mod_mpi_PHIn_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= mod_mpi_PHIn a b.
Proof. intros; unfold mod_mpi_PHIn, grow_PHI, AVOL_CALL; lia. Qed.
Lemma exp_mod_PHIn_nonneg : forall a e n, 0 <= a -> 0 <= n -> 0 <= exp_mod_PHIn a e n.
Proof. intros; unfold exp_mod_PHIn, grow_PHI, AVOL_CALL; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sub_abs_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  sub_abs_R LB dX dA dB r dX' /\ md_n dX' <= sub_abs_nz (md_n dX) (md_n dA) (md_n dB).
Definition add_abs_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  add_abs_R LB dX dA dB r dX' /\ md_n dX' <= addsub_nz (md_n dX) (md_n dA) (md_n dB).
Definition add_mpi_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  add_mpi_R LB dX dA dB r dX' /\ md_n dX' <= addsub_nz (md_n dX) (md_n dA) (md_n dB).
Definition sub_mpi_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  sub_mpi_R LB dX dA dB r dX' /\ md_n dX' <= addsub_nz (md_n dX) (md_n dA) (md_n dB).
Definition add_int_Rsz (LB : list blk) (dX dA : mpd) (b r : Z) (dX' : mpd) : Prop :=
  add_int_R LB dX dA b r dX' /\ md_n dX' <= intop_nz (md_n dX) (md_n dA).
Definition sub_int_Rsz (LB : list blk) (dX dA : mpd) (b r : Z) (dX' : mpd) : Prop :=
  sub_int_R LB dX dA b r dX' /\ md_n dX' <= intop_nz (md_n dX) (md_n dA).
Definition mul_mpi_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  mul_mpi_R LB dX dA dB r dX' /\ md_n dX' <= mul_mpi_nz (md_n dX) (md_n dA) (md_n dB).
Definition mod_mpi_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  mod_mpi_R LB dX dA dB r dX' /\ md_n dX' <= mod_mpi_nz (md_n dX) (md_n dA) (md_n dB).
Definition exp_mod_Rsz (LB : list blk) (dX dA dE dN : mpd) (r : Z) (dX' : mpd) : Prop :=
  exp_mod_R LB dX dA dE dN r dX' /\ md_n dX' <= exp_mod_nz (md_n dX) (md_n dA) (md_n dN).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mpi_binop_stmtA_sz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z) (NF : nat) (C24 : Z)
    (NB SS : bool) (PHI : mpd -> mpd -> mpd -> Z) (FRC : mpd -> mpd -> mpd -> Z -> Z)
    (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Ph,(6.O<.O;.O:.)PLB,(7.$8.)PLF,(7.$8.)Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(:.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(;.(9.&8.))Pmo,$<.PdX,$=.PdA,$=.PdB,$=.Plo,$0.Pd,$0.Pslo,$0.P,(>.O<.O;.O:.R2<.R2;.R2:.R8.)P,(?.O<.O;.O:.R2=.R8.)P,(10.(11.(12.$8.R2<.)O7.)#200.)P,(13.O<.R;.R2>.R9.)P,(13.O<.R<.R2?.R9.)P,(13.O<.R=.R30.R9.)P,(14.R<.R;.)P,(14.R=.R;.)P,(14.R=.R<.)P,(15.(16.$17.(18.R?.)$19.))P,P,(16.$1:.O5.$1;.)(15.(16.$0.(1<.R11.)(1<.R?.)))P,(1=.R11.R10.R>.(1>.&40.R33.))P,(1=.R12.R10.R?.(1>.&40.R34.))P,(1?.(20.O;.)(21.$8.R38.(22.R37.))R10.(1<.R12.)+10.)P,P,(16.$17.(18.R13.)$23.)(1?.(20.O;.)(21.$8.R3:.(22.R39.))R12.(24.R14.)(25.+4.(26.R14.)))P,(1?.(20.O;.)(21.$8.R3:.(22.R39.))R12.(1<.R13.)+10.)P,P,(16.$17.(18.R14.)$23.)(1?.(20.O;.)(21.$8.R3<.(22.R3;.))R14.(24.R15.)(25.+4.(26.R15.)))P,(27.O;.R3<.R3;.(1>.&40.R39.)(28.O<.O;.O:.R3=.)R17.)P,P,(15.(16.$17.(18.R18.)$29.))(2:.(1.(2;.(24.R19.)(25.+4.(26.R19.)))R16.)(1.(1>.&40.R3;.)(24.R19.)))P,(2<.O<.R1;.R16.(1>.&40.R3;.))P,(1.(2=.O;.)R17.)P,(1.R18.(2>.(2>.(1>.&40.R3=.)O8.)(2?.O;.)))P,P,(16.$1:.O4.$1;.)(3.(30.O<.(31.O;.)R1?.R18.(1>.&40.R3?.))(3.(1.(2=.O;.)R18.)(1.R18.R1:.)))P,(1.(1>.&40.R3?.)(28.O<.O;.O:.R43.))P,(16.$0.(32.(1>.&40.R40.)+10.)=)P,(16.(9.&40.)R3?.(33.&40.(34.O;.)))P,(35.O<.R22.)P,(16.$0.(32.(1>.&40.R44.)+2.)=)P,(36.O<.(31.O;.)(37.O<.O;.O:.R48.)R24.R22.)P,(36.O<.(31.O;.)(37.O<.O;.O:.R49.)R25.R22.)P,(36.O<.(31.O;.)(37.O<.O;.O:.R4:.)R26.R22.)P,(38.R24.)P,(38.R24.)P,(1.(2;.(39.O<.O;.O:.R4=.)A3.O3.R27.R26.R25.)$3:.)P,(3;.O<.R2:.(2=.O;.)(3<.O<.O;.O:.R4>.)(1>.&40.R44.)(1>.&40.R4:.)R24.)P,(3=.O;.(1<.R29.)+10.R25.)P,(3=.O;.(1<.R29.)+10.R26.)P,(3=.O;.(1<.R29.)+10.R27.)P,(1.(2;.(3>.O<.O;.O:.R52.)A4.O2.R2<.R2;.R2:.R28.)$3?.)P,(1.(2;.(40.R52.)O6.)$41.)P,(16.(9.&40.)R48.(33.&40.(1<.R2>.)))P,(16.(9.&40.)R48.(33.&40.(1<.R2>.)))P,(16.(9.&40.)R48.(33.&40.(1<.R2>.)))(42.O<.(43.O<.O;.O:.R54.R53.R52.R51.R4=.R4<.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R35.R34.R57.R56.R55.R31.A4.O1.R56.R31.R30.R2?.A3.O3.R31.R30.R2?.A4.O2.R31.R30.R2?.R2=.R2>.R33.R32.)(44.(45.(46.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.)R35.(33.&40.O9.)R34.(47.(9.&40.))R33.(48.O<.))R32.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_intop_stmtA_sz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z) (NF : nat) (C24 : Z)
    (PHI : mpd -> mpd -> Z) (FRC : Z -> Z)
    (Rr : list blk -> mpd -> mpd -> Z -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Ph,(6.O:.O9.O8.)PLB,(7.$8.)PLF,(7.$8.)Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(:.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(;.(9.&8.))Pmo,$<.PdX,$=.PdA,$=.Pb,$0.Plo,$0.Pd,$0.P,(>.O:.O9.O8.R2;.R2:.R29.R7.)P,(?.O:.O9.O8.R2<.R7.)P,(10.(11.(12.$8.R2;.)O5.)#200.)P,(13.O:.R:.R2=.R8.)P,(13.O:.R;.R2>.R8.)P,(14.R:.R9.)P,(15.(16.$17.(18.R;.)$19.))P,(1=.R<.R;.R9.(1>.&40.R2>.))P,(1?.(20.O9.)(21.$8.R32.(22.R31.))R:.(1<.R<.)+10.)P,P,(16.$17.(18.R=.)$23.)(1?.(20.O9.)(21.$8.R34.(22.R33.))R<.(24.R>.)(25.+4.(26.R>.)))P,(27.O9.R34.R33.(1>.&40.R31.)(28.O:.O9.O8.R35.)R?.)P,(3.(1.(49.(4:.+2.+1?.))R>.)(4;.R>.(4:.+2.+1?.)))P,P,(15.(16.$17.(18.R11.)$29.))(2:.(1.(2;.(24.R12.)(25.+4.(26.R12.)))R?.)(1.(1>.&40.R34.)(24.R12.)))P,(2<.O:.R14.R?.(1>.&40.R34.))P,(1.(2=.O9.)R10.)P,(1.R11.(2>.(2>.(1>.&40.R36.)O6.)(2?.O9.)))P,(1.(1>.&40.R37.)(28.O:.O9.O8.R3;.))P,(16.$0.(32.(1>.&40.R38.)+10.)=)P,(16.(9.&40.)R37.(33.&40.(34.O9.)))P,(35.O:.R1:.)P,(16.$0.(32.(1>.&40.R3<.)+2.)=)P,(36.O:.(31.O9.)(37.O:.O9.O8.R40.)R1<.R1:.)P,(36.O:.(31.O9.)(37.O:.O9.O8.R41.)R1=.R1:.)P,(38.R1;.)P,(1.(2;.(39.O:.O9.O8.R43.)A2.O3.R1=.R1<.)$3:.)P,(3;.O:.R20.(2=.O9.)(3<.O:.O9.O8.R44.)(1>.&40.R3:.)(1>.&40.R40.)R1:.)P,(3=.O9.(1<.R1?.)+10.R1;.)P,(3=.O9.(1<.R1?.)+10.R1<.)P,(1.(2;.(3>.O:.O9.O8.R47.)A1.O2.R1=.)$3?.)P,(1.(2;.(40.R47.)O4.)$41.)P,(16.(9.&40.)R3=.(33.&40.(1<.R23.)))P,(16.(9.&40.)R3=.(33.&40.(1<.R23.)))P,(16.(9.&40.)R3=.(33.&40.R23.))(42.O:.(43.O:.O9.O8.R49.R48.R47.R46.R42.R41.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2:.R29.R4<.R4;.R4:.R26.A4.O1.R4;.R26.R25.R24.A2.O3.R26.R25.A1.O2.R22.R23.R28.R27.)(44.(45.(46.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.)R2:.(33.&40.O7.)R29.(47.(9.&40.))R28.(48.O:.))R27.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_exp_mod_stmtA_sz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z) (NF : nat) (C24 : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Ph,(6.O7.O6.O5.)PLB,(7.$8.)PLF,(7.$8.)Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(:.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(;.(9.&8.))Pmo,$<.PdX,$=.PdA,$=.PdE,$=.PdN,$=.Plo,$0.Pd,$0.Pslo,$0.P,(>.O7.O6.O5.R2=.R2<.R2;.R9.)P,(?.O7.O6.O5.R2>.R9.)P,(10.(11.(12.$8.R2=.)O2.)#200.)P,(13.O7.R<.R2?.R:.)P,(13.O7.R=.R30.R:.)P,(13.O7.R>.R31.R:.)P,(13.O7.R?.R32.R:.)P,(1.(26.R;.)+1387.)P,(1.(26.R?.)(26.R>.))P,(14.R10.R?.)P,(14.R11.R?.)P,(14.R12.R?.)P,(15.(16.$0.(1<.R13.)(1<.R11.)))P,(15.(16.$0.(1<.R14.)(1<.R11.)))P,(15.(16.$17.(18.R15.)$19.))P,(1=.R16.R15.R12.(1>.&40.R38.))P,(1=.R17.R15.R13.(1>.&40.R39.))P,(1=.R18.R15.R14.(1>.&40.R3:.))P,(1?.(20.O6.)(21.$8.R3>.(22.R3=.))R15.(1<.R18.)+10.)P,P,(16.$17.(18.R19.)$23.)(1?.(20.O6.)(21.$8.R40.(22.R3?.))R17.(24.R1:.)(25.+4.(26.R1:.)))P,(1?.(20.O6.)(21.$8.R40.(22.R3?.))R17.(1<.R19.)+10.)P,P,(16.$17.(18.R1:.)$23.)(1?.(20.O6.)(21.$8.R42.(22.R41.))R19.(24.R1;.)(25.+4.(26.R1;.)))P,(1?.(20.O6.)(21.$8.R42.(22.R41.))R19.(1<.R1:.)+10.)P,P,(16.$17.(18.R1;.)$23.)(1?.(20.O6.)(21.$8.R44.(22.R43.))R1;.(24.R1<.)(25.+4.(26.R1<.)))P,(27.O6.R44.R43.(1>.&40.R41.)(28.O7.O6.O5.R45.)R1?.)P,P,(15.(16.$17.(18.R20.)$29.))(2:.(1.(2;.(24.R21.)(25.+4.(26.R21.)))R1=.)(1.(1>.&40.R43.)(24.R21.)))P,(2<.O7.R23.R1=.(1>.&40.R43.))P,(1.(2=.O6.)R1>.)P,(1.R1?.(2>.(2>.(1>.&40.R45.)O3.)(2?.O6.)))P,(30.O7.(31.O6.)R26.R1>.(1>.&40.R46.))P,(1.(2=.O6.)R1?.)P,(1.R20.R22.)P,(1.(1>.&40.R49.)(28.O7.O6.O5.R4=.))P,(16.$0.(32.(1>.&40.R4:.)+10.)=)P,(16.(9.&40.)R49.(33.&40.(34.O6.)))P,(35.O7.R2<.)P,(16.$0.(32.(1>.&40.R4>.)+2.)=)P,(36.O7.(31.O6.)(37.O7.O6.O5.R52.)R2>.R2<.)P,(36.O7.(31.O6.)(37.O7.O6.O5.R53.)R2?.R2<.)P,(36.O7.(31.O6.)(37.O7.O6.O5.R54.)R30.R2<.)P,(36.O7.(31.O6.)(37.O7.O6.O5.R55.)R31.R2<.)P,(38.R2?.)P,(38.R2?.)P,(38.R2?.)P,(1.(2;.(39.O7.O6.O5.R59.)(2.(26.R32.)(26.R31.)(26.R30.)))$3:.)P,(3;.O7.R36.(2=.O6.)(3<.O7.O6.O5.R5:.)(1>.&40.R50.)(1>.&40.R56.)R2?.)P,(3=.O6.(1<.R35.)+10.R30.)P,(3=.O6.(1<.R35.)+10.R31.)P,(3=.O6.(1<.R35.)+10.R32.)P,(3=.O6.(1<.R35.)+10.R33.)P,(1.(2;.(3>.O7.O6.O5.R5?.)(5.(26.R38.)(26.R37.)(26.R36.)R34.))$3?.)P,(1.(2;.(40.R5?.)O1.)$41.)P,(16.(9.&40.)R55.(33.&40.(1<.R3;.)))P,(16.(9.&40.)R55.(33.&40.(1<.R3;.)))P,(16.(9.&40.)R55.(33.&40.(1<.R3;.)))P,(16.(9.&40.)R55.(33.&40.(1<.R3;.)))P,(16.(9.&40.)R55.(33.&40.=))(42.O7.(43.O7.O6.O5.R63.R62.R61.R60.R5<.R5;.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R44.R43.R66.R65.R64.R40.(4<.R65.R40.R3?.R3>.R3=.)(2.(26.R3?.)(26.R3>.)(26.R3=.))(5.(26.R3?.)(26.R3>.)(26.R3=.)R3;.)R3<.R42.R41.)(44.(45.(46.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.)R44.(33.&40.O4.)R43.(47.(9.&40.))R42.(48.O7.))R41.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mpi_sub_abs_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(4=.O4.O3.O2.O1.+>0.#0.$4>.$4?.$4?.LdX,$=.LdA,$=.LdB,$=.(50.(26.R2.))L,$=.L,$=.L,$=.Ld,$0.(51.R1.)$52.)")
(* [comment removed for export] *).
Definition mpi_add_abs_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(4=.O4.O3.O2.O1.+130.#0.$53.$4?.$4?.LdX,$=.LdA,$=.LdB,$=.(54.(26.R2.)(26.R1.))L,$=.L,$=.L,$=.Ld,$0.(55.R1.)$56.)")
(* [comment removed for export] *).
Definition mpi_add_mpi_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(4=.O4.O3.O2.O1.+170.#0.$53.$4?.$4?.LdX,$=.LdA,$=.LdB,$=.(54.(26.R2.)(26.R1.))L,$=.L,$=.L,$=.Ld,$0.(55.R1.)$57.)")
(* [comment removed for export] *).
Definition mpi_sub_mpi_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(4=.O4.O3.O2.O1.+170.#0.$53.$4?.$4?.LdX,$=.LdA,$=.LdB,$=.(54.(26.R2.)(26.R1.))L,$=.L,$=.L,$=.Ld,$0.(55.R1.)$58.)")
(* [comment removed for export] *).
Definition mpi_add_int_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(59.O4.O3.O2.O1.+1?0.#1.$5:.LdX,$=.LdA,$=.(5;.(26.R1.))$5<.$5=.)")
(* [comment removed for export] *).
Definition mpi_sub_int_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(59.O4.O3.O2.O1.+1?0.#1.$5:.LdX,$=.LdA,$=.(5;.(26.R1.))$5<.$5>.)")
(* [comment removed for export] *).
Definition mpi_mul_mpi_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(4=.O4.O3.O2.O1.+210.#1.$5?.$4?.$4?.LdX,$=.LdA,$=.LdB,$=.(60.(26.R2.)(26.R1.))L,$=.L,$=.L,$=.Ld,$0.(61.R1.)$62.)")
(* [comment removed for export] *).
Definition mpi_mod_mpi_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "(4=.O4.O3.O2.O1.+360.#2.$63.$1;.$1;.LdX,$=.LdA,$=.LdB,$=.(64.(26.R2.)(26.R1.))LdX,$=.LdA,$=.LdB,$=.Ld,$0.(4.(26.R3.)(26.R2.)R1.)$65.)")
(* [comment removed for export] *).
Definition mpi_exp_mod_stmtA_szT segs R HIA ENTRY :=
  mpi_exp_mod_stmtA_sz segs R HIA ENTRY MPI_EXP_MOD_STACK_A 3 C24_EXP_MOD.

(* [comment removed for export] *)
Definition C24_GROW : Z := 2.
Definition mpi_grow_stmtA_sz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_sz ()) "Ph,(6.O4.O3.O2.)PLB,(7.$8.)PLF,(7.$8.)Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(:.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(;.(9.&8.))Pmo,$<.PdX,$=.Pv,$0.Plo,$0.Pd,$0.P,(>.O4.O3.O2.R2:.R29.R28.R6.)P,(?.O4.O3.O2.R2;.R6.)P,(13.O4.R8.R2;.R6.)P,(15.(16.$17.(18.R7.)$19.))P,(3.(1.=R7.)(4;.R7.(4:.+2.+40.)))P,(27.O3.R2>.R2=.(1>.&40.R2;.)(28.O4.O3.O2.R2?.)R9.)P,P,(15.(16.$17.(18.R:.)$29.))(2:.(1.(2;.(24.R;.)(25.+4.(26.R;.)))R9.)(1.(1>.&40.R2=.)(24.R;.)))P,(2<.O4.R=.R9.(1>.&40.R2=.))P,(1.(2=.O3.)R:.)P,(1.R;.(2>.(2>.(1>.&40.R2?.)+60.)(66.O3.)))P,(1.(1>.&40.R30.)(28.O4.O3.O2.R34.))P,(16.$0.(32.(1>.&40.R31.)+10.)=)P,(16.(9.&40.)R30.(33.&40.(34.O3.)))P,(35.O4.R13.)P,(16.$0.(32.(1>.&40.R35.)+2.)=)P,(36.O4.(31.O3.)(37.O4.O3.O2.R39.)R15.R13.)P,(1.(2;.(39.O4.O3.O2.R3:.)(67.R13.))$3:.)P,(3;.O4.R17.(2=.O3.)(3<.O4.O3.O2.R3;.)(1>.&40.R31.)(1>.&40.R37.)R12.)P,(3=.O3.(1<.R16.)+10.R13.)P,(1.(2;.(3>.O4.O3.O2.R3=.)(68.+2.R14.))$3?.)P,(1.(2;.(40.R3=.)$69.)$41.)P,(16.(9.&40.)R33.(33.&40.(1<.R19.)))P,(16.(9.&40.)R33.(33.&40.R19.))(42.O4.(43.O4.O3.O2.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R41.R40.R3?.R1;.(6:.R1:.R1;.R40.)(67.R1:.)(68.+2.R18.)R19.R1=.R1<.)(44.(45.(46.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(33.&40.O1.)R1>.(47.(9.&40.))R1=.(48.O4.))R1<.))")
(* [comment removed for export] *).
