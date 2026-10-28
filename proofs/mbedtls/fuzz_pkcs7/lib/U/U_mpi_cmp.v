(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_cmp () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_cmp_post"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "SIGF"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"].


Definition U_MPI_CMP_MPI : Z := 0x202a4.
Definition U_MPI_CMP_INT : Z := 0x2044c.

(* [comment removed for export] *)
Notation MPI_CMP_STACK := 32 (only parsing).

(* [comment removed for export] *)
Definition mpi_cmp_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(3.(4.$0.R?.(5.(6.O14.O13.O12.O11.R>.R=.R<.O10.O?.(7.&40.O2.)R;.R:.R9.R8.R7.R6.R5.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R4.R3.R2.R1.)O4.(8.O14.)O3.(9.(2.&40.))O1.(:.O15.)))(3.(;.(<.$=.)O1.O1.)(3.(>.O15.O1.O1.)(?.O15.O1.))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_cmp_int_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(10.(2.&8.))Lm',P,(2.&40.)(10.(2.&8.))(3.(4.$0.R10.(5.(6.O15.O14.O13.O12.R?.R>.R=.O11.O10.(7.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(8.O15.)O4.(9.(2.&40.))R1.(:.O16.)))(3.(;.(11.(12.$13.$13.)(14.$13.$13.(15.(16.&40.O14.)+20.)(16.&40.O14.))(<.(12.$13.$13.)))O1.R1.)(3.(>.O16.O1.R1.)(3.(?.O16.R1.)(17.O16.R1.O2.(16.&40.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_cmp_abs_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(10.(2.&8.))PLB,(19.$1:.)PdX,$1;.PdY,$1;.P,(1<.O2.R4.R3.R2.)P,(1<.O2.R5.R4.R2.)P,P,(4.$1=.(1>.R4.)$1?.)(20.=(21.R5.))P,P,(4.$1=.(1>.R4.)$1?.)(20.=(21.R5.))P,(?.O2.R8.)P,(4.(2.&40.)R21.(7.&40.(22.R7.)))P,(4.(2.&40.)R21.(7.&40.(22.R7.)))(23.O2.(24.O2.R2<.R2;.R2:.R29.R25.R24.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R=.R<.(25.(15.(26.R9.)(26.R8.)))R;.)(5.(6.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(7.&40.O1.)R<.(9.(2.&40.))R;.(:.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_cmp_mpi_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(10.(2.&8.))PLB,(19.$1:.)PdX,$1;.PdY,$1;.P,(1<.O2.R4.R3.R2.)P,(1<.O2.R5.R4.R2.)P,P,(4.$1=.(1>.R4.)$1?.)(20.=(21.R5.))P,P,(4.$1=.(1>.R4.)$1?.)(20.=(21.R5.))P,(?.O2.R8.)P,(4.(2.&40.)R21.(7.&40.(22.R7.)))P,(4.(2.&40.)R21.(7.&40.(22.R7.)))(23.O2.(24.O2.R2<.R2;.R2:.R29.R25.R24.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R=.R<.(25.(15.(27.R9.)(27.R8.)))R;.)(5.(6.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(7.&40.O1.)R<.(9.(2.&40.))R;.(:.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_cmp_int_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (dX : mpd) (z lo : Z),
  mpd_at segs m LB dX -> (md_own dX = LHeap -> 0 < md_p dX) -> -2^31 <= z < 2^31 ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - MPI_CMP_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  (md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX) ->
  (md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 (md_addr dX) -> a1 = Z_to_bv 64 z ->
  evt segs (mpi_cmp_int_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.sgn (mpd_val dX - z)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Definition mpi_cmp_mpi_stmt_o (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (dX dY : mpd),
  opnd_at segs m LB (bv_unsigned sp) dX -> opnd_at segs m LB (bv_unsigned sp) dY ->
  (md_own dX = LHeap -> 0 < md_p dX) -> (md_own dY = LHeap -> 0 < md_p dY) -> mem_inv segs m ->
  a0 = Z_to_bv 64 (md_addr dX) -> a1 = Z_to_bv 64 (md_addr dY) ->
  evt segs (mpi_cmp_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.sgn (mpd_val dX - mpd_val dY)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Definition mpi_cmp_abs_stmt_o (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (dX dY : mpd),
  opnd_at segs m LB (bv_unsigned sp) dX -> opnd_at segs m LB (bv_unsigned sp) dY ->
  (md_own dX = LHeap -> 0 < md_p dX) -> (md_own dY = LHeap -> 0 < md_p dY) -> mem_inv segs m ->
  a0 = Z_to_bv 64 (md_addr dX) -> a1 = Z_to_bv 64 (md_addr dY) ->
  evt segs (mpi_cmp_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.sgn (mpd_abs dX - mpd_abs dY)) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38557618280.2L42111638888.200000600<S1z2HzS1z2Hz". (* [comment removed for export] *)
Lemma zx16_small : forall z, 0 <= z < 2^16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L11550708067.3L11607912823.3L15894245495.3L18337568290.3L25162877559.3L3768665582.3 L38559713562.3L4114035564.3 L7327412462.3 00000300400700:00;00A00I00L00TS1zSS1zS1zSS1z2HzS1z2Hz1HS1zS1z2Hz1H". (* [comment removed for export] *)
Lemma sx16_small : forall z, -2^15 <= z < 2^15 -> sx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx16. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with (2^64). change (bv_modulus 16) with (2^16). change (bv_half_modulus 16) with (2^15).
  destruct (Z.lt_ge_cases z 0).
  - replace (z mod 2^64) with (z + 2^64) by (rewrite <- (Z.mod_small (z + 2^64) (2^64)) by lia; replace (z + 2^64) with (z + 1 * 2^64) by lia; rewrite Z.mod_add by lia; reflexivity).
    replace (z + 2^64 + 2^15) with ((z + 2^15) + (2^48) * 2^16) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace (z + 2 ^ 15 - 2 ^ 15) with z by lia. reflexivity.
  - rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L3134031665.3 L41422282358.3000007008S1a1b1HS". (* [comment removed for export] *)
Lemma pow32_le : forall a b, 0 <= a <= b -> 2 ^ (32 * a) <= 2 ^ (32 * b).
Proof. intros a b H. apply Z.pow_le_mono_r; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L41422282358.2L9308211436.2 000001006SS1a1H". (* [comment removed for export] *)
Lemma pow32_pos : forall a, 0 <= a -> 0 < 2 ^ (32 * a).
Proof. intros a H. apply Z.pow_pos_nonneg; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L2316405997.4 L42610269850.4L54425656421.400000600900?S2ws1rS1rS1r2Hr". (* [comment removed for export] *)
Lemma lval_drop_zero : forall ws r, 1 <= r -> limb32 ws (Z.to_nat (r - 1)) = 0 -> lval ws r = lval ws (r - 1).
Proof.
  intros ws r Hr Hz. replace r with ((r - 1) + 1) at 1 by lia. rewrite lval_succ by lia. rewrite Hz. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L42610269850.4L54425656421.4L54425663791.6L54431941911.500000300900?00ES1rS1r2HrS1r2HrS1r2Hr". (* [comment removed for export] *)
Lemma lval_top_nonzero : forall ws r, 1 <= r -> limb32 ws (Z.to_nat (r - 1)) <> 0 -> 2 ^ (32 * (r - 1)) <= lval ws r.
Proof.
  intros ws r Hr Hz. replace r with ((r - 1) + 1) at 2 by lia. rewrite lval_succ by lia.
  pose proof (limb32_range ws (Z.to_nat (r - 1))). pose proof (lval_range ws (r - 1) ltac:(lia)).
  pose proof (pow32_pos (r - 1) ltac:(lia)). nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SIGF (ws : list word) (n i : Z) : Prop :=
  0 <= i <= n /\ lval ws n = lval ws i /\ (i = 0 \/ 2 ^ (32 * (i - 1)) <= lval ws i).


Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L20668371764.14L45270656544.13L688643585.15  L8212521524.11 00000?00J00g01:S1i2n'1j2Y13HltS1i2n'1j2Y1S2xs1i2ys2n'1j2X32Y13Hlt2RY1HS2xs2ys2n'1j2Y13Hlt". (* [comment removed for export] *)
Lemma SIGF_lt : forall xs n i ys n' j, SIGF xs n i -> SIGF ys n' j -> j < i -> lval ys n' < lval xs n.
Proof.
  (intros xs n i ys n' j dd_H; ddestruct dd_H as (X1 & X2 & X3); intros dd_H; ddestruct dd_H as (Y1 & Y2 & Y3); intros Hlt). rewrite X2, Y2.
  destruct X3 as [->|X3]; [lia|].
  pose proof (lval_range ys j ltac:(lia)) as [_ RY]. pose proof (pow32_le j (i - 1) ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L20410898086.3L41791802756.3L56682468906.3L66508898836.300000700>00E00LS1a1b1HS1a1b1HS1a1b1HS1a1b1H". (* [comment removed for export] *)
Lemma sgn_of_lt : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Psx,$13.Psy,$13.Pa,$13.Pb,$13.P,(28.(4.$13.R4.+1.)(4.$13.R4.-1.))P,(28.(4.$13.R4.+1.)(4.$13.R4.-1.))P,(3.(29.=R3.)(20.R3.R4.))(4.$13.(25.(15.(2:.R7.R5.)(2:.R6.R4.)))R7.)")
(* [comment removed for export] *).
Proof. intros sx sy a b [->| ->] [->| ->] H; first [apply Z.sgn_pos; lia | apply Z.sgn_neg; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L20410898086.3L55147004676.3L55367886264.3L56682468906.300000700>00E00LS1a1b1HS1a1b1HS1a1b1HS1a1b1H". (* [comment removed for export] *)
Lemma sgn_of_gt : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Psx,$13.Psy,$13.Pa,$13.Pb,$13.P,(28.(4.$13.R4.+1.)(4.$13.R4.-1.))P,(28.(4.$13.R4.+1.)(4.$13.R4.-1.))P,(3.(29.=R4.)(20.R4.R3.))(4.$13.(25.(15.(2:.R7.R5.)(2:.R6.R4.)))(2;.R6.))")
(* [comment removed for export] *).
Proof. intros sx sy a b [->| ->] [->| ->] H; first [apply Z.sgn_pos; lia | apply Z.sgn_neg; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L3629681391.2 L46854123637.2L56111440432.200000500:00?S1a1bS1a1bS1a1b". (* [comment removed for export] *)
Lemma sgn_same_sign : forall (s a b : Z), (s = 1 \/ s = -1) -> Z.sgn (s * a - s * b) = s * Z.sgn (a - b).
Proof.
  intros s a b [->| ->]; [rewrite Z.mul_1_l; f_equal; lia|].
  replace (-1 * a - -1 * b) with (- (a - b)) by lia. rewrite Z.sgn_opp. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L13675760733.5L42608246887.5L54432023192.500000900<00BS2xs2ys1rS1rS1r2Hr". (* [comment removed for export] *)
Lemma cmp_step_eq : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pxs,(19.(2.&40.))Pys,(19.(2.&40.))Pr,$13.P,(29.+1.R1.)P,(4.$13.(2<.R4.(2=.(15.R2.+1.)))(2<.R3.(2=.(15.R2.+1.))))(4.$13.(25.(15.(2>.R5.R3.)(2>.R4.R3.)))(25.(15.(2>.R5.(15.R3.+1.))(2>.R4.(15.R3.+1.)))))")
(* [comment removed for export] *).
Proof.
  intros xs ys r Hr E. replace r with ((r - 1) + 1) at 1 2 by lia. rewrite !lval_succ by lia. rewrite E. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L42608246887.5L49728440834.5L54425663791.7L54431941911.6L54432023192.500000300600<00B00HS1rS1rS1r2HrS1r2HrS1r2Hr". (* [comment removed for export] *)
Lemma cmp_step_gt : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pxs,(19.(2.&40.))Pys,(19.(2.&40.))Pr,$13.P,(29.+1.R1.)P,(20.(2<.R3.(2=.(15.R2.+1.)))(2<.R4.(2=.(15.R2.+1.))))(4.$13.(25.(15.(2>.R5.R3.)(2>.R4.R3.)))+1.)")
(* [comment removed for export] *).
Proof.
  intros xs ys r Hr E. replace r with ((r - 1) + 1) by lia. rewrite !lval_succ by lia.
  replace (r - 1 + 1 - 1) with (r - 1) in E by lia.
  pose proof (lval_range xs (r - 1) ltac:(lia)). pose proof (lval_range ys (r - 1) ltac:(lia)). pose proof (pow32_pos (r - 1) ltac:(lia)).
  apply Z.sgn_pos. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L23392681281.6000009S2xs2ys1r". (* [comment removed for export] *)
Lemma cmp_step_lt : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pxs,(19.(2.&40.))Pys,(19.(2.&40.))Pr,$13.P,(29.+1.R1.)P,(20.(2<.R4.(2=.(15.R2.+1.)))(2<.R3.(2=.(15.R2.+1.))))(4.$13.(25.(15.(2>.R5.R3.)(2>.R4.R3.)))-1.)")
(* [comment removed for export] *).
Proof.
  intros xs ys r Hr E. pose proof (cmp_step_gt ys xs r Hr E) as G.
  replace (lval xs r - lval ys r) with (- (lval ys r - lval xs r)) by lia. rewrite Z.sgn_opp, G. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L27966550640.4L36557432084.400000600<S1u2HuS1v2Hv". (* [comment removed for export] *)
Lemma sxz_lt_iff : forall u v, 0 <= u < 2^32 -> 0 <= v < 2^32 -> (sxz u < sxz v <-> u < v).
Proof. intros u v Hu Hv. rewrite <- !Z.ltb_lt, sxz_ltb by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39873560648.5000007S1u1v1H". (* [comment removed for export] *)
Lemma sxz_le_iff : forall u v, 0 <= u < 2^32 -> 0 <= v < 2^32 -> (sxz u <= sxz v <-> u <= v).
Proof. intros u v Hu Hv. pose proof (sxz_lt_iff v u Hv Hu). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma limb32_of_read : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pws,(19.(2.&40.))Pr,$13.Pw,(2.&40.)P,(4.(10.(2.&40.))(2?.(2.&40.)R3.(2=.(15.R2.+1.)))(30.(2.&40.)R1.))(4.$13.(2<.R4.(2=.(15.R3.+1.)))(31.(16.&40.R2.)(32.+2.+20.)))")
(* [comment removed for export] *).
Proof. intros ws r w H. unfold limb32. rewrite (nth_error_nth _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma mpd_abs_lval : forall d, Z.of_nat (length (md_limbs d)) = md_n d -> mpd_abs d = lval (md_limbs d) (md_n d).
Proof. intros d H. unfold mpd_abs, lval. rewrite <- H, Nat2Z.id, firstn_all. reflexivity. Qed.

Lemma zlow64_small : forall x, 0 <= x < 2^64 -> zlow 64 x = x.
Proof. intros x Hx. unfold zlow. apply Z.mod_small. exact Hx. Qed.

Lemma sw_sxz_w : forall w : word, zlow 64 (zswrap 32 (zlow 32 (bv_unsigned w))) = sxz (w32 w).
Proof.
  intros w. pose proof (w32_range w) as R. change (zlow 32 (bv_unsigned w)) with (w32 w).
  remember (w32 w) as u eqn:Eu. clear Eu.
  unfold zlow, zswrap, sxz. change (32 - 1) with 31.
  destruct (Z.ltb_spec u (2^31)) as [L|L].
  - rewrite (Z.mod_small (u + 2^31) (2^32)) by lia. rewrite Z.mod_small; lia.
  - replace (u + 2^31) with ((u - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (u - 2^31) (2^32)) by lia.
    replace (u - 2^31 - 2^31) with ((u + (2^64 - 2^32)) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
Qed.

Lemma SIGF_eq : forall xs n i ys n' j, SIGF xs n i -> SIGF ys n' j -> i = j ->
  (i = 0 /\ lval xs n = 0 /\ lval ys n' = 0) \/ (1 <= i /\ 0 < lval xs n /\ 0 < lval ys n').
Proof.
  intros xs n i ys n' j (I1 & I2 & I3) (J1 & J2 & J3) E. subst j. rewrite I2, J2.
  destruct (Z.eq_dec i 0) as [->|Ni]; [left; rewrite !lval_0; lia| right].
  destruct I3 as [I3|I3]; [lia|]. destruct J3 as [J3|J3]; [lia|].
  pose proof (pow32_pos (i - 1) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WalkP.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X P n sg : Z) (xs : list word) (pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells usegs m X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at usegs m P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis CY : rw_cells usegs m Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at usegs m Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis SG' : sg' = 1 \/ sg' = -1.
  Hypothesis YB : 0 <= Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis XA : X mod 8 = 0.
  Hypothesis XN : 0 < X.
  Hypothesis YA : Y mod 8 = 0.
  Hypothesis YN : 0 < Y.
  Hypothesis PR : 0 <= P /\ P + 4 * n <= 2^64.
  Hypothesis QR : 0 <= Q /\ Q + 4 * n' <= 2^64.

  Let POST (T : Z) := mpi_cmp_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T m.

  Local Ltac pc_norm :=
    repeat match goal with
    | H : context [zlow 64 (zswrap 32 (zlow 32 (bv_unsigned ?w)))] |- _ => rewrite (sw_sxz_w w) in H
    end;
    repeat match goal with
    | H : (sxz ?u <? sxz ?v) = _ |- _ => rewrite (sxz_ltb u v (w32_range _) (w32_range _)) in H
    end;
    repeat match goal with
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    end;
    repeat match goal with
    | H : context [zlow 64 ?x] |- _ => rewrite (zlow64_small x) in H by lia
    end;
    repeat match goal with
    | H : sxz (w32 ?w) = 0 |- _ => apply (sxz_zero_iff _ (w32_range w)) in H
    | H : sxz (w32 ?w) <> 0 |- _ => rewrite (sxz_zero_iff _ (w32_range w)) in H
    end.

  Local Ltac same_mem := lazymatch goal with H : ?l = m |- _ => subst l end.

  Local Ltac ret_post :=
    apply evt_done; subst POST; unfold mpi_cmp_post; cbv beta; do 14 eexists;
    split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl| assumption].

  Local Ltac ret_with T :=
    lazymatch goal with
    | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        replace (Z_to_bv 64 v) with (Z_to_bv 64 T); [ret_post|]
    end.

  Lemma u_loop3 : forall (k : nat) (r T : Z) (w2 w3 w4 a5 a6 a7 x0 x1 x2 : word),
    Z.to_nat r = k -> 1 <= r -> r <= n -> r <= n' ->
    T = sg * Z.sgn (lval xs r - lval ys r) ->
    w2 = Z_to_bv 64 (4 * r - 4) -> w3 = Z_to_bv 64 r -> w4 = Z_to_bv 64 sg ->
    evt usegs (POST T)
      (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) w2 w3 w4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 132020) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros r T w2 w3 w4 a5 a6 a7 x0 x1 x2 Hk Hr Rn Rn' HT -> -> ->; [lia|].
    destruct PB as [N0|[PP PAL]]; [lia|]. destruct QB as [N0|[QP QAL]]; [lia|].
    lx_limb HX (r - 1) wx VX. lx_limb HY (r - 1) wy VY.
    lx_run_tac (PLAN [132020; 132168] [] 200%N); lx_tree.
    all: same_mem; pc_norm.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 132020) _ _ _ _] =>
             eapply (IH (r - 1) T);
             [ lia | lia | lia | lia | rewrite HT, (cmp_step_eq xs ys r) by lia; reflexivity
             | f_equal; lia | f_equal; lia | reflexivity ]
         | |- _ =>
             ret_with T; f_equal; rewrite HT;
             first [ rewrite (cmp_step_gt xs ys r) by lia; lia
                   | rewrite (cmp_step_lt xs ys r) by lia; lia
                   | rewrite (cmp_step_eq xs ys r) by lia; replace (r - 1) with 0 by lia;
                     rewrite !lval_0, Z.sub_diag; change (Z.sgn 0) with 0; lia ]
         end.
  Qed.

  Lemma u_decide : forall (i j : Z) (w2 w3 w4 w5 a6 a7 x0 x1 x2 : word),
    SIGF xs n i -> SIGF ys n' j ->
    w2 = Z_to_bv 64 (4 * i - 4) -> w3 = Z_to_bv 64 (i + 1) -> w4 = Z_to_bv 64 i -> w5 = Z_to_bv 64 j ->
    evt usegs (POST (Z.sgn (sg * lval xs n - sg' * lval ys n')))
      (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) w2 w3 w4 w5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131944) fc None m (seg_rom usegs)).
  Proof.
    intros i j w2 w3 w4 w5 a6 a7 x0 x1 x2 SX SY -> -> -> ->.
    pose proof SX as (I1 & I2 & I3). pose proof SY as (J1 & J2 & J3). lx_hide I3. lx_hide J3.
    pose proof (lor_lt_pow2 j i 64 ltac:(lia) ltac:(lia)) as LR.
    pose proof (lor_ge_r j i ltac:(lia) ltac:(lia)) as LI.
    pose proof (lor_ge_r i j ltac:(lia) ltac:(lia)) as LJ. rewrite Z.lor_comm in LJ.
    pose proof (lval_range xs n ltac:(lia)) as RX. pose proof (lval_range ys n' ltac:(lia)) as RY.
    pose proof CX as CX1. pose proof CY as CY1. lx_hide CX. lx_hide CY.
    destruct SG as [E1|E1]; destruct SG' as [E2|E2]; rewrite E1 in CX1; rewrite E2 in CY1.
    all: lx_run_tac (PLAN [132020; 132168] [] 200%N); lx_tree.
    all: same_mem; pc_norm.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 132020) _ _ _ _] =>
             assert (Eji : j = i) by lia;
             eapply (u_loop3 (Z.to_nat i) i);
             [ reflexivity | lia | lia | lia
             | rewrite I2, J2, Eji; replace sg' with sg by lia; apply sgn_same_sign; lia
             | f_equal; lia | f_equal; lia | f_equal; lia ]
         | |- _ =>
             ret_with (Z.sgn (sg * lval xs n - sg' * lval ys n')); f_equal; rewrite E1, E2;
             destruct (Z.lt_trichotomy i j) as [L|[L|L]];
             [ pose proof (SIGF_lt ys n' j xs n i SY SX L)
             | destruct (SIGF_eq xs n i ys n' j SX SY L) as [(? & ? & ?)|(? & ? & ?)]
             | pose proof (SIGF_lt xs n i ys n' j SX SY L) ];
             try (exfalso; assert (Z.lor j i = 0) by (replace i with 0 by lia; replace j with 0 by lia; reflexivity); lia);
             match goal with |- Z.sgn ?e = _ => destruct (Z.sgn_spec e) as [[A B]|[[A B]|[A B]]]; rewrite B; lia end
         end.
  Qed.

  Lemma u_loop2 : forall (k : nat) (i j : Z) (w2 w3 w4 a5 w6 w7 x0 x1 x2 : word),
    Z.to_nat j = k -> 0 <= j <= n' -> lval ys n' = lval ys j -> SIGF xs n i ->
    w2 = Z_to_bv 64 (4 * i - 4) -> w3 = Z_to_bv 64 (i + 1) -> w4 = Z_to_bv 64 i ->
    w6 = Z_to_bv 64 (4 * j - 4) -> w7 = Z_to_bv 64 j ->
    evt usegs (POST (Z.sgn (sg * lval xs n - sg' * lval ys n')))
      (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) w2 w3 w4 a5 w6 w7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131876) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i j w2 w3 w4 a5 w6 w7 x0 x1 x2 Hk Hj HYj HS -> -> -> -> ->;
      pose proof HS as (Hi & HXi & HT); lx_hide HT.
    - assert (j = 0) as -> by lia.
      lx_run_tac (PLAN [131876; 131944; 132168] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: eapply (u_decide i 0);
           [ exact HS | split; [lia|]; split; [exact HYj| left; reflexivity]
           | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ].
    - destruct QB as [N0|[QP QAL]]; [lia|].
      lx_limb HY (j - 1) wy VY.
      lx_run_tac (PLAN [131876; 131944; 132168] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 131876) _ _ _ _] =>
               eapply (IH i (j - 1));
               [ lia | lia | rewrite HYj; apply lval_drop_zero; lia | exact HS
               | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ]
           | |- _ =>
               eapply (u_decide i j);
               [ exact HS | split; [lia|]; split; [exact HYj| right; apply lval_top_nonzero; lia]
               | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ]
           end.
  Qed.

  Lemma u_loop1 : forall (k : nat) (i : Z) (a2 w3 a4 w5 w6 a7 x0 : word),
    Z.to_nat i = k -> 0 <= i <= n -> lval xs n = lval xs i ->
    w3 = Z_to_bv 64 (-4) -> w5 = Z_to_bv 64 (4 * i - 4) -> w6 = Z_to_bv 64 i ->
    evt usegs (POST (Z.sgn (sg * lval xs n - sg' * lval ys n')))
      (MS (mkR ra sp gp tp x0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 w3 a4 w5 w6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 131776) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i a2 w3 a4 w5 w6 a7 x0 Hk Hi HXi -> -> ->.
    - assert (i = 0) as -> by lia.
      lx_run_tac (PLAN [131876; 132168] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: eapply (u_loop2 (Z.to_nat n') 0 n');
           [ reflexivity | lia | reflexivity | split; [lia|]; split; [exact HXi| left; reflexivity]
           | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ].
    - destruct PB as [N0|[PP PAL]]; [lia|].
      lx_limb HX (i - 1) wx VX.
      lx_run_tac (PLAN [131776; 131876; 132168] [] 200%N); lx_tree.
      all: same_mem; pc_norm.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 131776) _ _ _ _] =>
               eapply (IH (i - 1));
               [ lia | lia | rewrite HXi; apply lval_drop_zero; lia
               | f_equal; lia | f_equal; lia | f_equal; lia ]
           | |- _ =>
               eapply (u_loop2 (Z.to_nat n') i n');
               [ reflexivity | lia | reflexivity
               | split; [lia|]; split; [exact HXi| right; apply lval_top_nonzero; lia]
               | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia ]
           end.
  Qed.

  Lemma u_cmp_mpi : forall (a2 a3 a4 a5 a6 a7 : word),
    evt usegs (POST (Z.sgn (sg * lval xs n - sg' * lval ys n')))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 U_MPI_CMP_MPI) fc None m (seg_rom usegs)).
  Proof.
    intros a2 a3 a4 a5 a6 a7. unfold U_MPI_CMP_MPI.
    lx_run_tac (PLAN [131776; 132168] [] 200%N); lx_tree.
    all: same_mem; pc_norm.
    all: eapply (u_loop1 (Z.to_nat n) n); [ reflexivity | lia | reflexivity | f_equal; lia | f_equal; lia | f_equal; lia ].
  Qed.
End WalkP.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L15042936624.15L16457969228.15L23834409035.15L24897143244.18L28825951035.18L36947023110.17L63831829383.15L65156019367.17L9205666860.17 00000500:00B00G00U00Z00d01901JS1d1BS1d1BS1d2HN1BS1d1BS1d4HPOS1k1E1BS1d1BS1d4HPOS1BS1d4HPOS1b1l2HL3HN01BS4segs1m1d1B1i2Hi". (* [comment removed for export] *)
Lemma mpd_raw : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Psegs,(19.$37.)Pm,P,(2.&40.)(10.(2.&8.))PLB,(19.$1:.)Pd,$1;.P,(1<.R4.R3.R2.R1.)P,P,(4.$1=.(1>.R2.)$1?.)(20.=(21.R3.))(3.(38.R6.R5.(22.R3.)(11.$39.(3:.(7.&40.(21.R3.)))(11.$39.(3;.(7.&40.(3<.R3.)))(11.$39.(3;.(7.&40.(3=.R3.)))(11.$39.(3>.(3?.R3.))(<.$39.))))))(3.(40.R6.R5.(21.R3.)(41.(42.R3.)))(3.(4.$13.(43.(44.(2.&40.)(42.R3.)))(3=.R3.))(3.(3.(29.=(3=.R3.))(29.(3=.R3.)+2710.))(3.(28.(4.$13.(3<.R3.)+1.)(4.$13.(3<.R3.)-1.))(3.(3.(29.=(22.R3.))(29.(34.(22.R3.)+10.)(32.+2.+40.)))(28.(4.$13.(3=.R3.)=)(3.(20.=(21.R3.))(4.$13.(31.(21.R3.)+4.)=)))))))))")
(* [comment removed for export] *).
Proof.
  intros segs m LB d [(HR & HAL & HPOS & HL & HN & HO) HS] PNZ. unfold MPI_MAX_LIMBS in HN.
 unfold mpi_cells in HR.
  pose proof (rw_cells_bound _ _ _ _ HR) as B. cbn [cells_size csize Nat.add] in B.
  split; [exact HR|]. 
  assert (K : bytes_at segs m (md_p d) (u32s (md_limbs d)) /\ (md_n d = 0 \/ 0 < md_p d /\ md_p d mod 4 = 0)).
  { destruct (md_own d) eqn:EO.
    - destruct HO as [HP HN0]. rewrite HP. assert (md_limbs d = []) as -> by (destruct (md_limbs d); [reflexivity| cbn in HL; lia]).
      split; [| left; exact HN0]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - ddestruct HO as (N1 & PIN & PAL & [HB _]). split; [exact HB| right]. split; [exact (PNZ eq_refl)|].
      apply Z.mod_divide in PAL; [| lia]. apply Z.mod_divide; [lia|]. destruct PAL as [k E]. exists (4 * k). lia.
    - ddestruct HO as (N1 & PAL & PP & HB & _). split; [exact HB| right; split; [exact PP| exact PAL]]. }
  destruct K as [K1 K2]. split; [exact K1|]. split; [exact HL|]. split; [lia|]. split; [exact HS|]. split; [lia| exact K2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Theorem U_mpi_cmp_mpi_spec_o : mpi_cmp_mpi_stmt_o usegs U_MPI_CMP_MPI.
Proof.
  unfold mpi_cmp_mpi_stmt_o. intros until dY. intros HX HY PX PY MI -> ->.
  pose proof (opnd_view _ _ _ _ _ HX) as ((_ & XA & XN & _) & _).
  pose proof (opnd_view _ _ _ _ _ HY) as ((_ & YA & YN & _) & _).
  destruct (opnd_raw _ _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  destruct (opnd_raw _ _ _ _ _ HY PY) as (CY & BY & LY & NY & SY & ABY & PBY).
  pose proof BX as PRX. apply bytes_at_bound in PRX. rewrite u32s_length in PRX.
  pose proof BY as PRY. apply bytes_at_bound in PRY. rewrite u32s_length in PRY.
  unfold mpd_val. fold (mpd_abs dX) (mpd_abs dY). rewrite !mpd_abs_lval by assumption.
  eapply u_cmp_mpi; try eassumption; lia.
Qed.

Theorem U_mpi_cmp_mpi_spec : mpi_cmp_mpi_stmt usegs U_MPI_CMP_MPI.
Proof.
  unfold mpi_cmp_mpi_stmt. intros until dY. intros HX HY PX PY MI EA EB.
  eapply U_mpi_cmp_mpi_spec_o; [apply opnd_at_mpd; exact HX | apply opnd_at_mpd; exact HY | exact PX | exact PY | exact MI | exact EA | exact EB].
Qed.
