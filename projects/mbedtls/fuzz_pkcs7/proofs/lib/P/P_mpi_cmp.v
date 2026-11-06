(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_cmp () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_cmp_post"; "Stdlib.ZArith.BinInt.Z.sgn"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.P.PImg.psegs"; "SIGF"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"].


Definition P_MPI_CMP_MPI : Z := 0x1f8e8.
Definition P_MPI_CMP_INT : Z := 0x1f9e0.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WalkP.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X P n sg : Z) (xs : list word) (pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells psegs m X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at psegs m P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis CY : rw_cells psegs m Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at psegs m Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis SG' : sg' = 1 \/ sg' = -1.
  Hypothesis YB : 0 <= Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis MI : mem_inv psegs m.

  Let POST (T : Z) := mpi_cmp_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T m.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L11014201954.79 L11014202083.78 L1120085281.72  L1183333284.76  L13987013234.79 L14957715125.76 L21750432760.79 L22553357965.78 L23100341967.72 L23917382008.79 L29010565666.65 L30163642507.104L30436581548.75 L3508006412.79  L38307974021.76 L41772055650.79 L42468637227.75 L42470501281.76 L44654311153.79 L47013807010.79 L4812189352.78  L49845099932.66 L54425554052.73 L54425647149.79 L54427583239.74 L56834426490.79 L58393504934.70 L58393505061.72 L59308628179.1  L59308628179.4  L60497097172.76 L66151422254.64 00000H00`01001B01]01^02602k03;03e04A04B04C05805905X06006H06e07]08808I08[09309E09]0;l0>;0>?0>J0>\0>oS1P2xs1Q2ys1k1r2Hk2wx2wyS1P2xs1Q2ys1k1r2Hk2wx2wyS2xs1Y2ys1k1r2HkS1P2xs1Q2ys1k1r2HkS1P2sg2xs1Q2ys1k1r2Hk2wx2wyFS1P2xs1Q2ys1k1r2Hk2wx2wyS1P1n2xs1Q2n'2ys2PB2QB1k1r2Hk2Rn3Rn'2wx2wy3LXr3LYr2K1S1X2xs2ys1k1r2HkS1P1n2xs1Q2n'2ys2PB2QB1k1r2Hk2Rn3Rn'2wx2wyS2xs2n'2ys3Hn'1k1r2Hk2Hr3Rn'FFS1P1n2xs1Q2n'2ys2PB2QB1k1r2Hk2Rn3Rn'2wx2wy3LXr3LYr2K2FS1P2xs1Q2n'2ys1k1r2Hk3Rn'2wx2wyS1P2xs1Q2ys1k1r2Hk2wx2wyS1P2xs1Q2ys1k1r2Hk2wx2wyS1P1n2xs1Q2ys1k1r2Hk2Rn2wx2wyS1P1n2xs1Q2n'2ys2PB2QB1k1r2Hk2Rn3Rn'2wx2wy3LXr3LYr2K12K2S1P2sg2xs1Q2ys1k1r2Hk2wx2wyS1P2sg2xs1Q2ys2HkS1P2xs1Q2ys1k1r2HkS1P2xs1Q2ys1k1r2Hk2wx2wyS1P2xs1Q2ys1k1r2HkS1P2xs1Q2ys1k1r2Hk2wx2wyS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2sg2xs1Y1Q2n'2ys2LX2PB2QB4POST1k1r1T2a52a62a72Hk2Rn3Rn'2NXS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2sg2xs1Y1Q2n'2ys2PB2LY2QB4POST1k1r1T2a52a62a72Hk2Rn3Rn'2NYS2K0S1k1r2Hk2K0S1P2xs1Q2ys1k1r2HkS1P2xs1Q2ys1r2Hk2Hr". (* [comment removed for export] *)
  #[using="P pad Q sg' pad' CX HX LX PB CY HY LY Hn' QB MI"] Lemma p_loop3 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pk,$33.Pr,$13.PT,$13.Pw12,(2.&40.)Pw14,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(4.$33.(2=.R7.)R8.)P,(29.=R8.)P,(29.R9.Vn,)P,(29.R:.Vn',)P,(4.$13.R:.(2:.Vsg,(25.(15.(2>.Vxs,R;.)(2>.Vys,R;.)))))P,(4.(2.&40.)R:.(7.&40.(34.R<.+1.)))P,(4.(2.&40.)R:.(7.&40.(15.(2:.+4.R=.)+4.)))(23.$35.A1.VPOST,R=.(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(7.&40.VX,)(7.&40.VY,)R<.(7.&40.Vsg,)R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+1?984.)Vfc,(9.(2.&40.))Vm,(:.$35.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r T w12 w14 a5 a6 a7 Hk Hr Rn Rn' HT -> ->.
    - assert (r = 0) as -> by lia.
      pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
      zstep. zstep. if_cases K0; zify_cond K0; [| exfalso; clear - K0; lia].
      zstep. zstep. replace (Z_to_bv 64 0) with (Z_to_bv 64 T) by (f_equal; rewrite HT, !lval_0; cbn; lia). finish.
    - pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
      zstep. zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 Hk; lia|].
      destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; lia].
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; lia].
      pose proof (u32ro_read psegs m P xs (r - 1) wx _ HX NX ltac:(lia) eq_refl) as RDX.
      pose proof (u32ro_read psegs m Q ys (r - 1) wy _ HY NY ltac:(lia) eq_refl) as RDY.
      zstep. zstep. zstep. zstep. zstep. zstep. clear RDX RDY.
      pose proof (limb32_of_read xs r wx NX) as LXr. pose proof (limb32_of_read ys r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Bx.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(lia)) as By.
      zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_lt_iff _ _ By Bx)) in K1.
        zstep. zstep. replace (Z_to_bv 64 sg) with (Z_to_bv 64 T) by (f_equal; rewrite HT, (cmp_step_gt xs ys r) by lia; lia). finish.
      + apply (proj1 (sxz_le_iff _ _ Bx By)) in K1.
        zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
        * (* [comment removed for export] *)
          apply (proj1 (sxz_le_iff _ _ By Bx)) in K2.
          eapply (IH (r - 1) T); [lia| lia| lia| lia| rewrite HT, (cmp_step_eq xs ys r) by lia; reflexivity| f_equal; lia| f_equal; lia].
        * (* [comment removed for export] *)
          apply (proj1 (sxz_lt_iff _ _ Bx By)) in K2.
          zstep. zstep. replace (Z_to_bv 64 (0 - sg mod 18446744073709551616)) with (Z_to_bv 64 T); [finish|].
          apply Z_to_bv_eqm. rewrite HT, (cmp_step_lt xs ys r) by lia. change 18446744073709551616 with (2^64).
          rewrite Zminus_mod_idemp_r. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0?L10116397382.81L10351988177.79L10351988177.80L10352001614.70L10354098792.79L10913375429.76L11433576588.71L14288440509.78L15912992687.79L1890460238.73 L2424904290.75 L27147534220.77L27601760771.75L32954672704.69L32954672833.68L32954672962.67L32955044585.66L35937035424.78L39881073330.78L39975566808.73L39975603450.75L41250042025.79L41250042670.78L41417842135.79L42991129712.74L44878774199.75L45272398924.71L48521138956.80L51200503683.79L5126932107.76 L53770557096.79L55488359596.69L57418377771.79L58650804904.78L58871878637.75L59308628304.79L59308628695.77L59308628695.78L59308628820.78L59309010171.73L59310766666.76L59310766666.77L66184202712.73L66184231035.74L66253296149.66L66253710909.68L66253711036.69L66253711294.67L66255345703.72L7938752179.78 00000M00_01101C01U01i02;02H04A04^05205K05`06506J06_07407A07N07c08:08P08f09309I09^0:30:P0:]0;60;H0;I0;\0=U0=h0>80>90>I0>J0>X0>Y0>i0?<0?Q0?d0@70@T0@g0A80AES1P2xs1Q2n'2ys1i2I32J12PP3RY'S1P1n2xs1Q2ys1i2I1S1P1n2xs1Q2ys1i2I1S1P1n2xs1Q2ys1i2I1S1P1n2xs1Q2ys1i2I1S1P1n2xs1Q2ys1i1j2K2S1P2sg2xs1Q3sg'2ysS1P2xs1Q2ys1iS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2xs1Y1Q2n'2ys4POST1i2a62a72I12I33NeiS1P1n2xs1Q2n'2ys1i1j2I12J12K0S1P1n2xs1Q2ys2Hn1i1jS1P1n2xs1Q2n'2ys1i1j1H2H0S1P2xs1Q2ys1i1j2K12K2S2xs2n'2ys3Hn'1i1j2J1S2xs2n'2ys3Hn'1i1j2J1S2xs2n'2ys3Hn'1i1j2J1S2xs2n'2ys3Hn'1i1j2J1S1P2xs1Q2ys1iS1P2xs1Q2ys1iS1P2xs1Q3sg'2ys3SG'1iS1P2xs1Q3sg'2ys3SG'1i1jS1P1n2xs1Q2ys1i2I13NeiS1P1n2xs1Q2ys1i2I13NeiS1P2xs1Q2ys1iS1P2xs1Q2n'2ys3Hn'1i1jS1P2xs1Q2n'2ys1i1j2K1S1P2xs1Q2n'2ys1i1j2J1S1P2xs1Q2n'2ys1i2I32J12PP3RY'S1P2xs1Q2ys1iS1P1n2xs1Q2n'2ys1i1j1H2H0S1P1n2xs1Q2ys1i2I1FS1P2xs1Q2n'2ys1i2J1S2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2xs1Y1Q2n'2ys4POST1i2a62a72I12I33NeiS1P2xs1Q3sg'2ys1i1jS1P2xs1Q2ys1i2K1FS1P2xs1Q2ys1i2K4FS1P2xs1Q2ys2K0FS1P2xs1Q2ys1i2K1S1P2sg2xs1Q2ys2SG1iS1P2sg2xs1Q2ys2SG1i1jS1n2xs2ys2Hn1i1j2I1S1n2xs2ys2Hn1i1j2I1S1n2xs2n'2ys3Hn'1i1j2I12J12K1S1n2xs2ys2Hn1i1j2I1S1n2xs2ys2Hn1i2I1S1P2xs1Q2ys1i". (* [comment removed for export] *)
  #[using="P pad Q pad' CX HX LX Hn SG PB CY HY LY Hn' SG' QB MI"] Lemma p_decide : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pi,$13.Pj,$13.Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(36.Vxs,Vn,R6.)P,(36.Vys,Vn',R6.)(23.$35.A1.VPOST,(25.(15.(2:.Vsg,(2>.Vxs,Vn,))(2:.Vsg',(2>.Vys,Vn',))))(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(7.&40.VX,)(7.&40.VY,)(7.&40.R8.)(7.&40.R7.)R6.R5.R4.R3.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+1?940.)Vfc,(9.(2.&40.))Vm,(:.$35.)))")
(* [comment removed for export] *).
  Proof.
    intros i j a4 a5 a6 a7 SX SY. dpose SX as (I1 & I2 & I3). dpose SY as (J1 & J2 & J3).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (lval_range xs i ltac:(lia)) as RX. pose proof (lval_range ys j ltac:(lia)) as RY.
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep.
      assert (i = 0 /\ j = 0) as [-> ->] by (rewrite Z.lor_comm in K0 || idtac; apply Z.lor_eq_0_iff in K0; lia).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - sg' * lval ys n'))) by (f_equal; rewrite I2, J2, !lval_0; lia).
      finish. }
    zstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *) zstep. rewrite sx16_small by lia. zstep.
        replace (Z_to_bv 64 sg) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - sg' * lval ys n'))); [finish|].
        f_equal. apply sgn_of_lt; [exact SG| exact SG'|]. pose proof (lval_range ys n' ltac:(lia)). pose proof (SIGF_lt xs n i ys n' j SX SY ltac:(lia)). lia. }
    zstep. if_cases K2; zify_cond K2.
    2:{ (* [comment removed for export] *) zstep. rewrite sx16_small by lia. zstep. zstep.
        replace (Z_to_bv 64 (0 - sg' mod 18446744073709551616)) with (Z_to_bv 64 (Z.sgn (sg * lval xs n - sg' * lval ys n'))); [finish|].
        apply Z_to_bv_eqm. change 18446744073709551616 with (2^64). rewrite Zminus_mod_idemp_r. f_equal.
        rewrite (sgn_of_gt sg sg'); [lia| exact SG| exact SG'|].
        pose proof (lval_range xs n ltac:(lia)). pose proof (SIGF_lt ys n' j xs n i SY SX ltac:(lia)). lia. }
    (* [comment removed for export] *)
    assert (j = i) as -> by lia. destruct (Z.eq_dec i 0) as [Ei|Nei]. { exfalso. subst i. rewrite Z.lor_0_l in K0. lia. }
    clear K0 K1 K2.
    assert (LP : forall s a5 a6 a7, s = 1 \/ s = -1 -> sg = s -> sg' = s ->
      evt psegs (POST (Z.sgn (sg * lval xs n - sg' * lval ys n')))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 i) (Z_to_bv 64 s) (Z_to_bv 64 s) a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1f978) fc None m (seg_rom psegs))).
    { intros s b5 b6 b7 Hs E1 E2. subst s. pose proof (munch_refl ([] : list ivl) m) as MU'. pose proof (wmono_refl psegs m) as WM'.
      zstep. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      eapply (p_loop3 (Z.to_nat i) i); [reflexivity| lia| lia| lia| | f_equal; lia| f_equal; lia].
      rewrite I2, J2, E2. apply sgn_same_sign. exact SG. }
    zstep. zstep. rewrite !sx16_small by lia. zstep.
    destruct SG as [Es|Es]; rewrite Es in *; (zstep; if_cases K3; zify_cond K3); destruct SG' as [Es'|Es']; rewrite Es' in *.
    all: try (exfalso; cbv in K3; discriminate K3).
    all: try (exfalso; lia).
    all: (zstep; if_cases K4; zify_cond K4).
    all: try (exfalso; cbv in K4; discriminate K4).
    all: try (exfalso; lia).
    all: try (apply LP; lia).
    all: try (zstep; if_cases K5; zify_cond K5).
    all: try (exfalso; cbv in K5; discriminate K5).
    all: try (exfalso; lia).
    all: try (apply LP; lia).
    (* [comment removed for export] *)
    all: destruct I3 as [I3|I3]; [lia|]; pose proof (pow32_pos (i - 1) ltac:(lia)) as PP; pose proof (lval_range ys i ltac:(lia)) as RY'.
    all: zstep; zstep.
    - replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.sgn (1 * lval xs n - -1 * lval ys n'))) by (f_equal; rewrite I2, J2; apply Z.sgn_pos; lia). finish.
    - replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (Z.sgn (-1 * lval xs n - 1 * lval ys n'))) by (f_equal; rewrite I2, J2; apply Z.sgn_neg; lia). finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11014116938.73L11014201954.73L1137720866.73 L1962781522.73 L21409347490.73L2164583015.68 L2166694122.63 L23917382008.73L23970764156.69L24672582925.73L31326834835.73L42468637227.70L43921870074.73L49857167078.71L54425554052.69L64930767917.7300000K00f01D01l02H04T06U07307N07c08A08V09109C09[0:9S1P2xs1Q2n'2ys1k1r2Hk2Hr2wyS1P2xs1Q2n'2ys1k1r2Hk2Hr2wyS1P2xs1Q2n'2ys1k1r2Hk2Hr2wy2K2S1P2xs1Q2n'2ys1k1r2Hk2Hr2wy3LYr2K12QB2K2S1P2xs1Q2n'2ys3Hn'1k1r2Hk2wyS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2sg2xs1Y1Q2n'3sg'2ys2LY2QB4POST1k1i1r2a52a62a72Hk2Hr2NYS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2sg2xs1Y1Q2n'3sg'2ys4POST1i1r2a52a62a72Hk2HrS1P2xs1Q2n'2ys2QB1k1r2Hk2Hr2wyS2xs2n'2ys3Hn'1k1r2Hk2Hr2wyS1P2xs1Q2ys1k1r2Hk2wyS1P2xs1Q2n'2ys1k1r2Hk2Hr2wy2K2S1P2xs1Q2ys1k1r2Hk2wyS1P2xs1Q2n'2ys1k1r2Hk2Hr2wyS1P2xs1Q2ys1k1r2HkS1P2xs1Q2n'2ys1k1r2Hk2HrS1P2xs1Q2n'2ys1k1r2Hk2Hr2wy2K2". (* [comment removed for export] *)
  #[using="P pad pad' CX HX LX Hn SG PB CY HY LY Hn' SG' QB MI"] Lemma p_loop2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pk,$33.Pi,$13.Pr,$13.Pw13,(2.&40.)Pw14,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(4.$33.(2=.R6.)R8.)P,(3.(29.+1.R7.)(29.R7.Vn',))P,(36.Vxs,Vn,R9.)P,(4.$13.(2>.Vys,Vn',)(2>.Vys,R9.))P,(4.(2.&40.)R9.(7.&40.R:.))P,(4.(2.&40.)R9.(7.&40.(15.(34.VQ,(2:.+4.R;.))+4.)))(23.$35.A1.VPOST,(25.(15.(2:.Vsg,(2>.Vxs,Vn,))(2:.Vsg',(2>.Vys,Vn',))))(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(7.&40.VX,)(7.&40.VY,)(7.&40.R=.)R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+1?92<.)Vfc,(9.(2.&40.))Vm,(:.$35.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i r w13 w14 a5 a6 a7 Hk Hr SX INV -> ->; [lia|].
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; lia].
    pose proof (u32ro_read psegs m Q ys (r - 1) wy _ HY NY ltac:(lia) eq_refl) as RDY.
    zstep. clear RDY. pose proof (limb32_of_read ys r wy NY) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(lia)) as By.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 ys (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
      apply p_decide; [exact SX|]. split; [lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [lia| exact NZ].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ By)) in K1.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH i (r - 1)); [lia| lia| exact SX| rewrite INV; apply lval_drop_zero; lia| f_equal; lia| f_equal; lia].
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; lia).
        apply p_decide; [exact SX|]. split; [lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero ys r) by lia. replace (r - 1) with 0 by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L1120085281.61 L14972936856.64L20890399074.64L41415942734.64L50702591249.63L54258658734.60L68338037100.6400000900N00\00g01901G01YS2xs1Y2ysS1P2xs1Q2n'2ys3Hn'2K0S1P2xs1Q2n'2ysS1P2xs1Q2ysS1P2xs1Q2n'2ys3Hn'S2xs2n'2ys3Hn'S1P2xs1Q2n'2ys3Hn'". (* [comment removed for export] *)
  #[using="P pad Q pad' CX HX LX Hn SG PB CY HY LY Hn' SG' QB MI"] Lemma p_stage2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pi,$13.Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(36.Vxs,Vn,R6.)(23.$35.A1.VPOST,(25.(15.(2:.Vsg,(2>.Vxs,Vn,))(2:.Vsg',(2>.Vys,Vn',))))(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(7.&40.VX,)(7.&40.VY,)(7.&40.R7.)R6.R5.R4.R3.R2.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+1?914.)Vfc,(9.(2.&40.))Vm,(:.$35.)))")
(* [comment removed for export] *).
  Proof.
    intros i a3 a4 a5 a6 a7 SX.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. rewrite zx16_small by lia. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *) apply p_decide; [exact SX|]. split; [lia|]. split; [reflexivity| left; exact K0].
    - zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      eapply (p_loop2 (Z.to_nat n') i n'); [reflexivity| lia| exact SX| reflexivity| reflexivity| f_equal; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11014116938.72L11014201954.72L21007948123.72L23917382008.72L23970764156.68L31326834835.72L33397861202.72L42164717379.72L42468637611.69L54425554183.68L56393850587.72L58159996790.62L58162074744.67L64930767917.72L65090966688.72L67745676442.7000000J00d01>01[02402Q03803R03g04>04[06]08j09G09\09nS1P1n2xs1Q2ys1k1r2Hk2Hr2wxS1P1n2xs1Q2ys1k1r2Hk2Hr2wxS1P1n2xs1Q2ys2Hn1k1r2Hk2wxS1P1n2xs1Q2ys2PB1k1r2Hk2Hr2wxS1n2xs2ys2Hn1k1r2Hk2Hr2wxS1P1n2xs1Q2ys1k1r2Hk2Hr2wx2K2S1P1n2xs1Q2ys1k1r2Hk2Hr2wx3LXr2K12PB2K2S1P1n2xs1Q2ys1k1r2Hk2Hr2wxS1P2xs1Q2ys1k1r2Hk2wxS1P1n2xs1Q2ys1k1r2Hk2HrS1P1n2xs1Q2ys1k1r2Hk2Hr2wx2K2S2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2sg2xs1Y1Q2n'3sg'2ys4POST1r2a42a52a62a72Hk2HrS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X1P1n2sg2xs1Y1Q2n'3sg'2ys2LX2PB4POST1k1r2a42a52a62a72Hk2Hr2NXS1P1n2xs1Q2ys1k1r2Hk2Hr2wx2K2S1P2xs1Q2ys1k1r2Hk2wxS1P2xs1Q2ys1k1r2Hk". (* [comment removed for export] *)
  #[using="pad Q pad' CX HX LX Hn SG PB CY HY LY Hn' SG' QB MI"] Lemma p_loop1 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pk,$33.Pr,$13.Pw12,(2.&40.)Pw13,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)P,(4.$33.(2=.R7.)R8.)P,(3.(29.+1.R8.)(29.R8.Vn,))P,(4.$13.(2>.Vxs,Vn,)(2>.Vxs,R9.))P,(4.(2.&40.)R9.(7.&40.R:.))P,(4.(2.&40.)R9.(7.&40.(15.(34.VP,(2:.+4.R;.))+4.)))(23.$35.A1.VPOST,(25.(15.(2:.Vsg,(2>.Vxs,Vn,))(2:.Vsg',(2>.Vys,Vn',))))(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(7.&40.VX,)(7.&40.VY,)R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+1?900.)Vfc,(9.(2.&40.))Vm,(:.$35.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w12 w13 a4 a5 a6 a7 Hk Hr INV -> ->; [lia|].
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (nth_error xs (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32ro_read psegs m P xs (r - 1) wx _ HX NX ltac:(lia) eq_refl) as RDX.
    zstep. clear RDX. pose proof (limb32_of_read xs r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Bx.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZ : limb32 xs (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply p_stage2. split; [lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [lia| exact NZ].
    - (* [comment removed for export] *) apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH (r - 1)); [lia| lia| rewrite INV; apply lval_drop_zero; lia| f_equal; lia| f_equal; lia].
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; lia).
        apply p_stage2. split; [lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero xs r) by lia. replace (r - 1) with 0 by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L23100341967.60L33087517741.62L41415942734.63L44822653989.63L57586077194.63L58796971353.63L61929812114.5900000900I00T00g01401D01PS1X2xs2ysS1P1n2xs1Q2ys2HnS1P2xs1Q2ysS1P1n2xs1Q2ys2Hn2K0S1P1n2xs1Q2ysS1P1n2xs1Q2ys2HnS1n2xs2ys2Hn". (* [comment removed for export] *)
  #[using="P pad Q pad' CX HX LX Hn SG PB CY HY LY Hn' SG' QB MI"] Lemma p_cmp_mpi : ltac2:(CDefT.buildp (gd_tbl_P_mpi_cmp ()) "Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)(23.$35.A1.VPOST,(25.(15.(2:.Vsg,(2>.Vxs,Vn,))(2:.Vsg',(2>.Vys,Vn',))))(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(7.&40.VX,)(7.&40.VY,)R6.R5.R4.R3.R2.R1.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+1?8>8.)Vfc,(9.(2.&40.))Vm,(:.$35.)))")
(* [comment removed for export] *).
  Proof.
    intros a2 a3 a4 a5 a6 a7.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. rewrite zx16_small by lia. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *) apply p_stage2. split; [lia|]. split; [reflexivity| left; exact K0].
    - zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      eapply (p_loop1 (Z.to_nat n) n); [reflexivity| lia| reflexivity| reflexivity| f_equal; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
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

Theorem P_mpi_cmp_mpi_spec : mpi_cmp_mpi_stmt psegs P_MPI_CMP_MPI.
Proof.
  unfold mpi_cmp_mpi_stmt, P_MPI_CMP_MPI. intros until dY. intros HX HY PX PY MI -> ->.
  destruct (mpd_raw _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  destruct (mpd_raw _ _ _ _ HY PY) as (CY & BY & LY & NY & SY & ABY & PBY).
  unfold mpd_val. fold (mpd_abs dX) (mpd_abs dY). rewrite !mpd_abs_lval by assumption.
  eapply p_cmp_mpi; eassumption.
Qed.
