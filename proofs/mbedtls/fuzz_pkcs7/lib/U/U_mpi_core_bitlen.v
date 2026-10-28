(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_bitlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_bitlen_post"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.log2"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen_rec"].

Definition U_MPI_CORE_BITLEN : Z := 0x22b44.

(* [comment removed for export] *)

Definition mpi_core_bitlen_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (xs : list word) (n : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_bitlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(3.(4.$0.R10.(5.(6.O15.O14.O13.O12.R?.R>.R=.O11.O10.R<.R;.R:.R9.R8.R7.R6.R5.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R4.R3.R2.R1.)O5.(7.O15.)O4.(8.(2.&40.))O1.(9.O16.)))(3.(:.(;.$<.)O1.O1.)(3.(=.O16.O1.O1.)(3.(>.O16.O1.)(4.(2.&40.)R<.(?.&40.(10.O3.O2.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_bitlen_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_bitlen ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(11.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(12.(2.&8.))PA,$13.Pn,$13.Pxs,(14.(2.&40.))P,(15.O2.R4.R3.(16.R1.))P,(3.(17.=R3.)(17.R3.+2710.))P,(17.R4.(18.(19.(2.&40.)R3.)))P,(4.$13.(1:.R6.+4.)=)P,(1;.=R7.)P,(>.O2.R9.)P,(4.(2.&40.)R22.(?.&40.R9.))P,(4.(2.&40.)R22.(?.&40.R9.))(1<.O2.(1=.O2.R2=.R2<.R2;.R2:.R26.R25.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R>.R=.R9.R:.R<.)(5.(6.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(?.&40.O1.)R=.(8.(2.&40.))R<.(9.O2.)))")
(* [comment removed for export] *).

Local Ltac zb_split K := repeat match type of K with
  | context [Z.b2z (?x <? ?y)] => revert K; destruct (Z.ltb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x <=? ?y)] => revert K; destruct (Z.leb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x =? ?y)] => revert K; destruct (Z.eqb_spec x y); cbn [Z.b2z]; intro K
  end.
Local Ltac chk := let K := fresh "K" in if_cases K;
  [ zify_cond K; rewrite ?unsigned_lit, ?signed_lit_small in K by lia;
    rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2, ?land_3_mod' in K by lia; zb_split K;
    rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in K;
    first [ exfalso; lia | let T := type of K in idtac "PROBE KT" T; fail 1 ] | clear K ].

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (A n : Z) (xs : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= Z.of_nat (length xs).
  Hypothesis XB : 0 < A /\ A + 4 * Z.of_nat (length xs) <= 2^64.
  Hypothesis AL : A mod 4 = 0.
  Hypothesis HA : bytes_at usegs m A (u32s xs).
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (mpi_core_bitlen_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs n m).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma clz_walk : forall (w : word) (x r : Z) (x10 x12 x14 x15 x16 x17 w11 : word),
    x = bv_unsigned w mod 2 ^ 32 -> x <> 0 -> 1 <= r <= n ->
    core_bitlen xs n = 32 * (r - 1) + Z.log2 x + 1 -> w11 = Z_to_bv 64 (r - 1) ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 w11 x12 (sx32 w) x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x22b94) fc None m (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros w x r x10 x12 x14 x15 x16 x17 w11 Hx Hnz Hr HBL ->.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 12 zstep.
    destruct (smear_chain w x (Z.log2 x) Hx Hnz eq_refl) as [SM Bb]. cbv zeta in SM.
    rewrite SM. clear SM.
    set (b := Z.log2 x) in *. clearbody b.
    do 19 step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (_ - bv_unsigned ?raw)] =>
        assert (HR : bv_unsigned raw = 31 - b)
          by (clear -b Bb; pattern b;
              lazymatch goal with |- ?P b =>
                unshelve refine (enum32 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b Bb) end;
              cbv beta; vm_compute; reflexivity)
    end.
    rewrite HR. clear HR. rewrite (unsigned_lit (r - 1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit ((r - 1) * 2 ^ 5)) by lia.
    zstep. zstep. finish. f_equal. rewrite HBL. lia.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (r : Z) (x3 x4 x5 x6 x7 w11 w12 : word),
    Z.to_nat r = k -> 1 <= r <= n -> core_bitlen xs n = core_bitlen_rec xs (Z.to_nat r) ->
    w11 = Z_to_bv 64 r -> w12 = Z_to_bv 64 1 ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) w11 w12 x3 x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x22b58) fc None m (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r x3 x4 x5 x6 x7 w11 w12 Hk Hr HBL -> ->; [lia|].
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. replace (bv_swrap 32 (r + -1)) with (r - 1) by (rewrite swrap32_of_small; lia).
    zstep. zstep. zstep. chk.
    zstep. zstep. zstep. chk.
    zstep. chk.
    zstep. zstep. chk.
    destruct (nth_error xs (Z.to_nat (r - 1))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32ro_read usegs m A xs (r - 1) w _ HA NX ltac:(lia) eq_refl) as RDX.
    replace (A + (r - 1) ≪ 2) with (A + 4 * (r - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. clear RDX.
    assert (L32 : limb32 xs (Z.to_nat (r - 1)) = bv_unsigned w mod 2^32).
    { unfold limb32. rewrite (nth_error_nth _ _ _ NX). reflexivity. }
    replace (Z.to_nat r) with (S (Z.to_nat (r - 1))) in HBL by lia. cbn [core_bitlen_rec] in HBL. rewrite L32 in HBL.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as Rw.
    zstep. if_cases Kz; zify_cond Kz; rewrite ?bv_unsigned_sx32 in Kz.
    + assert (NZ : bv_unsigned w mod 2^32 <> 0) by (intros E; apply Kz; rewrite E; reflexivity).
      rewrite (proj2 (Z.eqb_neq _ _) NZ) in HBL.
      eapply (clz_walk w (bv_unsigned w mod 2^32) r); [reflexivity | exact NZ | lia | rewrite HBL; lia | f_equal; lia].
    + (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ Rw)) in Kz. rewrite Kz, Z.eqb_refl in HBL.
      zstep. if_cases K1; zify_cond K1.
      * eapply (IH (r - 1)); [lia | lia | exact HBL | f_equal; lia | reflexivity].
      * apply Bool.andb_false_iff in K1. destruct K1 as [K1|K1]; apply Z.ltb_ge in K1; [|lia].
        zstep. zstep. finish. f_equal. rewrite HBL. replace (Z.to_nat (r - 1)) with 0%nat by lia. reflexivity.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma U_mpi_core_bitlen_spec : mpi_core_bitlen_stmt usegs U_MPI_CORE_BITLEN.
Proof.
  unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN.
  intros until xs. intros HA Hn LX ALA NZA MI -> ->.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HA) as XB.
  zstep. zstep. rewrite (swrap32_signed_small (n + -1)) by lia. rewrite (swrap32_signed_small (n + 0)) by lia.
  zstep. chk.
  zstep. if_cases K0; zify_cond K0.
  - zstep. zstep. finish. f_equal. unfold core_bitlen. replace (Z.to_nat n) with 0%nat by lia. reflexivity.
  - zstep. rewrite (flag_nz A) by lia.
    eapply loop_walk with (n := n) (xs := xs) (k := Z.to_nat n) (r := n); try eassumption; try lia; try (f_equal; lia).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
