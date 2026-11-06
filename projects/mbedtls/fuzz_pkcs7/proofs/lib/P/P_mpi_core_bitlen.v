(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_bitlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MpiCoreAux.core_bitlen"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_bitlen_post"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.log2"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Mem.sx32"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.core_bitlen_rec"].


Definition P_MPI_CORE_BITLEN : Z := 0x22240.

(* [comment removed for export] *)

Definition mpi_core_bitlen_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (xs : list word) (n : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_bitlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(3.(4.$0.R10.(5.(6.O15.O14.O13.O12.R?.R>.R=.O11.O10.R<.R;.R:.R9.R8.R7.R6.R5.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R4.R3.R2.R1.)O5.(7.O15.)O4.(8.(2.&40.))O1.(9.O16.)))(3.(:.(;.$<.)O1.O1.)(3.(=.O16.O1.O1.)(3.(>.O16.O1.)(4.(2.&40.)R<.(?.&40.(10.O3.O2.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_bitlen_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_bitlen ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(11.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(12.(2.&8.))PA,$13.Pn,$13.Pxs,(14.(2.&40.))P,(15.O2.R4.R3.(16.R1.))P,(3.(17.=R3.)(17.R3.+2710.))P,(17.R4.(18.(19.(2.&40.)R3.)))P,(4.$13.(1:.R6.+4.)=)P,(1;.=R7.)P,(>.O2.R9.)P,(4.(2.&40.)R22.(?.&40.R9.))P,(4.(2.&40.)R22.(?.&40.R9.))(1<.O2.(1=.O2.R2=.R2<.R2;.R2:.R26.R25.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R>.R=.R9.R:.R<.)(5.(6.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(?.&40.O1.)R=.(8.(2.&40.))R<.(9.O2.)))")
(* [comment removed for export] *).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (A n : Z) (xs : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= Z.of_nat (length xs).
  Hypothesis XB : 0 < A /\ A + 4 * Z.of_nat (length xs) <= 2^64.
  Hypothesis AL : A mod 4 = 0.
  Hypothesis HA : bytes_at psegs m A (u32s xs).
  Hypothesis MI : mem_inv psegs m.

  Notation POST := (mpi_core_bitlen_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs n m).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L14948133805.50L15475097341.52L46933721732.52L59577446157.5000000100=00R00ZFS1A2xs1w1r1bS1A1n2xs2Hn2XB1w1r2HrS1A2xs1w". (* [comment removed for export] *)
  #[using="A Hn XB MI"] Lemma clz_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_bitlen ()) "Pw,(2.&40.)Px,$13.Pr,$13.Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pw11,(2.&40.)P,(4.$13.R9.(1:.(1>.&40.R:.)(1?.+2.+20.)))P,(20.(4.$13.R:.=))P,(3.(17.+1.R:.)(17.R:.Vn,))P,(4.$13.(10.Vxs,Vn,)(21.(21.(22.+20.(23.R;.+1.))(24.R<.))+1.))P,(4.(2.&40.)R5.(?.&40.(22.+20.R<.)))(1<.$25.(1=.$25.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vxs,Vn,Vm,)(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(26.R?.)R6.R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(?.&40.+22274.)Vfc,(8.(2.&40.))Vm,(9.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros w x r x12 x13 x14 x15 x16 x17 w11 Hx Hnz Hr HBL ->.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    do 12 zstep.
    destruct (smear_chain w x (Z.log2 x) Hx Hnz eq_refl) as [SM Bb]. cbv zeta in SM.
    rewrite SM. clear SM.
    set (b := Z.log2 x) in *. clearbody b.
    do 19 step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch get_x10 R with Z_to_bv 64 (_ - bv_unsigned ?raw) =>
        assert (HR : bv_unsigned raw = 31 - b)
          by (clear -b Bb; pattern b;
              lazymatch goal with |- ?P b =>
                unshelve refine (enum32 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b Bb) end;
              cbv beta; vm_compute; reflexivity)
      end end.
    rewrite HR. clear HR. rewrite (unsigned_lit (32 * r)) by lia.
    zstep. finish. f_equal. rewrite HBL. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L20378331621.55L23917391152.55L26773890077.53L29010565666.49L31889232343.55L42468625771.53L44661166086.54L51683658162.51L54425554183.52L55298092921.48L56834433586.55L58491786581.48L58829635818.56L59164244479.56L59308628179.46L59308628179.49L66149323318.44L67687606069.55L8670880585.48 00000?00T00i01A01X01g02404404D04\04k05805S05n06:06U06h07707OS1A2xs1k1r2Hk1wS1A2xs2XB1k1r2Hk1w2K1S1A2xs2XB1k1r2Hk2K11wS1A1n2xs2Ln2XB1k1r2Hk2HrS1A1n2xs1k1r2Hk2Hr1w2K1S1A2xs1k1r2Hk1wS1A2xs1k1r2HkS2ra2sp2gp2tp2t02t12t22s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1A1n2xs2Ln2XB1k1r3x103x143x153x163x172Hk2Hr2K12NXS1A2xs1k1r2Hk2K1S1A1n2xs2Hn2XB1k1r2Hk2HrS1A2xs1k1r2Hk1wS1A2xs1k1r2HkS1A1n2xs2XB1k1r2Hk1w3HBL2K1S1A1n2xs1k1r2Hk2Hr1w3HBL2K1S1A2xs2Hk2K0S1A1n2xs2Ln2XB1k1r2Hk2Hr2K0S1A1n2xs2XB1r2Hk2HrS1A2xs1k1r2Hk1wS1A1n2xs2Ln2XB1k1r2Hk2Hr". (* [comment removed for export] *)
  #[using="Hn Ln XB HA MI"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_bitlen ()) "Pk,$27.Pr,$13.Px10,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pw11,(2.&40.)Pw12,(2.&40.)Pw13,(2.&40.)P,(4.$27.(28.R9.)R:.)P,(3.(17.=R:.)(17.R:.Vn,))P,(4.$13.(10.Vxs,Vn,)(29.Vxs,(28.R;.)))P,(4.(2.&40.)R6.(?.&40.(21.(22.+20.R<.)+20.)))P,(4.(2.&40.)R6.(?.&40.(21.R=.+1.)))P,(4.(2.&40.)R6.(?.&40.(23.(21.VA,(22.+4.R>.))+4.)))(1<.$25.(1=.$25.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vxs,Vn,Vm,)(5.(6.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,R>.R9.R8.R7.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(?.&40.+2225<.)Vfc,(8.(2.&40.))Vm,(9.$25.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r x10 x14 x15 x16 x17 w11 w12 w13 Hk Hr HBL -> -> ->.
    - assert (r = 0) by lia. subst r.
      pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
      zstep. change (bv_swrap 32 (0 + 1 + -1)) with 0.
      zstep. if_cases K0; zify_cond K0.
      + zstep. zstep. finish. f_equal. rewrite HBL. reflexivity.
      + exfalso. lia.
    - pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
      zstep. replace (bv_swrap 32 (r + 1 + -1)) with r by (rewrite swrap32_of_small; lia).
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in * by lia; lia|].
      destruct (nth_error xs (Z.to_nat (r - 1))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
      pose proof (u32ro_read psegs m A xs (r - 1) w _ HA NX ltac:(lia) eq_refl) as RDX.
      zstep. clear RDX. zstep. zstep.
      assert (L32 : limb32 xs (Z.to_nat (r - 1)) = bv_unsigned w mod 2^32).
      { unfold limb32. rewrite (nth_error_nth _ _ _ NX). reflexivity. }
      replace (Z.to_nat r) with (S (Z.to_nat (r - 1))) in HBL by lia. cbn [core_bitlen_rec] in HBL. rewrite L32 in HBL.
      pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as Rw.
      zstep. if_cases Kz; zify_cond Kz; rewrite ?bv_unsigned_sx32 in Kz.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_zero_iff _ Rw)) in Kz. rewrite Kz, Z.eqb_refl in HBL.
        eapply (IH (r - 1)); [lia | lia | exact HBL | f_equal; lia | f_equal; lia | f_equal; lia].
      + assert (NZ : bv_unsigned w mod 2^32 <> 0) by (intros E; apply Kz; rewrite E; reflexivity).
        rewrite (proj2 (Z.eqb_neq _ _) NZ) in HBL.
        eapply (clz_walk w (bv_unsigned w mod 2^32) r); [reflexivity | exact NZ | lia | rewrite HBL; lia | f_equal; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L11616597409.44L1169170692.44 L17913333467.44L18873760060.44L18926491590.44L22331633159.44L25960979700.44L3227145185.44 L44015429788.44L44301304300.44L47040096957.44L53395330156.44L58304872257.44L58797223019.44L60194516225.44L61929490848.44L7059124976.44 00000100200300900?00@00H00U00[00\00k01101901D01L01W01_FFFS1A2xsS1A2xsFS1A1n2xsS1A2xs3NZA2XBS1A2xsFS1A1n2xs2Hn3NZAS1A2xsS1A1n2xsS1A1n2xs2HnS1A1n2xsS1A1n2xs2HnS1A1n2xs". (* [comment removed for export] *)
Lemma P_mpi_core_bitlen_spec : mpi_core_bitlen_stmt psegs P_MPI_CORE_BITLEN.
Proof.
  unfold mpi_core_bitlen_stmt, P_MPI_CORE_BITLEN.
  intros until xs. intros HA Hn LX ALA NZA MI -> ->.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (u32ro_bound _ _ _ _ HA) as XB.
  do 7 zstep.
  rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^27) with 134217728. change (2^30) with 1073741824.
  rewrite (Z.mod_small (n * 4294967296)) by lia.
  replace (n * 4294967296 / 134217728) with (32 * n)
    by (replace (n * 4294967296) with (32 * n * 134217728) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace (n * 4294967296 / 1073741824) with (4 * n)
    by (replace (n * 4294967296) with (4 * n * 1073741824) by lia; rewrite Z.div_mul by lia; reflexivity).
  eapply loop_walk with (n := n) (xs := xs) (k := Z.to_nat n) (r := n); try eassumption; try lia; try (f_equal; lia).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
