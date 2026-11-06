(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_shift_r () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_SHIFT_R_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_shift_r_post"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.Lists.List.nth_error"; "OSSVerify.KrLib.Lib.MpiCoreAux.lseg"; "OSSVerify.KrLib.Lib.MpiCoreAux.w32"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"].


Definition P_MPI_CORE_SHIFT_R : Z := 0x2272c.
Definition MPI_CORE_SHIFT_R_STACK : Z := 32.

Definition mpi_core_shift_r_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cnt : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O19.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O6.(11.O6.(12.+4.O5.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O17.)$15.)(14.&40.O17.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O19.O1.R2.)(5.(18.O19.R2.)(5.(19.O19.R2.O6.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O5.)R1.)(1<.(2.&40.)(1=.O5.)O3.))(5.(6.$?.(1>.R1.O5.)(1?.(1>.O3.O5.)(20.+2.O4.)))(21.O19.R2.O2.(14.&40.O17.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_shift_r_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.Pn,$?.Pcnt,$?.Plo,$?.Pxs,(4.(2.&40.))P,(19.O2.R6.R5.R1.)P,(5.(23.+1.R5.)(23.R5.+2710.))P,(23.R6.(24.(1;.(2.&40.)R3.)))P,(5.(23.=R6.)(25.R6.(20.+2.+40.)))P,(6.$?.(26.R9.+4.)=)P,(25.=R:.)P,(21.O2.R<.R8.(14.&40.R2<.))P,(23.R9.(13.(14.&40.R2=.)$15.))P,(6.$?.(26.(14.&40.R2>.)+10.)=)P,(27.(23.(11.R>.(12.+4.(24.(1;.(2.&40.)R:.))))R;.)(23.(14.&40.R2?.)R>.))P,(18.O2.R10.)P,(6.$?.(26.(14.&40.R32.)+2.)=)P,(6.(2.&40.)R2:.(28.&40.R11.))P,(6.(2.&40.)R2:.(28.&40.R11.))P,(6.(2.&40.)R2:.(28.&40.R11.))(29.O2.(2:.O2.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R14.R13.R12.R10.R11.R15.)(7.(8.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(28.&40.O1.)R16.(:.(2.&40.))R15.(;.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L12158135620.7L12985146626.7L14736140061.7L20757219225.7L21228278198.7L28210021617.9L49721060961.9L58737526686.700000900B00N00Z00i01701E01QS2ys1n2v0S2ys1n2v0S2ys1n2v02HvS2ys1n2v02HvS2ys1n2v02Hv2HlS2ys1n2v01k2HkS2ys1n2v01k2HkS2ys1n2v02Hv". (* [comment removed for export] *)
Lemma shr_phase1_value : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pxs0,(4.(2.&40.))Pys,(4.(2.&40.))Pn,$?.Pv0,$?.P,(5.(23.+1.R1.)(23.R1.R2.))P,(23.R3.(24.(1;.(2.&40.)R4.)))P,Pq,$1:.P,(2;.R1.(1=.(13.R5.R4.)))(6.$?.(2<.R7.R2.)(2<.R8.(2=.R2.(1=.R5.))))(6.$?.(1>.(2>.(2.&40.)(2?.(2.&40.)(1=.(13.R5.R4.))R6.)(2>.(2.&40.)(30.(2.&40.)(28.&40.=)(1=.R4.))(1<.(2.&40.)(1=.R5.)R6.)))R5.)(1?.(1>.R7.R5.)(20.+2.(12.+20.R4.))))")
(* [comment removed for export] *).
Proof.
  intros xs0 ys n v0 Hv Hl HP.
  rewrite (lval_split _ (n - v0) n) by lia. unfold lseg.
  rewrite skipn_app, firstn_length. rewrite (skipn_all2 (firstn _ ys)) by (rewrite firstn_length; lia).
  replace (Z.to_nat (n - v0) - _)%nat with 0%nat by lia. rewrite skipn_O. cbn [app].
  rewrite lval_repeat0_app by lia. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite lval_div_limbs by lia. unfold lseg.
  transitivity (lval ys (n - v0)).
  { apply lval_ext. rewrite firstn_app, firstn_firstn, firstn_length. replace (Nat.min _ _) with (Z.to_nat (n - v0)) by lia.
    replace (Z.to_nat (n - v0) - _)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r. }
  apply lval_ext_limb32. intros k Hk. rewrite HP by lia. unfold limb32. rewrite nth_skipn. f_equal. f_equal. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Walk.
  Variables (ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 s2 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n cnt v0 v1 lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 1 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis Hcnt : 0 <= cnt < 2^64.
  Hypothesis Ecnt : cnt = 32 * v0 + v1.
  Hypothesis Rv : 0 <= v0 /\ 0 <= v1 < 32.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 32.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Notation POST := (mpi_core_shift_r_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cnt xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L39939554818.68L41564619544.6700000M00dS2ra2sp1n3cnt2lo3xs02LO2ys2LXS2ra2sp1n3cnt3xs02ys2LX". (* [comment removed for export] *)
  #[using="LO"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pys,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxs0_,(2.&40.)Pxs1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(19.$31.R14.VX,R15.)P,(6.$1:.(1;.(2.&40.)R16.)(1;.(2.&40.)Vxs0,))P,(6.(4.(2.&40.))(1<.(2.&40.)(1=.Vn,)R17.)(1<.(2.&40.)(1=.Vn,)Vxs0,))P,(6.$?.(1>.R18.Vn,)(1?.(1>.Vxs0,Vn,)(20.+2.Vcnt,)))P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+20.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R18.)P,(17.$31.Vm,R19.)P,(18.$31.R1:.)P,(21.$31.R1;.Vlo,(11.(14.&40.Vsp,)-20.))P,(32.$31.R1<.(11.(14.&40.Vsp,)-20.)(=.$33.(34.Vs2,)(=.$33.(34.Vs1,)(=.$33.(34.Vs0,)(=.$33.(34.Vra,)(16.$33.))))))(29.$31.(2:.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R1<.(28.&40.(11.(14.&40.Vsp,)-20.))Vgp,Vtp,R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(28.&40.+22818.)Vfc,(:.(2.&40.))R1=.(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HX LX TX VX MU WM MI ST FR.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish. 1: exact HX. all: assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section WithZs.
    (* [comment removed for export] *)
    Variable zs : list word.
    Hypothesis LZ : length zs = length xs0.
    Hypothesis TZ : skipn (Z.to_nat n) zs = skipn (Z.to_nat n) xs0.
    Hypothesis VZ : lval zs n / 2^v1 = lval xs0 n / 2^cnt.

  Section Phase2.
    Hypothesis Hv1 : 0 < v1 < 32.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L14948245562.83L15364881305.87L17297232509.87L19594427422.89L21007718489.89L22798285110.83L27329419576.87L32195216017.85L32867407698.87L3432239224.84 L34328786283.89L3434386669.83 L37444735563.88L40567854061.86L40568293785.87L41249981698.83L41415742316.88L43936164022.88L44960413355.88L4988732769.87 L50467811335.91L50487188423.89L51715542588.91L53380753436.89L53768783725.87L54397307819.87L54397412855.89L54987412219.87L59798865670.89L60719942178.87L60720112766.89L62068247658.83L62965564504.90L62965564766.88L65035946358.88L65035946358.89L66351106951.89L66351146459.87L66806791447.87L67985703674.87L7037817584.82 L7037949946.79 L7572214554.87 L8371044112.89 L8638976234.87 00000100_01J02I03403`04J05U06i0810920::0:h0;i0<m0=V0>>0>h0@@0@n0BJ0C20C30C`0DK0E=0Eo0Fk0GS0H>0Hi0IU0K70LY0Mk0O=0Oh0PS0QW0R?0UG0X60Y80Z40Z\FS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2Hi2LX1w2KlS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2Hi2LX1wS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C2Hk2Hi2LX2CB1w2WR2KlS2ra1n3cnt2v13xs02Hn2zs2LZ1k1i2ys1C2Hk2LX1wS2ra1n3cnt2v02v13xs02Rv2zs2LZ1k1i2ys1C2Hk2LXS2ra1X1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1wS2ra1n3cnt2v02v12lx3xs02Hn2Ln2L04Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RBS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2XB4Hcnt2Rv3SPR2LO2zs2LZ1k1i2ys1C2Hk2Hi2LX2CB1w2WRS2ra1n3cnt2v02v12lx3xs02Ln2L04Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RBS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C2Hk2Hi2LX2CB1w2WR1q2HqS2ra1n3cnt2v02v12lx3xs02Ln2L04Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RBS2ra1n3cnt2v02v13xs02Rv2zs2LZ1k1i2ys1C2Hk2LX1wS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1wS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2Hi2LXS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1wS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1w1HS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln4Hcnt2Rv2LO2SX2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2Hi2LX1w2KlS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln4Hcnt2Rv2LO2SX2zs2LZ1k1i2ys3r0w1C1R2Hk2Hi2LX2HC2CB2RB1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1wFS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1w1q2HqS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2Hi2LX1wS2ra1n3cnt2v02v13xs02Rv2zs2LZ3Hv11k1i2ys1C2Hk2LX1wS2ra1n3cnt2v02v13xs02Rv2zs2LZ3Hv11k1i2ys1C2Hk2LX1wS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C2Hk2Hi2LX2CB1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1wS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1w2WRS2ra1n3cnt2v02v13xs02Rv2zs2LZ1k1i2ys1C2Hk2LXS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt2Rv3SPR2LO2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WR5HBarrS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt2Rv3SPR2LO2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WR5HBarrS2ra1X1n3cnt2v02v12lx3xs02XB4Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WR5HBarrS2ra1X1n3cnt2v02v12lx3xs02XB4Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WR5HBarrS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX2CB1wS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX2CB1wS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C1R2Hk2Hi2LX2HC2CB2RB1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1wS2ra2sp2gp2tp2s32s42s52s62s72s82s93s103s112s02s12s21F2fc1m1X1n3cnt2v02v12lx2lo3xs02Hn2Ln2L04Hcnt2Rv2zs2LZ1k1i2ys3r0w1C1R2mm3xra3xt03xt13xt23xs13xa43xa53xa63xa73xs23xt33xt43xt53xt62Hk2Hi2LX2HC2CB2RB2NXS2ra2sp2gp2tp2s32s42s52s62s72s82s93s103s112s02s12s21F2fc1m1X1n3cnt2v02v12lo3xs04Hcnt2Rv2zs2LZ1i2ys3r0w1C2mm3xra3xt03xt13xt23xs13xa43xa53xa63xa73xs23xt33xt43xt53xt62Hk2Hi2LX2CBS2ra1n3cnt2v02v13xs02Hn4Hcnt2Rv2zs2LZ1k1i2ys1C2Hk2Hi2LX2CB1w2WR2KlS2ra1n3cnt2v02v13xs04Hcnt2Rv2zs2LZ1k1i2ys1C2Hk2Hi2LX2CB1w2WRS2ra1n3cnt2v13xs02zs2LZ1k1i2ys1C2Hk2LX1w". (* [comment removed for export] *)
    #[using="v0 lx Hn Ln L0 XB Hcnt Rv SPR LO SX LZ VZ Hv1"] Lemma loop2_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pk,$1:.Pi,$?.Pys,(4.(2.&40.))Pr0w,(2.&40.)PC,$?.PR,$?.Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxs1,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwi,(2.&40.)Pwp,(2.&40.)P,(6.$1:.(1=.R16.)R17.)P,(5.(23.+1.R17.)(23.R17.Vn,))P,(6.(2.&40.)R4.(28.&40.R18.))P,(6.(2.&40.)R4.(28.&40.(11.VX,(12.+4.(13.R19.+1.)))))P,(19.$31.R15.VX,R19.)P,(6.$1:.(1;.(2.&40.)R1:.)(1;.(2.&40.)Vxs0,))P,Pq,$1:.P,(2;.R1.(1=.R1=.))(6.(3.(2.&40.))(35.(2.&40.)R1=.R2.)(35.(2.&40.)Vzs,R2.))P,(6.(4.(2.&40.))(1<.(2.&40.)(1=.Vn,)R1<.)(1<.(2.&40.)(1=.Vn,)Vxs0,))P,(6.$?.(36.R1=.R1>.Vn,)(1?.(36.Vzs,R1>.Vn,)(20.+2.Vv1,)))P,(6.$?.(36.Vzs,R1?.Vn,)(11.R1<.(12.(20.+2.+20.)R1;.)))P,(5.(23.=R1=.)(25.R1=.(20.+2.+20.)))P,(23.=R1=.)P,(6.$?.(37.R20.)(12.(26.R1?.(20.+2.Vv1,))(20.+2.(13.+20.Vv1,))))P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+20.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R1>.)P,(17.$31.Vm,R1?.)P,(18.$31.R20.)P,(21.$31.R21.Vlo,(11.(14.&40.Vsp,)-20.))P,(32.$31.R22.(11.(14.&40.Vsp,)-20.)(=.$33.(34.Vs2,)(=.$33.(34.Vs1,)(=.$33.(34.Vs0,)(=.$33.(34.Vra,)(16.$33.))))))(29.$31.(2:.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R22.(28.&40.(11.(14.&40.Vsp,)-20.))Vgp,Vtp,R21.R20.R1?.(28.&40.Vv1,)R1>.(28.&40.(13.+20.Vv1,))R14.R26.R13.R1=.R1<.R1;.R1:.R19.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R18.R17.R16.R15.)VF,(28.&40.+227?4.)Vfc,(:.(2.&40.))R23.(;.$31.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i ys r0w C R mm xra xt0 xt1 xt2 xs1 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 wi wp
        Hk Hi -> -> HX LX FY TY INV HC CB RB HR MU WM MI ST FR; [lia|].
      destruct (nth_error ys (Z.to_nat (i - 1))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
      pose proof (u32arr_read psegs mm X ys (i - 1) w _ HX NX ltac:(lia) eq_refl) as RDX.
      zstep. clear RDX.
      zstep. zstep. zstep. zstep.
      pose proof (u32arr_store_ok psegs mm X ys (i - 1) _ HX ltac:(lia) eq_refl) as SOK.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write psegs mm X ys (i - 1) v HX ltac:(lia)) as HX';
        pose proof (limb32_upd_same ys (Z.to_nat (i - 1)) v ltac:(lia)) as VX end.
      (* [comment removed for export] *)
      assert (VW : limb32 zs (Z.to_nat (i - 1)) = w32 w).
      { apply limb32_nth_error. rewrite <- FY by lia. exact NX. }
      pose proof (w32_range w) as WR.
      rewrite (shr_limb_bits w r0w v1 (C mod 2^v1) Hv1 ltac:(apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia) HR) in VX.
      store_done. try clear HX.
      zstep. zstep. zstep.
      if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
      - (* [comment removed for export] *)
        eapply (IH (i - 1) _ _ (w32 w) (lseg zs i n));
          [ lia | lia | f_equal; lia | f_equal; lia | exact HX' | rewrite upd_length; lia
          | intros q Hq; rewrite nth_error_upd_other by lia; apply FY; lia
          | rewrite skipn_upd_lt by lia; exact TY
          | | rewrite (lseg_cons zs (i - 1) n), VW by lia; f_equal; f_equal; f_equal; lia
          | lia | pose proof (lseg_range zs i n ltac:(lia)); lia
          | apply shr_carry_bits; lia
          | exact MU | exact WM | exact MI | exact ST | exact FR ].
        rewrite (lseg_cons (upd ys (Z.to_nat (i - 1)) _) (i - 1) n) by lia. rewrite VX.
        replace (i - 1 + 1) with i by lia.
        replace (lseg (upd ys (Z.to_nat (i - 1)) _) i n) with (lseg ys i n)
          by (unfold lseg; rewrite skipn_upd_lt by lia; reflexivity).
        rewrite (lseg_cons zs (i - 1) n), VW by lia. replace (i - 1 + 1) with i by lia.
        eapply shr_step_arith; [lia | lia | lia | exact RB | exact HC | exact INV].
      - (* [comment removed for export] *)
        eapply tail_walk; [ exact HX' | rewrite upd_length; lia | rewrite skipn_upd_lt by lia; exact TY | | exact MU | exact WM | exact MI | exact ST | exact FR ].
        rewrite <- VZ. assert (Ei : i = 1) by lia.
        assert (E0 : forall ws, lval ws n = lseg ws 0 n) by (intros; unfold lseg; cbn [Z.to_nat skipn]; f_equal; lia).
        rewrite !E0. rewrite (lseg_cons (upd ys _ _) 0 n), (lseg_cons zs 0 n) by lia.
        replace (Z.to_nat (i - 1)) with (Z.to_nat 0) in VX |- * by lia. rewrite VX.
        rewrite Ei in VW, INV, HC. replace (1 - 1) with 0 in VW by lia. rewrite VW. change (0 + 1) with 1.
        replace (lseg (upd ys (Z.to_nat 0) _) 1 n) with (lseg ys 1 n) by (unfold lseg; rewrite skipn_upd_lt by lia; reflexivity).
        eapply shr_step_arith; [lia | lia | lia | exact RB | exact HC | exact INV].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Phase2.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L10066630288.68L15045134080.68L20745261266.68L220377172.67  L22798355484.68L22798355613.67L28500699844.68L37445067371.68L39541107158.68L41415942988.68L44822654247.68L54397314293.68L61929812368.68L7277684688.68 00000G00^01501U02202O02l03I03`04704Q05105K05dS2ra1n3cnt2v13xs02zs2LZS2ra1n3cnt2v13xs02zs2LZS2ra1n3cnt2v13xs02zs2LZS2ra1n3cnt2v02v13xs02Rv2zs2LZ2K1S2ra1n3cnt2v02v13xs02Rv2zs2LZS2ra1n3cnt2v02v13xs02Rv2zs2LZS2ra1n3cnt2v13xs02Hn2zs2LZ2K2S2ra1n3cnt2v02v13xs02Rv2zs2LZS2ra1n3cnt2v13xs02zs2LZS2ra1n3cnt2v13xs02zs2LZS2ra1n3cnt2v13xs02Hn2zs2LZS2ra1n3cnt2v02v13xs02Rv2zs2LZ2K1S2ra1n3cnt2v13xs02Hn2zs2LZS2ra1X1n3cnt2v13xs02zs2LZ". (* [comment removed for export] *)
    #[using="v0 lx Hn Ln L0 XB Hcnt Rv SPR LO SX LZ TZ VZ"] Lemma phase2_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxs1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(5.(23.=Vv1,)(25.Vv1,+20.))P,(19.$31.R12.VX,Vzs,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+20.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R13.)P,(17.$31.Vm,R14.)P,(18.$31.R15.)P,(21.$31.R16.Vlo,(11.(14.&40.Vsp,)-20.))P,(32.$31.R17.(11.(14.&40.Vsp,)-20.)(=.$33.(34.Vs2,)(=.$33.(34.Vs1,)(=.$33.(34.Vs0,)(=.$33.(34.Vra,)(16.$33.))))))(29.$31.(2:.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R17.(28.&40.(11.(14.&40.Vsp,)-20.))Vgp,Vtp,R16.R15.R14.(28.&40.Vv1,)R13.(28.&40.VX,)(28.&40.Vn,)R12.R11.R10.R?.R>.R=.R<.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(28.&40.+227=4.)Vfc,(:.(2.&40.))R18.(;.$31.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros Hv1 HX MU WM MI ST FR.
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      { (* [comment removed for export] *)
        eapply tail_walk; [exact HX | exact LZ | exact TZ | | exact MU | exact WM | exact MI | exact ST | exact FR].
        rewrite <- VZ. replace v1 with 0 by lia. rewrite Z.div_1_r. reflexivity. }
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      { (* [comment removed for export] *)
        eapply tail_walk; [exact HX | exact LZ | exact TZ | | exact MU | exact WM | exact MI | exact ST | exact FR].
        rewrite <- VZ. replace n with 0 by lia. rewrite !lval_0. rewrite !Z.div_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
      zstep. zstep. zstep. zstep. zstep. zstep.
      eapply (loop2_walk ltac:(lia) (Z.to_nat n) n zs (Z_to_bv 64 0) 0 0);
        [ reflexivity | lia | reflexivity | f_equal; rewrite ?Z.shiftl_mul_pow2; lia | exact HX | exact LZ
        | intros; reflexivity | exact TZ
        | rewrite lseg_empty, Z.div_0_l; [reflexivity|]; apply Z.pow_nonzero; lia
        | rewrite lseg_empty; lia | lia | lia
        | rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); reflexivity
        | exact MU | exact WM | exact MI | exact ST | exact FR ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithZs.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L11801586693.90L15270784212.64L15716106808.83L17030316504.82L18890663537.64L19143320938.72L19145353322.86L19660585441.64L19662654587.83L2211540478.73 L2211882220.71 L22700267513.92L26659923681.82L28887984738.86L32408945813.64L33621104961.84L37442983792.82L40601571469.90L41415943117.64L41418085975.82L44484923210.90L45507666326.86L4780116544.86 L51692017272.82L53519092896.71L54399455726.84L55630291447.73L57868141674.82L57902736052.64L61929812241.64L62006540601.84L63568834870.82L65575347148.82L66125982750.73L66126193932.7100000m03<03i04S05<05e06N06k07R08J09B0:@0:A0:e0;i0<M0<n0=W0=e0>@0?80?U0@;0@\0A90A\0BC0Bm0CI0C\0D@0Da0E@0FT0GhS2ra2sp1X1n2v02lx2lo3xs02Hn2Ln2LO2SX2ys3Hv01A1B2LX2K12LA2LB1CS2ra2sp2gp2tp2s32s42s52s62s72s82s93s103s112s02s12s21F2fc1m1X1n3cnt2v02v12lo3xs02ys2mm3xra3xt03xt13xt23xa33xa53xa63xa73xt33xt43xt53xt63Hv02LX2K1S2ra1n2v02lx3xs02Hn2Ln2L02ys3Hv01A1B2LX2LA2LBS2ra1n2v02lx3xs02Hn2Ln2L02ys1B2LX2K12LA2LBS2ra3cnt2v02v13xs04Hcnt4Ecnt2Rv2ys3Hv12LXS2ra1X1n2v03xs02Hn2ys3Hv01A1B2LX2K12LA2LBS2ra1X1n2v03xs02Hn2ys3Hv01A1B2LX2K12LA2LBS2ra1n2v03xs02Hn2ys3Hv02LX2K1S2ra1n2v03xs02Hn2ys3Hv01A1B2LX2K12LA2LBS2ra1n3cnt2v02v13xs02Hn4Hcnt4Ecnt2ys3Hv11A1B2LX2K12LA2LBS2ra1n3cnt2v02v13xs02Hn4Hcnt4Ecnt2ys3Hv11A1B2LX2K12LA2LBS2ra2sp1X1n2v02lx2lo3xs02Hn2Ln2LO2SX2ys3Hv01A1B2LX2LA2LB3x141HFS2ra1n2v03xs02Hn2ys3Hv01A1B2LX2LA2LBS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2XB4Hcnt4Ecnt3SPR2LO2ys3Hv03Hv12LXS2ra1n2v03xs02Hn2ys3Hv01A1B2LX2LA2LBS2ra1n2v02v13xs02Rv2ys1B2LX2LA2LBS2ra1X1n2v03xs02Hn2ys3Hv01A1B2LX2K12LA2LBS2ra3xs02ys2LXS2ra1n2v03xs02ys1B2LX2LA2LBS2ra2sp1X1n2v02lx2lo3xs02Hn2Ln2SX2ys3Hv01A1B2LX2K12LA2LBS2ra1n2v03xs02ys1A1B2LX2LA2LBS2ra1X1n2v03xs02Hn2ys3Hv01A1B2LX2LA2LBS2ra1n2v03xs02Hn2ys1B2LX2K12LA2LBS2ra1n2v03xs02ys1A1B2LX2LA2LBS2ra1n2v02v13xs02Rv2ys1A1B2LX2LA2LBS2ra1n2v03xs02Hn2ys3Hv01A1B2LX2K12LA2LBS2ra1n3cnt2v02v13xs02Hn4Ecnt2ys1B2LX2LA2LBS2ra1n2lx3xs02Hn2Ln2L02ys2LXS2ra1n3xs02Hn2ys2LXS2ra1n2v03xs02Hn2ys3Hv01A1B2LX2LA2LBS2ra1n2v03xs02Hn2ys1B2LX2K12LA2LBS2ra1n2v03xs02ys3Hv01B2LX2LA2LBS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Hn2Ln2XB4Hcnt4Ecnt3SPR2LO2ys3Hv03Hv11A1B2LX2K12LA2LBS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Hn2Ln2XB4Hcnt4Ecnt3SPR2LO2ys3Hv03Hv11A1B2LX2K12LA2LB". (* [comment removed for export] *)
  #[using="lx Hn Ln L0 XB Hcnt Ecnt Rv SPR LO SX"] Lemma after_copy_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pys,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa3,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(5.(23.+1.Vv0,)(23.Vv0,Vn,))P,(5.(23.=Vv1,)(25.Vv1,+20.))P,(19.$31.R?.VX,R10.)P,(6.$1:.(1;.(2.&40.)R11.)(1;.(2.&40.)Vxs0,))P,Pq,$1:.P,(2;.R1.(1=.(13.Vn,Vv0,)))(6.$?.(2<.R14.R2.)(2<.Vxs0,(2=.R2.(1=.Vv0,))))P,(38.(2.&40.)(1=.(13.Vn,Vv0,))R13.Vxs0,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+20.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R13.)P,(17.$31.Vm,R14.)P,(18.$31.R15.)P,(21.$31.R16.Vlo,(11.(14.&40.Vsp,)-20.))P,(32.$31.R17.(11.(14.&40.Vsp,)-20.)(=.$33.(34.Vs2,)(=.$33.(34.Vs1,)(=.$33.(34.Vs0,)(=.$33.(34.Vra,)(16.$33.))))))(29.$31.(2:.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R17.(28.&40.(11.(14.&40.Vsp,)-20.))Vgp,Vtp,R16.R15.R14.(28.&40.Vv1,)Vs1,(28.&40.VX,)(28.&40.Vn,)(28.&40.(13.Vn,Vv0,))R13.(28.&40.Vv0,)R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(28.&40.+227:8.)Vfc,(:.(2.&40.))R18.(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros Hv0 Hv1 HX LX HP FS MU WM MI ST FR.
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [lia|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
    (* [comment removed for export] *)
    ddestruct (split3 ys (Z.to_nat (n - v0)) (Z.to_nat n) ltac:(lia) ltac:(lia)) as (EY & LA & LB).
    set (A := firstn (Z.to_nat (n - v0)) ys) in *. set (B := firstn _ (skipn _ ys)) in *. set (C := skipn (Z.to_nat n) ys) in *.
    rewrite EY in HX. apply u32arr_app in HX. destruct HX as [HXA HX]. apply u32arr_app in HX. destruct HX as [HXB HXC].
    rewrite LA in HXB, HXC. rewrite LB in HXC. apply u32arr_cells in HXB. rewrite LB in HXB.
    replace (X + 4 * Z.of_nat (Z.to_nat (n - v0))) with (X + (n - v0) * 4) in HXB, HXC by lia.
    pose proof P_memset_spec as SP. unfold memset_stmt in SP.
    eapply evt_cut.
    { eapply SP; [|exact MI]. rewrite !unsigned_lit by lia.
      replace (Z.to_nat (v0 * 4)) with (4 * (Z.to_nat n - Z.to_nat (n - v0)))%nat by lia. exact HXB. }
    clear SP HXB. unfold memset_post. rewrite !unsigned_lit by lia.
    post_call psegs mm.
    (* [comment removed for export] *)
    match goal with H : rw_cells psegs ?m2 (X + (n - v0) * 4) [CB _ _] |- _ =>
      apply (u32arr_of_cells psegs m2 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat v0))) in H;
      [| rewrite u32s_repeat0; replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 by reflexivity; f_equal; lia ];
      rename H into HXB
    end.
    lazymatch type of HXB with u32arr _ ?m2 _ _ =>
      assert (HX' : u32arr psegs m2 X (A ++ (repeat (Z_to_bv 64 0) (Z.to_nat v0) ++ C))) end.
    { apply u32arr_app. split; [exact HXA|]. rewrite LA. apply u32arr_app. split.
      - replace (X + 4 * Z.of_nat (Z.to_nat (n - v0))) with (X + (n - v0) * 4) by lia. exact HXB.
      - rewrite repeat_length. replace (X + 4 * Z.of_nat (Z.to_nat (n - v0)) + 4 * Z.of_nat (Z.to_nat v0)) with (X + (n - v0) * 4 + 4 * Z.of_nat (Z.to_nat n - Z.to_nat (n - v0))) by lia. exact HXC. }
    clear HXA HXB HXC.
    zstep. zstep.
    eapply (phase2_walk (A ++ (repeat (Z_to_bv 64 0) (Z.to_nat v0) ++ C)));
      [ | | | lia | exact HX' | assumption | assumption | assumption | assumption | assumption ].
    - rewrite !app_length, repeat_length, LA. subst C. rewrite skipn_length. lia.
    - rewrite app_assoc, skipn_app, skipn_all2 by (rewrite app_length, repeat_length, LA; lia).
      rewrite app_length, repeat_length, LA. replace (_ - _)%nat with 0%nat by lia. rewrite skipn_O.
      subst C. apply same_from_skipn; [| exact LX]. eapply same_from_weaken; [exact FS | lia].
    - subst A C. rewrite (shr_phase1_value xs0 ys n v0) by first [lia | exact HP].
      rewrite Z.div_div, <- Z.pow_add_r by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonneg; lia).
      f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L12357732928.71L13714651078.71L14983703935.66L19829503675.73L28484053877.71L30201245471.69L31121636256.71L31838202207.71L33045003426.71L35900490670.71L43896037668.71L44960413355.72L45413819155.69L50467811335.75L51139067655.67L51715542588.75L52067437258.71L54397307819.71L54987412219.71L56313436524.63L59114351891.73L62704041383.71L62965564504.74L62965564766.72L64757813392.72L64757813392.73L65067292645.67L65069863792.68L65577466249.7100000M00j03<03^04K04l05L06E06a07?07_08o09K0:B0:c0:d0;n0<N0<k0>o0?Q0?k0A?0BS0C80C]0DG0E10EUS2ra1n2v03xs01k1j2ys2Hk2Hj2LXS2ra1n2v03xs01k1j2ys2Hk2Hj2LXS2ra2sp2gp2tp2s32s42s52s62s72s82s93s103s112s02s12s21F2fc1m1X1n3cnt2v02v12lx2lo3xs02Ln2L01k1j2ys2mm3xra3xt03xt13xt23xt33xt43xt53xt62Hk2Hj3Hv02LX2NXS2ra1n2v03xs01k1j2ys2Hk2LX1q2Hq2n0S2ra1n2v02lx3xs02Ln2L01k1j2ys2Hk2Hj3Hv02LX2HqS2ra1n2v03xs01k1j2ys2Hk2Hj3Hv02LXS2ra1n2v03xs01k1j2ys2Hk2Hj2LX2KlS2ra1n3cnt2v02v13xs04Hcnt4Ecnt1k1j2ys2Hk2Hj3Hv03Hv12LX2HqS2ra1X1n2v03xs01k1j2ys2Hk2LXS2ra1n2v03xs01k1j2ys2Hk3Hv02LXS2ra1n2v03xs01k1j2ys2Hk2Hj2LX2KlS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Hn2Ln2L04Hcnt4Ecnt2LO2SX1k1j2ys2Hk2Hj3Hv03Hv12LXS2ra1X1n2v03xs01k1j2ys2Hk2LXS2ra2sp1X1n2v02lx2lo3xs02Ln2LO2SX1k1j2ys2Hk2Hj3Hv02LX1wS2ra1n2v03xs01k1j2ys2Hk2Hj3Hv02LXFS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2XB4Hcnt4Ecnt3SPR2LO1k1j2ys2Hk2Hj3Hv12LXS2ra1n2v02v13xs02Rv1k1j2ys2Hk2LXS2ra1n2v03xs01k1j2ys2Hk2Hj2LXS2ra2sp2gp2tp2s32s42s52s62s72s82s93s103s112s02s12s21F2fc1m1X1n3cnt2v02v12lo3xs01j2ys2mm3xra3xt03xt13xt23xa73xt33xt43xt53xt62Hk2Hj2LXS2ra1n2v03xs01k1j2ys2Hk2LX1q2Hq2n0S2ra1n2v03xs01k1j2ys2Hk2LXS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt3SPR2LO1k1j2ys2Hk2Hj3Hv03Hv12LX5HBarrS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt3SPR2LO1k1j2ys2Hk2Hj3Hv03Hv12LX5HBarrS2ra1X1n2v02lx3xs02XB1k1j2ys2Hk2Hj2LXS2ra1X1n2v02lx3xs02XB1k1j2ys2Hk2Hj2LXS2ra1n2v02lx3xs02Ln2L01k1j2ys2Hk2Hj3Hv02LXS2ra1n2v02lx3xs02Ln2L01k1j2ys2Hk2Hj3Hv02LXS2ra1n2v03xs01k1j2ys2Hk2Hj3Hv02LX2Kl". (* [comment removed for export] *)
  #[using="lx Hn Ln L0 XB Hcnt Ecnt Rv SPR LO SX"] Lemma loop1_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pk,$1:.Pj,$?.Pys,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwp,(2.&40.)Pwc,(2.&40.)Pwv,(2.&40.)P,(6.$1:.(1=.(13.(13.Vn,Vv0,)R?.))R10.)P,(5.(23.=R10.)(25.R10.(13.Vn,Vv0,)))P,(23.+1.Vv0,)P,(5.(23.=Vv1,)(25.Vv1,+20.))P,(6.(2.&40.)R7.(28.&40.(11.VX,(12.+4.R13.))))P,(6.(2.&40.)R7.(28.&40.(13.(13.Vn,Vv0,)R14.)))P,(6.(2.&40.)R7.(28.&40.(12.+4.Vv0,)))P,(19.$31.R14.VX,R15.)P,(6.$1:.(1;.(2.&40.)R16.)(1;.(2.&40.)Vxs0,))P,Pq,$1:.P,(2;.R1.(1=.R19.))(6.$?.(2<.R19.R2.)(2<.Vxs0,(2=.R2.(1=.Vv0,))))P,(38.(2.&40.)(1=.R19.)R18.Vxs0,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+20.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R18.)P,(17.$31.Vm,R19.)P,(18.$31.R1:.)P,(21.$31.R1;.Vlo,(11.(14.&40.Vsp,)-20.))P,(32.$31.R1<.(11.(14.&40.Vsp,)-20.)(=.$33.(34.Vs2,)(=.$33.(34.Vs1,)(=.$33.(34.Vs0,)(=.$33.(34.Vra,)(16.$33.))))))(29.$31.(2:.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R1<.(28.&40.(11.(14.&40.Vsp,)-20.))Vgp,Vtp,R1;.R1:.R19.(28.&40.Vv1,)Vs1,(28.&40.VX,)(28.&40.Vn,)(28.&40.(13.Vn,Vv0,))R11.(28.&40.Vv0,)R13.R12.R18.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(28.&40.+22790.)Vfc,(:.(2.&40.))R1=.(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros j ys mm xra xt0 xt1 xt2 xa7 xt3 xt4 xt5 xt6 wp wc wv Hk Hj Hv0 Hv1 -> -> -> HX LX HP FS MU WM MI ST FR; [lia|].
    zstep.
    destruct (nth_error ys (Z.to_nat (j + v0))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32arr_read psegs mm X ys (j + v0) w _ HX NX ltac:(lia) ltac:(f_equal; lia)) as RDX.
    zstep. clear RDX.
    zstep.
    pose proof (u32arr_store_ok psegs mm X ys j _ HX ltac:(lia) eq_refl) as SOK.
    zstep.
    pose proof (u32arr_write psegs mm X ys j (sx32 w) HX ltac:(lia)) as HX'.
    (* [comment removed for export] *)
    assert (VW : limb32 xs0 (Z.to_nat (j + v0)) = w32 w).
    { apply limb32_nth_error. rewrite <- (FS (Z.to_nat (j + v0))) by lia. exact NX. }
    assert (HP' : forall q, (q < S (Z.to_nat j))%nat -> limb32 (upd ys (Z.to_nat j) (sx32 w)) q = limb32 xs0 (q + Z.to_nat v0)%nat).
    { intros q Hq. destruct (Nat.eq_dec q (Z.to_nat j)) as [->|].
      - rewrite limb32_upd_same, w32_of_sx32, <- VW by lia. f_equal. lia.
      - rewrite limb32_upd_other by lia. apply HP. lia. }
    pose proof (same_from_upd _ _ _ (sx32 w) FS) as FS'.
    store_done. try clear HX.
    zstep. zstep.
    if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    - eapply (IH (j + 1)); [lia | lia | lia | lia | f_equal; lia | f_equal; lia | reflexivity | exact HX' | rewrite upd_length; lia
        | replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact HP'
        | replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact FS'
        | assumption | assumption | assumption | assumption | assumption ].
    - eapply (after_copy_walk (upd ys (Z.to_nat j) (sx32 w))); [lia | lia | exact HX' | rewrite upd_length; lia
        | replace (Z.to_nat (n - v0)) with (S (Z.to_nat j)) by lia; exact HP'
        | replace (Z.to_nat (n - v0)) with (S (Z.to_nat j)) by lia; exact FS'
        | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L18878064619.62L18890663664.63L19657665847.63L20121506554.63L33083793023.63L35900501105.61L35900501232.63L41415942988.63L43204974290.61L54397314164.61L54397314293.63L60288955564.63L61929812368.63L61933957259.62L65577457367.63L68464322328.63L7393588011.65 00000S01601C01W01b02@02P02X03>03O03`03j04704D04Z04g05;S2ra3cnt2v02v13xs04Hcnt4Ecnt2Rv3Hv1S2ra3cnt2v02v13xs04Hcnt4Ecnt2Rv3Hv1S2ra1n2v03xs0S2ra1n2v03xs03Hv02K2S2ra2v03xs0S2ra3cnt2v02v13xs04Ecnt3Hv12K1S2ra2v03xs04Hv0'S2ra3xs0S2ra3cnt2v02v13xs04Hcnt4Ecnt2Rv3Hv12K1S2ra2v02v13xs02RvS2ra2v02v13xs02RvS2ra1X3xs0S2ra1n3xs02HnS2ra1n3xs02HnS2ra1n2v03xs03Hv04Hv0'S2ra1n2v03xs0S2ra1n2v03xs02K21q1H". (* [comment removed for export] *)
  #[using="lx Hn Ln L0 XB Hcnt Ecnt Rv SPR LO SX"] Lemma phase1_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa3,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(23.Vv0,Vn,)P,(27.(25.Vv0,Vn,)(6.$?.Vv1,=))P,(5.(23.=Vv1,)(25.Vv1,+20.))P,(19.$31.R10.VX,Vxs0,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+20.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R11.)P,(17.$31.Vm,R12.)P,(18.$31.R13.)P,(21.$31.R14.Vlo,(11.(14.&40.Vsp,)-20.))P,(32.$31.R15.(11.(14.&40.Vsp,)-20.)(=.$33.(34.Vs2,)(=.$33.(34.Vs1,)(=.$33.(34.Vs0,)(=.$33.(34.Vra,)(16.$33.))))))(29.$31.(2:.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R15.(28.&40.(11.(14.&40.Vsp,)-20.))Vgp,Vtp,R14.R13.R12.(28.&40.Vv1,)Vs1,(28.&40.VX,)(28.&40.Vn,)(28.&40.Vcnt,)R11.(28.&40.Vv0,)R10.R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(28.&40.+22774.)Vfc,(:.(2.&40.))R16.(;.$31.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros Hv0 Hdis Hv1 HX MU WM MI ST FR.
    zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { (* [comment removed for export] *)
      eapply (phase2_walk xs0); [reflexivity | reflexivity | | lia | exact HX | assumption | assumption | assumption | assumption | assumption ].
      f_equal. f_equal. lia. }
    assert (Hv0' : 1 <= v0) by lia.
    zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { (* [comment removed for export] *)
      eapply (after_copy_walk xs0); [lia | lia | exact HX | reflexivity | intros; lia | apply same_from_refl
        | assumption | assumption | assumption | assumption | assumption ]. }
    zstep. zstep. zstep.
    eapply (loop1_walk (Z.to_nat (n - v0)) 0 xs0); [lia | lia | lia | lia | f_equal; lia | f_equal; lia
      | f_equal; rewrite Z.shiftl_mul_pow2; lia | exact HX | reflexivity
      | intros; lia | apply same_from_refl | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00o0?L15736436871.75L15736436871.77L16764811524.59L16764811524.61L16764989462.61L16764989462.63L17976596318.74L17976596318.76L22700267513.80L22700267513.82L2427055993.75 L2427055993.77 L24356466231.60L24695273878.61L24695273878.63L25709326372.74L25709326372.76L29317478364.57L34290115814.56L36459696189.59L36459697082.60L37723014267.59L37723015164.60L39939624357.60L39939624611.58L41415807082.57L41415807082.59L41418085975.75L41418085975.77L41432194434.75L41432194434.77L41564619544.57L41564619544.59L42585448788.59L42585448788.60L43059692603.54L44015103505.53L44015210541.58L44015210668.59L45035744.75   L45035744.77   L46598470749.78L46598470749.80L46608153814.52L49582498545.75L49582498545.77L5259869074.61 L5259869074.63 L5259981440.59 L5259981440.61 L53519092896.59L53519092896.61L56529753542.60L56529753665.59L58428508945.58L58428508945.60L59906210512.74L59906210512.76L61929812241.58L61929812368.59L61929812503.60L64294415842.78L64294415842.8000000X01@01k02V03A03l04Q05605U06:06V07207F07k08P08i09B09V09j0:I0:e0;A0;]0<70<Q0<e0=90=R0=k0>D0>]0?10?E0@B0AH0Ab0B60BJ0B^0CI0D40DY0E>0EN0F30FX0GC0Gn0HY0ID0I]0J60JQ0Jl0KQ0L60LO0Lh0MA0MZ0N30Na0OUS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2DM2K12LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2DM2K22LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2DM2K12LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2DM2K22LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LB3x141HS2ra2sp1X1n3cnt2xs3SPR2MB2K32LB3x141HS2ra2sp1X1n3cnt2xs2Hn3SPR2LBS2ra2sp1X1n3cnt2xs2Hn3SPR2LBS2ra2sp1X3cnt2xs3SPRS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X1n3cnt2xs3SPR2MB2K12K2S2ra2sp1X1n3cnt2xs3SPR2MB2K3S2ra2sp1X3cnt2xs4Hcnt3SPR2MBS2ra2sp1X3cnt2xs4Hcnt3SPR2MBS2ra2sp1X3cnt2lo2xs2LO3SPRS2ra2sp1X3cnt2lo2xs2LO3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2lo2xs4Hcnt3ALX3NZX2LO3SPA2SX3SPR2HB5Ha_st5Hl_stS2ra2sp2s01X3cnt2lo2xs4Hcnt3ALX3NZX2LO3SPA2SX3SPR2HB5Ha_st5Hl_st2s12s2S2ra2sp1X3cnt2lo2xs2LO3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2DM2K12LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2DM2K22LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X2xs3SPRS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn4Hcnt3NZX3SPR2LBS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX2XB3SPR2LBS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX2XB3SPR2LBS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX2XB3SPR2LBS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX2XB3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X3cnt2xs3NZX2XB3SPRS2ra2sp1X3cnt2xs3NZX2XB3SPRS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX3SPRS2ra2sp1X1n3cnt2xs2Hn2LX4Hcnt3NZX3SPRS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs3SPR2LBS2ra2sp1X1n3cnt2xs2Hn3SPRS2ra2sp1X1n3cnt2xs2Hn3SPRS2ra2sp1X1n3cnt2xs2Hn3SPRS2ra2sp1X1n3cnt2lo2xs2Hn2LX4Hcnt3NZX2SX3SPR2LBS2ra2sp1X1n3cnt2lo2xs2Hn2LX4Hcnt3NZX2SX3SPR2MB2K32LB". (* [comment removed for export] *)
Lemma P_mpi_core_shift_r_spec : mpi_core_shift_r_stmt psegs P_MPI_CORE_SHIFT_R.
Proof.
  unfold mpi_core_shift_r_stmt, P_MPI_CORE_SHIFT_R.
  intros until xs. intros HX Hn LX Hcnt ALX NZX ST LO SPA SX MI RA -> -> ->.
  unfold MPI_CORE_SHIFT_R_STACK in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof (Z.div_mod cnt 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound cnt 32 ltac:(lia)) as MB.
  carve_frame 32%nat ST.
  zstep. zstep. zstep. zstep. zstep.
  zstep. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  2: zstep; rewrite land_31_mod; zstep; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia;
     [| zstep; if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia].
  (* [comment removed for export] *)
  2,3: eapply (@phase1_walk) with (v0 := cnt / 32) (v1 := cnt mod 32); try eassumption; try reflexivity; try lia.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep.
  all: release_frame FR ST (bv_unsigned sp).
  all: rewrite !Z.shiftl_mul_pow2 by lia; change (2^2) with 4.
  all: pose proof (firstn_skipn (Z.to_nat n) xs) as EY; symmetry in EY;
       assert (LB : length (firstn (Z.to_nat n) xs) = Z.to_nat n) by (rewrite firstn_length; lia).
  all: rewrite EY in HX; apply u32arr_app in HX; destruct HX as [HXB HXC]; rewrite LB in HXC;
       apply u32arr_cells in HXB; rewrite LB in HXB.
  all: pose proof P_memset_spec as SP; unfold memset_stmt in SP.
  all: eapply evt_cut; [ eapply SP; [|exact MI]; rewrite !unsigned_lit by lia;
                         replace (Z.to_nat (n * 4)) with (4 * Z.to_nat n)%nat by lia; exact HXB | ].
  all: clear SP HXB; unfold memset_post; rewrite !unsigned_lit by lia.
  all: match goal with H : mem_inv psegs ?mc |- _ => post_call psegs mc end.
  all: match goal with H : rw_cells psegs ?m2 ?X' [CB _ (repeat _ _)] |- _ =>
      constr_eq X' X;
      apply (u32arr_of_cells psegs m2 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat n))) in H;
      [| rewrite u32s_repeat0; replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 by reflexivity; f_equal; lia ];
      rename H into HXB
    end.
  all: lazymatch type of HXB with u32arr _ ?m2 _ _ =>
       assert (HX' : u32arr psegs m2 X (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs))
       by (apply u32arr_app; split; [exact HXB|]; rewrite repeat_length; replace (4 * Z.of_nat (Z.to_nat n)) with (4 * Z.of_nat (Z.to_nat n)) by lia;
           lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat n)) with a by lia end; exact HXC) end.
  all: finish.
  all: try exact HX'.
  all: try (rewrite app_length, repeat_length, skipn_length; lia).
  all: try (rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; lia); rewrite Nat.sub_diag; reflexivity).
  all: rewrite lval_repeat0_app by lia; symmetry; apply Z.div_small; split; [apply (proj1 (lval_range xs n ltac:(lia)))|];
       eapply Z.lt_le_trans; [apply (proj2 (lval_range xs n ltac:(lia)))|]; apply Z.pow_le_mono_r; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
