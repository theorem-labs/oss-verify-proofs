(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_mpi_core_read_be.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac LxP_SumsArr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00112cf021b75bb8 0 2 0 1 45 1P006f2406e1fdf43c 1 1 4 2 21 1 27 1 3 0 1 28 1 29 4P00fa91f46d8ae42a 0 2 0 1 7 1P01d1d49b56aebebb 0 2 0 1 30 1P02981bdb593d2583 0 2 0 1 8 1P046beed7b5f1964f 0 8 0 64 1 64 20 64 21 64 28 64 29 64 30 64 31 64P04f2dfdc0961b94b 0 2 0 1 31 1P063cc972a0d44cdb 1 1 4 3 0 1 24 1 26 1 2 12 1 39 1P07b2e8b2cad04fc8 0 3 0 1 18 4 32 1P07ebb11cff7cadd6 0 2 0 1 46 1P082c64cdbc8c6f3a 1 1 4 2 0 1 45 1 3 6 1 46 1 47 4P08a00db5e556b3f3 0 6 0 4 4 1 30 1 32 1 34 4 45 1P0dec932c55bd6a54 0 2 0 1 21 1P0ea522106e0b71e4 1 1 4 2 1 1 29 1 3 0 1 28 1 30 4P0eada4d64697e4ac 2 40 1 2 4 4 1 1 48 1 50 1 51 1 4 4 6 1 32 1 34 1 49 1 7 0 4 30 4 44 16 47 4 52 4 53 16 54 16 1 1 4 4 2 1 47 1 49 1 52 1 6 0 4 8 4 48 4 50 4 51 4 53 16P101c68d2ac13b421 1 1 4 1 0 1 3 5 1 16 1 28 1P12f0f94f39a0ca65 1 1 4 1 0 1 2 17 1 28 1P146a90c057b1206c 1 1 4 2 0 1 27 1 3 10 1 28 1 29 4P14e3c86f51d428bf 0 6 0 4 6 1 10 1 11 1 25 4 26 1P1637f1e6ef5d86f6 0 2 0 1 24 1P16920a1c7648787c 0 4 0 1 21 1 28 1 29 1P176aaafb09f1101f 0 4 0 1 21 1 28 1 29 1P1909feeb1cee27b8 0 2 0 1 25 1P19e849e1068ef5b6 0 2 0 1 9 1P1b1f5a910d0611e7 2 23 1 1 4 4 3 1 19 4 32 1 33 1 6 0 1 24 1 26 4 31 1 34 1 35 4 1 1 4 3 2 1 31 1 34 1 4 0 4 32 4 33 4 35 16P1bfa670791224e16 0 3 0 4 6 1 46 1P1c41310e031ab215 2 23 1 1 4 4 3 1 19 4 32 1 33 1 6 0 1 24 1 26 4 31 1 34 1 35 4 1 1 4 3 2 1 31 1 34 1 4 0 4 32 4 33 4 35 16P1cb2acf5404197d9 0 2 0 1 45 1P1e2468250fba3f9f 1 1 4 2 0 1 27 1 3 10 1 28 1 29 4P1ec974c6cda1ec54 0 3 0 1 18 4 32 1P1fa0c0ab259efce3 0 4 0 1 21 1 28 1 29 1P20413cc7faad0af8 2 43 1 1 4 6 0 1 3 1 41 1 48 1 49 1 50 1 3 9 1 51 1 52 4 1 2 4 4 7 1 33 1 35 1 50 1 4 6 0 1 2 1 45 4 48 1 49 1 51 1 2 52 1 53 1P2355b64f9c6e52e6 2 17 0 2 0 1 1 1 0 4 0 1 1 1 7 1 11 1P238500241641f2be 1 1 4 2 7 1 27 1 3 0 1 24 1 28 1P241c592674075048 0 4 0 1 22 1 29 1 30 1P2442cda3b5719fbf 1 1 4 2 22 1 28 1 3 0 1 29 1 30 4P253f04534179b918 0 2 0 1 23 1P26108e22919759b8 0 5 0 1 2 1 25 4 32 1 33 1P26a267b13ce3216d 1 1 4 3 0 1 32 4 44 1 5 2 1 28 1 30 1 43 1 45 4P2744dc4d7e7c7a43 0 2 0 1 9 1P277988406339d024 0 2 0 1 21 1P27dc8b8c95ee69e2 0 2 0 1 25 1P283aaba6d61a7a3d 1 1 4 2 0 1 46 1 5 4 1 30 1 32 1 45 1 47 4P283acf4825a6c602 1 1 4 2 0 1 27 1 3 10 1 28 1 29 4P28c184871e211c01 1 1 4 1 0 1 3 5 1 16 1 28 1P290a6287605d7af4 0 3 0 1 3 1 14 1P2bd38a228a4bded9 0 2 0 1 9 1P2c12b8cf36b6a7ff 2 19 0 2 0 1 1 1 0 4 0 1 1 1 9 1 13 1P2cf1254dd4c62f54 0 4 0 1 18 4 30 1 32 1P2da5837d0f03980c 0 4 0 1 29 1 46 1 47 1P2e3a60b9c82f74fd 0 2 0 1 30 1P2ead664bfa0ea943 0 4 0 1 12 1 22 1 31 1P2f37b45cba834d14 0 2 0 1 4 1P3465ec0c013867cb 0 2 0 1 31 1P3572f51117f2fa28 0 4 0 1 21 1 28 1 29 1P35b20704f6875327 0 2 0 1 7 1P37e8854a499e5448 0 4 0 1 18 4 30 1 32 1P381e06278e31815c 2 23 1 1 4 4 3 1 19 4 32 1 33 1 6 0 1 24 1 26 4 31 1 34 1 35 4 1 1 4 3 2 1 31 1 34 1 4 0 4 32 4 33 4 35 16P3ab4c26e1ed91c06 1 1 4 3 1 1 30 1 33 1 4 2 4 31 4 32 4 34 16P3c6f6d488f52e957 1 1 4 3 0 1 31 1 32 1 6 2 1 23 1 25 4 30 1 33 1 34 4P3cea0329ab847c0e 2 23 1 1 4 4 3 1 19 4 32 1 33 1 6 0 1 24 1 26 4 31 1 34 1 35 4 1 1 4 3 2 1 31 1 34 1 4 0 4 32 4 33 4 35 16P3d14d6835bf8e208 1 1 4 3 1 1 31 1 32 1 4 2 4 30 4 33 4 34 16P3d71c6569c364188 1 1 4 2 0 1 43 1 3 4 1 44 1 45 4N00a2721658665301N00b22806ce06c465N017ec45a4932e6c8N023d574b80100b51N02c01bc48d6ce43cN03c4957ca7779bfaN04c17c39b9dd46b5N05074c8d0b6db1eaN05602e7be49703fbN06def306fb895d16N06f941db2bfcebcfN076dfc5a8e75a7ceN07724e42421be112N0827ff312330acc4N08bd24e1e5f42429N0a688617a2e95f39N0a8d53cc579d3ec2N0addbd082ee3b5a0N0b551937df6a4cccN0c1061d5c2ca5c1bN0c4b1ba16845124cN0d10236d15ec0290N0dd8b65b505bfb0aN0f4cc7d1717630cfN0fa9582bdf6b3df6N0ff28ff4f8d66010N100862472681a28cN10bcd550d66a898cN11ea9c5f94cc3038N120e610feee568a1N1215da3cf7cafabbN12856845e4a42f43N138f9967925107bbN13c823a86e70e773N1486bb99b7a5ae1eN14a516002628cabcN17018ccfd8b52e7cN1718cd940fece332N177e4684c911fcedN189bce5ff5dc948bN18c95d6a7bcf388fN19b6d701fb7e5ab6N1a82d8ffd1e62a1dN1b23e2912e5bd5f8N1b7e7a4e0c32fa24N1b9802bc38a2277bN1bb0018910254deeN1bf9c0751f5f7114N1ca65d6f48a7c31aN1d6c68ba698fefbbN1d6db620a98c38dfN1d9707e8b76722c9N1e890e7b22b1761bN1f3c2eb1c889661bN1f5f38b83aa411b5N1fc541ddd57fb0bdN1fdb62371993fae6N212df9d6171fc97cN21f221016d9c4d5cN23786c65f7fb7628N240da8fe4cacf6b6N24a3b64c20eea41aN2577f0cdf614eddcN26d71eec86749c3dN271ef307009eb67cN27a277ecfdecab51N27e9e2ac2ffa818bN28ca2b6693415369N2a04999b064c6e10N2a61316e646585eeN2aa799dc0da08fd7N2b7fd0dbe52d693dN2bc350d1e7088aa8N2bcf8a6c5f49ebd7N2be5f5eded9058e9N2caf3f4c01600570N2d3d98911e4158ceN2dbaff21c5c6b86dN2e8b4fcc7e068d5cN2eb7bb8c62b55809N2f4a00110fdab5e4N30ef604dcd8cd54fN332a394fadb25343N33e82f04c9f04086N3406e66e412b4323N34f8b5a074821c45N35178dd26e286854N36b87e56c98fa9b4N3721402f1d885605N372fb8564fc15c1eN37b63b820236ffbfN3a3f9f24c99f79a2N3b0cc54135c0f944N3b11cb1dec77dd5bN3b63e04cf3ee3b28N3bf641c2f863e72bN3c277d29179938acN3cbd24d851aa5a8dN3da8ae82c7187d5cN3e7876b91b78b2eaN3eefebcc21315ed0N3f5d5cb905fcca3cN3fd6d5289e75c7cc"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_read_le () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_READ_LE_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_read_le_post"; "OSSVerify.KrLib.P.P_mpi_core_read_be.read_be_ret"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"].


Definition P_MPI_CORE_READ_LE : Z := 0x22488.
Definition MPI_CORE_READ_LE_STACK : Z := 32.

Definition mpi_core_read_le_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n r : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_le ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O18.O17.O16.O15.R10.R?.R>.O14.O13.(9.&40.O4.)R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(:.O18.)O7.(;.(2.&40.))R2.(<.O19.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O6.(12.O6.(13.+4.O5.)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.O17.)$16.)(15.&40.O17.))(17.(?.$10.$10.))))O1.R2.)(5.(18.O19.O1.R2.)(5.(19.O19.R2.)(5.(1:.O19.R2.O6.R1.)(5.(6.$1;.(1<.(2.&40.)R1.)(1<.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1=.(2.&40.)(1>.O5.)R1.)(1=.(2.&40.)(1>.O5.)O3.))(1?.O19.R2.O2.(15.&40.O17.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_read_le_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_le ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$10.Pn,$10.PB,$10.Pblen,$10.Plo,$10.Pxs,(4.(2.&40.))Pbs,(4.(2.&8.))P,(1:.O2.R8.R7.R2.)P,(21.O2.R9.R6.R2.)P,(5.(22.=R8.)(22.R8.+2710.))P,(22.R9.(23.(1<.(2.&40.)R5.)))P,(5.(22.=R8.)(22.R8.(23.(1<.(2.&8.)R5.))))P,(24.(22.(12.R:.(23.(1<.(2.&8.)R6.)))R<.)(22.(12.R<.(13.+4.(23.(1<.(2.&40.)R7.))))R:.))P,(6.$10.(25.R=.+4.)=)P,(26.R>.(27.+2.+40.))P,(24.(6.$10.R<.=)(26.=R=.))P,(1?.O2.R11.R<.(15.&40.R31.))P,(22.R=.(14.(15.&40.R32.)$16.))P,(6.$10.(25.(15.&40.R33.)+10.)=)P,(24.(22.(12.R13.(13.+4.(23.(1<.(2.&40.)R>.))))R?.)(22.(15.&40.R34.)R13.))P,(24.(22.(12.R12.(23.(1<.(2.&8.)R>.)))R10.)(22.(15.&40.R35.)R12.))P,(19.O2.R16.)P,(6.$10.(25.(15.&40.R38.)+2.)=)P,(6.(2.&40.)R30.(9.&40.R17.))P,(6.(2.&40.)R30.(9.&40.R17.))P,(6.(2.&40.)R30.(9.&40.R17.))P,(6.(2.&40.)R30.(9.&40.R17.))(28.O2.(29.O2.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.R1;.R1:.(2:.R1:.R18.)R16.R17.R1<.)(7.(8.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(9.&40.O1.)R1=.(;.(2.&40.))R1<.(<.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L28313414001.2L35497642613.2L41415987093.2L66253720165.200000300400500;S1iSSS1i2Hi". (* [comment removed for export] *)
Lemma land_m4 : forall i, 0 <= i < 2^64 -> Z.land i 18446744073709551612 = 4 * (i / 4).
Proof.
  intros i Hi.
  replace 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))) by reflexivity.
  rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Ltac rdle_dinv_tac X n m lo sp W :=
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
  lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
  lazymatch goal with Hi' : mem_inv _ mx |- _ =>
  lazymatch goal with Hs : stk _ mx lo _ |- _ =>
    assert (DI' : u32arr psegs mx X l /\ Z.of_nat (length l) = n
                  /\ munch W m mx /\ wmono psegs m mx /\ mem_inv psegs mx /\ stk psegs mx lo (bv_unsigned sp + -32));
    [split; [exact Hu| split; [rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] | split; [first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | split; [exact Hw| split; [exact Hi'| exact Hs]]]]] |]
  end end end end end end.

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n B blen lx lb lo : Z) (xs0 : list word) (bs : list byte).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LB : Z.of_nat (length bs) = lb.
  Hypothesis Hbl : 0 < blen <= lb.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis BB : 0 < B /\ B + lb <= 2^64.
  Hypothesis DB : B + lb <= X \/ X + 4 * lx <= B.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 32.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SB : B + lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis OK : chars_to_limbs4 blen <= n.
  Hypothesis HB0 : bytes_at psegs m B bs.
  (* [comment removed for export] *)
  Hypothesis HXhi : u32arr psegs m (X + 4 * n) (skipn (Z.to_nat n) xs0).

  Notation POST := (mpi_core_read_le_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n (read_be_ret n blen) xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation DINV mm xs := (u32arr psegs mm X xs /\ Z.of_nat (length xs) = n
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp + -32)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2977899845.4700000LS2ra2sp1X1n4blen3xs02bs2OK1E". (* [comment removed for export] *)
  Lemma ret_ok : read_be_ret n blen = 0.
  Proof. unfold read_be_ret. destruct (n <? chars_to_limbs4 blen) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39016585212.600000BS1n4blen2lb3Hbl2OK". (* [comment removed for export] *)
  Lemma blen4 : blen <= 4 * n.
  Proof. clear - OK Hbl Hn. unfold chars_to_limbs4 in OK. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rdle_dinv := rdle_dinv_tac X n m lo sp constr:(W).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L23907401973.4L36962904668.8L56174851022.4L6330159503.11L64980102424.400000:00Q00]01>01HS1n3xs'2LXS1n2lx3xs02Ln2L03xs'2LXS1X1n3xs'2LXS2sp1X1n2lx2lo3xs02Hn2Ln2L02LO2SXS1n3xs'2LX". (* [comment removed for export] *)
  Lemma fin_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_le ()) "Pm',P,(2.&40.)(3.(2.&8.))Pxs',(4.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(=.(>.(?.$10.$10.)(11.$10.$10.VX,(12.VX,(13.+4.Vn,)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.Vsp,)+20.)(15.&40.Vsp,))(17.(?.$10.$10.))))Vm,R10.)P,(18.$2;.Vm,R11.)P,(19.$2;.R12.)P,(1?.$2;.R13.Vlo,(15.&40.Vsp,))P,(1:.$2;.R14.VX,R13.)P,(6.$10.(23.(1<.(2.&40.)R14.))Vn,)(29.$2;.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,(2:.Vn,Vblen,)Vxs0,Vlo,Vm,(7.(8.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(9.&40.=)R11.R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(:.Vra,)Vfc,(;.(2.&40.))R16.(<.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until yt6. intros MU WM MI ST HX LX.
    unfold mpi_core_read_le_post, MPI_CORE_READ_LE_STACK. rewrite ret_ok.
    flexi 15%nat. exists (xs' ++ skipn (Z.to_nat n) xs0). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { apply u32arr_app. split; [exact HX|]. replace (X + 4 * Z.of_nat (length xs')) with (X + 4 * n) by xlia LX.
             eapply u32arr_transport; [exact HXhi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -Hn Ln L0 SX LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LX L0 Ln Hn. }
    split. { rewrite skipn_app, skipn_all2 by xlia LX Hn. replace (Z.to_nat n - length xs')%nat with 0%nat by xlia LX Hn. reflexivity. }
    exact ST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rdle_ret :=
    try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ];
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo (bv_unsigned sp) |- _ =>
      eapply (fin_post mx l);
      [ first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | exact Hw | exact Hi' | exact Hs | exact Hu
      | rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] ]
    end end end end end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L18573464707.14L28498816157.5 L59308586248.4 L61134621255.1 M45728408632.9600000R00b01001301AS2sp1X1n1B2lx2lb2lo2bs2Ln2DB2LO2SBS4blen1k1i2Hk2HiS4blen1i2Hk2HiS1iS4blen1i2Hi2H3". (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_le ()) "Pk,$1;.Pi,$10.Pxs,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwi8,(2.&40.)Pwpb,(2.&40.)P,(6.$1;.(1>.(14.Vblen,R10.))R11.)P,(5.(22.=R11.)(26.R11.Vblen,))P,(6.(2.&40.)R4.(9.&40.(13.+8.R12.)))P,(6.(2.&40.)R4.(9.&40.(12.VB,R13.)))P,(5.(1:.$2;.R12.VX,R13.)(5.(6.$10.(23.(1<.(2.&40.)R13.))Vn,)(5.(=.(>.(?.$10.$10.)(11.$10.$10.VX,(12.VX,(13.+4.Vn,)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.Vsp,)+20.)(15.&40.Vsp,))(17.(?.$10.$10.))))Vm,R12.)(5.(18.$2;.Vm,R12.)(5.(19.$2;.R12.)(1?.$2;.R12.Vlo,(12.(15.&40.Vsp,)-20.)))))))P,(2<.$2;.R13.(12.(15.&40.Vsp,)-20.)(>.$2=.(2>.Vs2,)(>.$2=.(2>.Vs1,)(>.$2=.(2>.Vs0,)(>.$2=.(2>.Vra,)(17.$2=.))))))(28.$2;.(29.$2;.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,(2:.Vn,Vblen,)Vxs0,Vlo,Vm,)(7.(8.R13.(9.&40.(12.(15.&40.Vsp,)-20.))Vgp,Vtp,R12.R11.R10.(9.&40.VB,)(9.&40.VX,)(9.&40.Vblen,)R8.(9.&40.R16.)R7.(9.&40.VX,)R?.R>.R=.(9.&40.Vblen,)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(9.&40.+224><.)Vfc,(;.(2.&40.))R14.(<.$2;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i xs mm xra xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wi8 wpb Hk Hi -> ->
      (HX & LX & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hi|].
    pose proof blen4 as BL4.
    pose proof (bytes_at_transport psegs _ _ _ _ _ HB0 MU ltac:(cbn [disjoint_from]; rewrite LB; clear -Hn Ln LB DB SB LO; lia)) as HB.
    lx_run_tac (PLAN [0x224ec] [] 40%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x224ec) _ _ _ _) =>
             rdle_dinv; eapply (IH (i + 1)); [xlia Hk Hi | klia | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => rdle_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422282358.2000001S". (* [comment removed for export] *)
Lemma lxp_c2l : forall len, 0 <= len -> Z.shiftr len 2 + Z.b2z (0 <? Z.land len 3) = chars_to_limbs4 len.
Proof. intros len H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply chars_to_limbs4_eq. exact H. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L27071287451.4 L40175532981.4 L49161362620.3 L56174851022.5 L57628700040.5 L60897247877.5 M1279833341.90 M14631121796.92M26169469248.92M27099014668.90M27099126441.92M30020895026.92M31127766590.92M322799827.90  M37464644674.65M37464644674.68M5162844963.92 M51734280331.92M53471219346.92M56527448794.92M58706133424.68M58706133424.90M58706197781.92M60445842743.90M60964123143.9200000<00H00U00c01001?01H01X01a01o02=02F02n03=03L03M03N03O03R03^03m04<04K04Q04RS1X2xs2XB2H1S1n2xs2Hn2LXS4blen2bs3HblS1X1n2xs2Hn2LXS2sp1X1n1x2HxS1B4blen2bs3NZBS1n2xs2LXS4blen2bs3Hbl2H2S4blen2H2S2sp2lo2LO3LO0S2sp2lo2LO3LO0S4blen2H2S2ra2sp1X1n1B4blen2xs2bs3BB04NZB'3lxl2H2S2sp1X2lo2xs2SXS1n4blen2H13C2LFFFS1BS1X2xs2XB2H3S1n4blen2H23C2LS1n4blen2H33C2LS1n4blen2H43C2LS1n2HnF". (* [comment removed for export] *)
Lemma P_mpi_core_read_le_spec : mpi_core_read_le_stmt psegs P_MPI_CORE_READ_LE.
Proof.
  unfold mpi_core_read_le_stmt, P_MPI_CORE_READ_LE.
  intros until bs. intros HX HB Hn LX Hbl DB ALX XT NZB ST LO SPA SX SB MI RA -> -> -> ->.
  unfold MPI_CORE_READ_LE_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HB) as BB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  assert (NZB' : blen <= 0 \/ 1 <= B) by (clear -NZB Hbl; lia). clear NZB.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (lock HB) as HB0. pose proof (lock HX) as HX0.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn (Z.to_nat n) xs) in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi.
  rewrite firstn_length in HXhi. replace (X + 4 * Z.of_nat (Nat.min (Z.to_nat n) (length xs))) with (X + 4 * n) in HXhi by xlia LX Hn.
  assert (LXlo : Z.of_nat (length (firstn (Z.to_nat n) xs)) = n) by (rewrite firstn_length; xlia LX Hn).
  pose proof (lock HXhi) as HXhi'. clear HXhi HB.
  pose proof (sumsarr_ok [X]) as LXSUMS.
  (* [comment removed for export] *)
  lx_run_tac (PLANS [0x224ec] [] 60%N SUMSARR); lx_tree.
  all: lxp_unjunk; try lx_same_mem; pose proof (lxp_c2l blen ltac:(xlia Hbl)) as C2L.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x224ec) _ _ _ _) =>
         rdle_dinv_tac X n m lo sp constr:([(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)]);
         eapply (@loop_walk) with (k := Z.to_nat blen) (i := 0) (B := B) (lx := Z.of_nat (length xs)) (lb := Z.of_nat (length bs))
             (bs := bs) (xs0 := xs);
           try eassumption; try reflexivity; try klia; try (f_equal; klia);
         first [exact (unlock _ HB0) | exact (unlock _ HXhi') | idtac]
       | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mf _) =>
         tryif constr_eq mf m then
           ((* [comment removed for export] *)
            apply evt_done; unfold mpi_core_read_le_post, read_be_ret;
            first [ rewrite (proj2 (Z.ltb_lt n (chars_to_limbs4 blen))) by klia
                  | rewrite (proj2 (Z.ltb_ge n (chars_to_limbs4 blen))) by klia;
                    (let xX := constr:(X) in
                     match goal with H2 : 0 <= - xX |- _ =>
                       replace (Z_to_bv 64 xX) with (Z_to_bv 64 0) by (f_equal; clear -XB H2; lia) | _ => idtac end) ];
            flexi 15%nat; exists xs;
            split; [reflexivity|];
            split; [apply munch_refl|]; split; [apply wmono_refl|]; split; [exact MI|]; split; [exact (unlock _ HX0)|];
            split; [reflexivity|]; split; [reflexivity|]; exact ST)
         else
           ((* [comment removed for export] *)
            try rewrite (Z_to_bv_bv_unsigned sp); apply evt_done;
            let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
            lazymatch goal with Hu : u32arr _ mx xX ?l |- _ =>
            lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
            lazymatch goal with Hm : munch _ xm mx |- _ =>
            lazymatch goal with Hw : wmono _ xm mx |- _ =>
            lazymatch goal with Hi' : mem_inv _ mx |- _ =>
            lazymatch goal with Hs : stk _ mx xlo (bv_unsigned xsp) |- _ =>
              eapply fin_post with (lx := Z.of_nat (length xs)) (xs0 := xs) (bs := bs);
              first [ exact Hw | exact Hi' | exact Hs | exact Hu | exact (unlock _ HXhi') | exact (unlock _ HB0) | exact eq_refl
                    | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia
                    | rewrite Hl; exact LXlo | klia ]
            end end end end end end)
       end.
  all: match goal with |- ?g => idtac "LEFT" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
