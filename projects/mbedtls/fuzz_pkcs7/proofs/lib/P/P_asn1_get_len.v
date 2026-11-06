(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00f511c23c0cb51c 0 2 0 1 25 1P02eff0e7c95f514c 0 3 0 1 8 1 13 1P07403ed2c50624f8 0 2 0 1 9 1P0acf7244764a75c4 0 5 0 1 9 1 11 1 13 1 14 1P0bcb4e1f24ac8b1a 0 2 0 1 15 1P1038ba92bf7b7722 0 2 0 1 26 1P1155a0c85c7cfba8 0 4 0 1 10 1 12 1 15 1P11eff5a2a14bb97f 0 2 0 1 17 1P16c0eccee78176ed 0 2 0 1 9 1P177b1972a4d8d420 0 5 0 1 15 1 18 1 19 1 21 1P17db3c3a05059f05 0 2 0 1 2 1P17f37b91a40ef572 0 6 0 1 11 1 13 1 14 1 15 1 16 1P19064fd6d7074703 0 2 0 1 25 1P1b1817d151ca38a2 0 2 0 1 20 1P1d0af3e8331d4e28 0 4 0 1 11 1 13 1 14 1P1d2276fa27e25ae5 0 2 0 1 6 1P1eacb1ae4de50e94 0 4 0 1 7 1 9 1 12 1P1fda725ac2ea9912 0 3 0 1 4 1 18 1P21709b0dff100d36 0 5 0 1 9 1 10 1 12 1 15 1P228d27e49b86b3b9 0 3 0 1 1 1 15 1P27dec66651b1ec7f 0 2 0 1 2 1P2b210d0caa78c955 0 2 0 1 5 1P2b56eb0114ad3414 0 4 0 1 11 1 13 1 14 1P2f9854914173e4e8 0 2 0 1 24 1P3331f270aef993a3 0 5 0 1 9 1 11 1 13 1 14 1P338d716d2bd83cf7 0 5 0 1 10 1 13 1 14 1 16 1P35424c8d7fcb70bc 0 4 0 1 10 1 12 1 15 1P385f82ebe42db961 0 5 0 1 9 1 10 1 12 1 15 1P394c19c103e3eb87 0 5 0 1 16 1 19 1 20 1 22 1P3aa3ceea1c760224 0 3 0 1 10 1 12 1P3aa4eeb82fe7e39c 0 2 0 1 1 1P3b612c912227e07a 0 2 0 1 1 1P3ebb6e99f72514d3 0 2 0 1 21 1N003802f2f756e998N00fc41469ad31b26N010ea8c41836a532N02066227b6654991N02e60a4a3bbd2a77N0389b0f5d1c1fbb2N0395574a569f9e28N039573e1aae8b5f6N040a17b38dc320d2N0512580ecedd529aN05cb54bd5b30f5e3N0628a0a72bcf0fb8N06b01f7a6665520dN06bc1495d15609efN094ce9bec213ca52N0a78199f70da4b7fN0bec55c6adedf14eN0c56a89305f89959N0e9cdc5f3b270c58N0eb3a068796cdef1N0ec0e58abc50d512N0f811940c169dc8dN111580e385dae563N12620438fc0094e6N1279b47a94e2e4c5N128b3d1f5628fb11N14c8b645f86b0a9fN152957e100516ae8N15781bad5805e5e3N16291dab3890c492N18915f9185b96af6N1c7bc74ef485a23fN1d359ed6a2140f65N1e01c9694e25ad25N1fe84dfa5af1f473N20fa9856225ff46fN215b903c38273c0aN2265e2a3c273fb87N2337fd4f3a936163N23a345dd39ca37eeN23fdc1c88312e879N2784c8dbd690d165N280bf44b71164f12N2930d1e6cadf372dN295cc6b977a89fcdN2a49a57e7bff9c66N2ac91977ef4c9747N2af0b0596ab21d68N2b2dfcd43ca6a9f3N2bf5f5ec4a77274bN2c3de8174ad36557N2ce57a274d5608a0N2dcd56e3646f7938N2e2f4c68fcbe3035N2ed2862d147f965dN2f929df57f046751N316b66e59db2d998N3175a65ba2241216N317f81d1579b900cN3180abca70a27149N31a4d54aa4574147N31ca32bf18e9b4eeN33ec9210482142c0N34709d7226c959acN34d16a5938298c01N356a1789eeb469abN35d8e0d527fe72a7N360d438ddc6e4449N361bba5df2311ea2N3745ef84dd459fddN3807142ef47fc3daN38bdbd3de71dca8aN394b250998602cb1N39c21be3b847dc95N3a43171eb28bcbe9N3adc03e8c399caeaN3b444c2c03b8bf13N3bfa71871c81a3c4N3c31b5e52409abd3N3d2bc8576f0a8762N3e301c2efd632bca"%lxh.
Ltac2 gd_tbl_P_asn1_get_len () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Exec.evt"; "asn1_get_len_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.P.PImg.psegs"].


Definition P_ASN1_GET_LEN : Z := 0x1ddec.

Definition asn1_get_len_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_len ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(9.O17.)O6.(:.(2.&40.))R4.(;.O18.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+8.))(11.(>.$4.$4.))))O1.R4.)(5.(12.O18.O1.R4.)(5.(13.O18.R4.)(5.(6.(2.&40.)R10.(14.&40.R3.))(5.(5.(15.-7?.R3.)(16.R3.=))(5.(17.O18.R4.O5.(=.$18.(19.(14.&40.R2.))(11.$18.)))(5.(17.O18.R4.O4.(=.$18.(19.R1.)(11.$18.)))(5.(5.(16.O3.R2.)(16.R2.O2.))P,(6.$4.R3.=)(5.(16.(10.O3.+1.)R3.)(16.(1:.&40.R2.)(1;.O2.R3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_len_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_len ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PLENP,$4.PP,$4.PEND,$4.PBUF,$4.Pbs,(1=.(2.&8.))Plenv,(2.&40.)P,(17.O2.R8.R7.(=.$18.(19.(14.&40.R5.))(11.$18.)))P,(17.O2.R9.R7.(=.$18.(19.R2.)(11.$18.)))P,(1>.O2.R:.R5.R4.)P,(16.R6.R8.)P,(16.R9.R8.)P,(16.R9.(10.R8.(1?.(20.(2.&8.)R7.))))P,(15.(10.R9.(1?.(20.(2.&8.)R8.)))(21.+2.+3?.))P,(22.(16.(10.R>.+8.)R=.)(16.(10.R=.+8.)R>.))P,(22.(16.(10.R?.+8.)R;.)(16.(10.R;.(1?.(20.(2.&8.)R:.)))R?.))P,(22.(16.(10.R?.+8.)R<.)(16.(10.R<.(1?.(20.(2.&8.)R;.)))R?.))P,(6.$4.(23.R11.+8.)=)P,(6.$4.(23.R11.+8.)=)P,(15.=R13.)P,(15.=R13.)P,(15.=R11.)P,(13.O2.R17.)P,(6.(2.&40.)R30.(14.&40.R17.))P,(6.(2.&40.)R30.(14.&40.R15.))P,(6.(2.&40.)R30.(14.&40.R18.))(24.O2.(25.O2.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R1:.R19.R18.R17.R1;.)(7.(8.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(14.&40.O1.)R1<.(:.(2.&40.))R1;.(;.O2.)))")
(* [comment removed for export] *).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation POST := (asn1_get_len_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END m).


  (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_len ()) "Pk,$26.Pcur,$4.Pstop,$4.PL,(2.&40.)Px5,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(6.$26.(27.(1;.R6.R7.))R8.)P,(5.(16.(10.VP,+1.)R8.)(15.R8.R7.))P,(16.R8.VEND,)P,(17.$28.R4.VPP,(=.$18.(19.(14.&40.R:.))(11.$18.)))P,(17.$28.R5.VLENP,(=.$18.(19.R9.)(11.$18.)))P,(1>.$28.R6.VBUF,Vbs,)P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(11.(>.$4.$4.))))Vm,R7.)P,(12.$28.Vm,R8.)P,(13.$28.R9.)(24.$28.(25.$28.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R=.Vt1,Vt2,Vs0,Vs1,(14.&40.VPP,)(14.&40.VEND,)(14.&40.VLENP,)R>.(14.&40.R?.)(14.&40.R10.)R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(14.&40.+1=>70.)Vfc,(:.(2.&40.))R:.(;.$28.)))")
(* [comment removed for export] *).
  Proof.
  induction k as [|k IH]; intros cur stop L x5 x16 x17 mm Hk Hcur Hstop HPP HLEN HBUF MU WM MI; [lia|].
  destruct (nth_error bs (Z.to_nat (cur - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  pose proof (u8ro_read psegs mm BUF bs (cur - BUF) b _ HBUF NB ltac:(lia) eq_refl) as RD.
  lxp_run (PLAN [0x1ddec; 0x1de70] [(0x1de24, DMerge 13)] 61%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 122480; (lxp_apply (IH (cur + 1) stop)) | lxp_ret ].
Qed.

End Walk.

Lemma P_asn1_get_len_spec : asn1_get_len_stmt psegs P_ASN1_GET_LEN.
Proof.
  unfold asn1_get_len_stmt, P_ASN1_GET_LEN.
  intros until lenv.
  intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 MI -> -> ->.
  pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0.
  lxp_run (PLAN [0x1de70] [(0x1de24, DMerge 13)] 61%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 122480; lxp_longform nn; lxp_apply loop_walk | lxp_ret ].
Qed.
