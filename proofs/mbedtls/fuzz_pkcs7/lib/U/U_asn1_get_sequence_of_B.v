(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_sequence_of_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsHeap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00022349d0155f20 0 8 0 16 1 16 34 16 40 16 41 16 42 16 52 16 53 16P01e7f8fc0adfbdc1 2 52 0 6 0 1 2 1 43 1 44 1 54 1 55 1 0 4 0 1 1 1 54 1 55 1P028553203d8bc588 1 1 16 3 0 1 53 1 54 1 7 1 1 40 1 41 1 42 1 52 1 55 1 56 16P0362ccede85c082c 3 4 0 1 1 1 1 1 16 3 1 1 54 1 57 1 4 0 1 55 1 56 1 58 16 1 1 16 3 2 1 55 1 56 1 4 0 1 54 1 57 1 58 16P04522df1524caa02 1 1 16 3 1 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P06eb1d918bcfcba5 0 2 0 1 39 1P0729a83d42a6e8eb 0 4 0 16 3 16 50 16 51 16P07b5e4f7b78db646 0 5 0 1 41 1 42 1 52 1 53 1P0a64a0cb472593c9 3 4 0 1 1 1 1 1 16 3 1 1 54 1 57 1 4 0 1 55 1 56 1 58 16 1 1 16 3 2 1 55 1 56 1 4 0 1 54 1 57 1 58 16P0c954c1ad252b5b5 3 4 0 1 1 1 1 1 16 3 2 1 54 1 57 1 4 0 1 55 1 56 1 58 16 1 1 16 3 1 1 55 1 56 1 4 0 1 54 1 57 1 58 16P0c99d93e9bfea1a8 1 1 16 3 0 1 53 1 54 1 7 27 1 40 1 41 1 42 1 52 1 55 1 56 16P0e670ce0c1376ebe 0 4 0 1 26 1 50 1 51 1P10da13f23e9e35d1 2 50 0 6 0 1 3 1 44 1 45 1 55 1 56 1 0 4 0 1 2 1 55 1 56 1P10dca9f82f4bc3e5 1 1 16 3 0 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P1268de38b0983228 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P1388b40d0ff22e29 1 1 16 3 0 1 53 1 54 1 7 1 1 40 1 41 1 42 1 52 1 55 1 56 16P143c6fa429e43cea 1 1 16 3 0 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P158ca48042d7c401 3 4 0 1 1 1 1 1 16 3 1 1 54 1 57 1 4 0 1 55 1 56 1 58 16 1 1 16 3 2 1 55 1 56 1 4 0 1 54 1 57 1 58 16P16e53e1b0e59d911 1 2 16 2 0 1 52 1 16 2 2 1 53 1 2 54 1 55 1P1af5dc78ade8aa37 1 1 16 3 1 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P1beb78ed6a5bb83d 3 6 0 1 1 1 0 4 0 16 1 16 54 16 55 16 0 4 0 16 2 16 54 16 55 16P1cd1e1e8317455b2 2 51 0 6 0 1 2 1 43 1 44 1 54 1 55 1 0 4 0 1 1 1 54 1 55 1P1f4dbf1b22e0afb1 0 4 0 1 28 1 52 1 53 1P206028f15daadfeb 1 1 16 2 2 1 53 1 3 0 1 52 1 54 16P20d881c61bc86429 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P25de8e6767e3e277 3 5 0 1 1 1 0 4 0 16 1 16 54 16 55 16 0 4 0 16 2 16 54 16 55 16P269d969aa3e6f7e1 0 2 0 1 1 1P2862b1f9b3fcee98 0 2 0 1 2 1P28e2e3d888d5cd5d 1 1 16 3 0 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P29ea0447e751adad 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P2a7ecce2b20fc8a5 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P2ae21ee0878f9eb8 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P2db02ef650a5e741 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P2e184d1520ad1a6c 1 1 16 3 0 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P2f77dcb07d3b58ca 3 6 0 1 1 1 0 4 0 16 1 16 54 16 55 16 0 4 0 16 2 16 54 16 55 16P2f81fea492bfe78c 1 1 16 3 0 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P2fd213cd1eb009e9 0 2 0 1 38 1P2ffbe5ef301ef722 1 1 16 3 0 1 54 1 55 1 7 28 1 41 1 42 1 43 1 53 1 56 1 57 16P37de4686157b4395 3 5 0 1 1 1 0 4 0 16 1 16 54 16 55 16 0 4 0 16 2 16 54 16 55 16P39dba654a429973c 0 4 0 1 40 1 50 1 51 1P3bc1a88a1bc02e99 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P3bc20ae8a43003a4 3 6 0 1 1 1 0 4 0 16 1 16 54 16 55 16 0 4 0 16 2 16 54 16 55 16P3d3ff38ba4534e04 3 5 0 1 1 1 0 4 0 16 1 16 54 16 55 16 0 4 0 16 2 16 54 16 55 16P3d5943996879d1f7 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16P3efb8363a6ec79d0 1 1 16 3 0 1 54 1 55 1 7 2 1 41 1 42 1 43 1 53 1 56 1 57 16N005787e79d8b91c1N00a233c12f86233fN010f6e9d6efd47c2N07af7e6277dde145N08b91b8a3fa21b2fN0ba4291f877242ddN0caef8a4c23233d6N11dd12a8b43ec95eN11f4beffc2a4303eN12afe7cef80004b7N16677191df22dc06N18330b103cfa434aN18cee8442f8ee8dbN1b87d22b3bef4443N1c2580bfbe9a79c3N1d186d9da39bfefeN1da513709fe3c891N1df4fa923cd8005dN1ea0b3de50341c72N243d323919fd94e9N265c1a3e8f0f8ea0N273d08dba1fe7cd8N288100a140dad099N2986be884737eb4dN2d1c4bf27cc1b0b4N2f553e65e412f171N30236bf2435d3314N31252beea304a6c1N32647ba782a51e9dN350b54e42b80e304N36085afd335fbb9cN361b8e698f6618e4N36a6f06d0e41e63eN37c97eebad64f6c2N37df74c460ffad8bN3895058f38601819N39e385b490a556a0N3a3757be217b0fb3N3a5d8b781041736bN3b9f16d8cda7dba0N3bf023705e6aecadN3d244ce79a8369fb"%lxh.
Ltac2 gd_tbl_P_asn1_get_sequence_of_B () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.LBof"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.fresh"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.Lists.List.hd"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.cb_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo tag : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 32 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 176 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 32 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 32.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (asn1_get_sequence_of_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation CTX := (bv_unsigned sp + -24).
  (* [comment removed for export] *)
  Notation SPG := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SPT := (Z_to_bv 64 (bv_unsigned sp + -128)).

  Notation INV := (inv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m mo h LB PP CUR END BUF lo bs).
  Notation CBPOST := (cb_post L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR END BUF lo bs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HCALLOC => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D2 => idtac | D3 => idtac | PPB => idtac | CURB => idtac | AL1 => idtac | AL2 => idtac | NZ1 => idtac | NZ2 => idtac | NZ3 => idtac | SLO => idtac | HLS => idtac | ACL => idtac | ACP => idtac | HTOP => idtac | SPA => idtac | DHI => idtac | DIM1 => idtac | DIM2 => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | CWPP => idtac | CWCUR => idtac | CRBUF => idtac | TP => idtac | SPB => idtac | HBR0 => idtac end.
  Lemma cb_alloc_tail : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_B ()) "Pinit,(0.$1.)Plst,$1.Phdn,$1.Pp,$1.Pq,$1.Ptb,$1.PLw,(2.&40.)Pct,(2.&40.)Pcpad,(2.&40.)Plt,(2.&40.)Plpad,(2.&40.)Ptagw,(2.&40.)Pzpad,(2.&40.)Pcl,$1.Pcp,$1.Pll,$1.Plp,$1.Pj0,(0.(2.&8.))Pj1,(0.(2.&8.))Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.$6.VL,VHI,R1.(8.VLB,(9.$1.R2=.(:.$1.R2<.(;.$1.))))R3.R2.)P,(<.$1.(=.$6.VL,VHI,R2.)(=.$6.VL,VHI,Vh,))P,(>.$1.(9.$1.R2?.(:.$1.R2>.(;.$1.))))P,(?.VL,VLB,(9.$1.R30.(:.$1.R2?.(;.$1.))))P,(10.$6.R7.(8.VLB,(9.$1.R31.(:.$1.R30.(;.$1.))))VBUF,VEND,R31.R30.)P,(11.$6.R8.R31.(12.R29.R28.R23.R22.=))P,(13.(14.VBUF,R23.)(13.(14.=R24.)(14.(15.R23.R24.)VEND,)))P,(<.$1.(16.R33.+10.)=)P,(17.=R34.)P,(11.$6.R<.VCUR,(12.R2?.R2>.R29.R28.R34.))P,(<.$1.R35.(18.$1.=(9.$1.R37.(:.$1.R36.(;.$1.)))))P,(19.(13.(<.$1.R2:.=)(13.(<.$1.R2;.=)(<.(0.$1.)(9.$1.R38.(:.$1.R37.(;.$1.)))(;.$1.))))(13.(14.VBUF,R2:.)(13.(14.=R2;.)(14.(15.R2:.R2;.)VEND,))))P,(11.$6.R?.(15.(1:.&40.Vsp,)-20.)(:.$1;.(1<.#8.R28.)(:.$1;.(1=.R2>.)(:.$1;.(1=.R2=.)(:.$1;.(1>.(1?.&40.R38.))(:.$1;.(1>.Vra,)(;.$1;.)))))))P,(11.$6.R10.(15.(1:.&40.Vsp,)-80.)(:.$1;.(1<.#8.R28.)(:.$1;.(1>.Vs9,)(:.$1;.(1>.Vs8,)(:.$1;.(1>.Vs7,)(:.$1;.(1>.Vs6,)(:.$1;.(1>.Vs5,)(:.$1;.(1>.Vs4,)(:.$1;.(1>.Vs3,)(:.$1;.(1>.Vs2,)(:.$1;.(1>.Vs1,)(:.$1;.(1>.Vs0,)(:.$1;.(1>.(1?.&40.+1>=08.))(;.$1;.))))))))))))))P,(11.$6.R11.(15.(1:.&40.Vsp,)-;0.)(:.$1;.(1>.R1<.)(:.$1;.(1>.R1=.)(:.$1;.(1>.R1>.)(:.$1;.(1>.R24.)(:.$1;.(1>.R25.)(:.$1;.(1>.(1?.&40.+1>;48.))(;.$1;.))))))))P,(20.$6.R12.Vlo,(15.(1:.&40.Vsp,)-;0.))P,(21.$6.R13.)P,(22.$6.R14.VBUF,Vbs,)P,(23.$6.VL,VLB,(1:.&40.Vsp,)(:.(24.$1.$1.)(25.$1.$1.VPP,(15.VPP,+8.))(:.(24.$1.$1.)(25.$1.$1.VCUR,(15.VCUR,+20.))(;.(24.$1.$1.))))Vm,R16.)P,(26.(:.(24.$1.$1.)(25.$1.$1.(27.(1:.&40.Vsp,)+;0.)(27.(1:.&40.Vsp,)+80.))(:.(24.$1.$1.)(25.$1.$1.VCUR,(15.VCUR,+20.))(:.(24.$1.$1.)(25.$1.$1.(27.(1:.&40.Vsp,)+20.)(1:.&40.Vsp,))(;.(24.$1.$1.)))))R17.R16.)P,(28.$6.R18.R17.)P,(29.Vmo,R17.)P,(11.$6.R19.VPP,(:.$1;.(1>.(1?.&40.R40.))(;.$1;.)))P,(14.VBUF,R40.)P,(14.(15.R41.(1:.&40.R3?.))VEND,)P,(13.(14.=R41.)(17.R41.+100.))(2:.$6.R1<.(2;.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R44.R35.R31.R30.R2:.R29.R28.R27.R26.R25.R24.R23.)(2<.(2=.(1?.&40.+1>;48.)(1?.&40.(15.(1:.&40.Vsp,)-;0.))Vgp,Vtp,R34.R33.R32.(1?.&40.R43.)R41.R2?.(1?.&40.R42.)(1?.&40.R43.)R41.R2>.R2=.R2<.R2;.(1?.&40.(15.(1:.&40.Vsp,)-18.))(1?.&40.R42.)(1?.&40.R46.)R27.R26.R25.R24.R23.Vs10,Vs11,R22.R21.R20.R1?.)VF,(1?.&40.+1>=64.)Vfc,(2>.(2.&40.))R1=.(2?.$6.)))")
(* [comment removed for export] *).
  Proof.
    (* [comment removed for export] *)
    intros init lst hdn p q tb Lw ct cpad lt lpad tagw zpad cl cp ll lp j0 j1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm0 mm moc hc
      HH HT HND HFR HLSI HLST HLBUF HL16 HLPOS HCUR -> HBUFOK FRG FRT FR ST MI HBUF HPX MU WM MF HPP Hq HqL Htb.
    clear AL1 AL2 NZ1 NZ2 B1.   (* [comment removed for export] *)
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    pose proof (List.NoDup_remove_2 init [] lst HND) as HNL. rewrite app_nil_r in HNL.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros _ HAPc.
    set (LB0 := LBof LB (init ++ [lst])) in *.
    assert (HSUB : forall b, In b LB -> In b LB0) by (intros b Hb; subst LB0; unfold LBof; apply in_or_app; right; exact Hb).
    pose proof (client_wrange_mono L _ _ _ _ _ _ CWCUR HSUB) as CWc. rewrite <- HT in CWc.
    pose proof (client_wrange_mono L _ _ _ _ _ _ CWPP HSUB) as CWp. rewrite <- HT in CWp.
    assert (CRb : client_range L LB0 lo BUF (Z.of_nat (length bs))).
    { intros a Ha. destruct (CRBUF a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [apply HSUB; exact Hb| exact Hr]]. }
    assert (HTOPc : bv_unsigned sp <= heap_top usegs L HI hc) by (rewrite HT; exact HTOP).
    assert (HINL : In (lst, 32) LB0) by (subst LB0; rewrite LBof_snoc; left; reflexivity).
    destruct (HFR lst ltac:(apply in_or_app; right; left; reflexivity)) as (HLC & HLD0 & HLAP).
    assert (HLD : lst + 32 <= hl_data_lo L \/ hl_data_hi L <= lst) by (clear -HLD0 DIM1 DIM2; lia).
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BBF.
    (* [comment removed for export] *)
    assert (ALC : lst + 32 <= CUR \/ CUR + 32 <= lst)
      by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HLC | exact HLD | exact HLAP]).
    assert (ALP : lst + 32 <= PP \/ PP + 8 <= lst)
      by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HLC | exact HLD | exact HLAP]).
    assert (ALB : Z.of_nat (length bs) = 0 \/ lst + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= lst).
    { destruct (Z.eq_dec (Z.of_nat (length bs)) 0); [left; assumption| right].
      eapply client_range_apart; [exact CRBUF | lia | lia | exact ACL | exact HLC | exact HLD | exact HLAP]. }
    unfold seq_cells in HLST, HCUR.
    (* [comment removed for export] *)
    pose proof (heapkit_intro L HI hc LB0 mm moc [(lo, heap_top usegs L HI hc); (lst, lst + 32)] HH
       ltac:(constructor; [apply ok_stack; exact ACL | constructor; [apply (ok_block L LB0); exact HINL | constructor]])) as HK.
    pose proof (hcli_block L LB0 (bv_unsigned sp) lst 32 HINL) as T0.
    pose proof (hcli_cwrange L LB0 lo _ (bv_unsigned sp) CUR 32 CWc DS2) as T1.
    pose proof (hcli_cwrange L LB0 lo _ (bv_unsigned sp) PP 8 CWp DS1) as T2.
    pose proof (hcli_crange L LB0 lo (bv_unsigned sp) BUF _ CRb DS3) as T3.
    pose proof (obj_block L LB0 lst 32 HINL ltac:(clear; lia)) as O0.
    pose proof (obj_cwrange L LB0 lo _ CUR 32 CWc ACL ltac:(clear; lia)) as O1.
    pose proof (obj_cwrange L LB0 lo _ PP 8 CWp ACL ltac:(clear; lia)) as O2.
    pose proof (obj_crange L LB0 lo BUF _ CRb ACL (Nat2Z.is_nonneg _)) as O3.
    rewrite TP. change (id (mo_frame mo moc)) in MF.
    lazymatch goal with |- aevtM _ _ ?Q _ => pose proof (SUMS_callocP_ok L HI HCALLOC DIM1 DIM2 32 Q LB0 (heap_top usegs L HI hc) moc ltac:(cbn; lia)) as SU end.
    lazymatch type of HPX with ?T => change (id T) in HPX end. lazymatch type of MU with ?T => change (id T) in MU end.
    lazymatch type of WM with ?T => change (id T) in WM end. lazymatch type of HLSI with ?T => change (id T) in HLSI end.
    assert (ELB0 : LB0 = LBof LB (init ++ [lst])) by reflexivity. clearbody LB0.
    lazymatch type of HLAP with ?T => change (id T) in HLAP end. lazymatch type of HFR with ?T => change (id T) in HFR end.
    lx_run_tac (PLANS [0x1eb48] [] 60%N [SUM_calloc1P 32]); lx_tree.
    all: lazymatch type of HLAP with id ?T => change T in HLAP end; lazymatch type of HFR with id ?T => change T in HFR end.
    (* [comment removed for export] *)
    all: (let flt1 := fresh "FLt" in let flt2 := fresh "FLt" in flat constr:(LXHK) 2%nat; flclear LXHK; intros flt1 _; flat constr:(flt1) 2%nat; flclear flt1; intros flt2 _; flat constr:(flt2) 4%nat; flclear flt2; intros h2 HH2 HT2 MF2); change (mo_frame mo moc) in MF;
         lazymatch type of HPX with id ?T => change T in HPX end; lazymatch type of MU with id ?T => change T in MU end;
         lazymatch type of WM with id ?T => change T in WM end; lazymatch type of HLSI with id ?T => change T in HLSI end;
         pose proof (mo_frame_trans _ _ _ MF MF2) as MF9; try rewrite <- TP.
    all: let xmm := constr:(mm) in let xLB0 := constr:(LB0) in lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hl : lawP L xLB0 _ [] ?mc ?mp, Hm1 : munch [] xmm ?mc', Hm2 : munch ?Wl ?mp' mx, Hw2 : wmono _ ?mp'' mx |- _ =>
           (* [comment removed for export] *)
           assert (HPX9 : heap_presx usegs L LB (bv_unsigned sp) X m mx);
           [ eapply heap_presx_trans; [exact HPX|]; eapply heap_presx_trans;
             [ eapply presx_munch; [exact MU| exact WM|]; intros a Ha Hc Ho; cbn [outside] in Ho |- *;
               destruct Hc as [Hs|[Hd|Hb]]; [clear -Hs Ho Ha SLO HLS; lia| clear -Hd Ho Ha DHI ACL SLO HLS; lia| pose proof (in_block_below L LB HBR0 a Hb) as HBL; clear -HBL Ho Ha ACL SLO HLS; lia] |];
             eapply heap_presx_trans; [ eapply (heap_presx_of_munch usegs L); [exact Hm1| assumption| intros a _ _ _; exact I] |];
             eapply heap_presx_trans; [ eapply heap_presx_of_pres_sub; [exact Hl| exact HSUB| clear; lia| clear; lia] |];
             eapply presx_munch; [exact Hm2| exact Hw2|]; intros a Ha Hc Ho; cbn [outside] in Ho |- *;
             destruct Hc as [Hs|[Hd|Hb]];
             [ first [ clear -Hs Ho Ha SLO HLS HLC ACL; lia
                     | match goal with Hc14 : 0 <= alloc_ceiling + (- _ + -32) |- _ => clear -Hs Ho Ha SLO HLS HLC Hc14 ACL; lia end ]
             | first [ clear -Hd Ho Ha DHI ACL SLO HLS HLD; lia
                     | match goal with Hi13 : _ + 32 <= hl_img_lo L \/ _ <= _ |- _ => clear -Hd Ho Ha DHI ACL SLO HLS HLD Hi13 DIM1 DIM2; lia end ]
             | (flat constr:(Hb) 3%nat; flclear Hb; intros b Hb' Hr); destruct b as [Bb kb]; cbn in Hr; pose proof (HLAP Bb kb Hb') as HXl;
               pose proof (in_block_below L LB HBR0 a ltac:(exists (Bb, kb); split; [exact Hb'| cbn; lia])) as HY;
               first [ clear -HXl HY Hr Ho Ha ACL SLO HLS; lia
                     | match goal with Hap : forall b k, In (b, k) xLB0 -> _ |- _ => pose proof (Hap Bb kb (HSUB _ Hb')) as HX end;
                       clear -HX HXl HY Hr Ho Ha ACL SLO HLS; lia ] ]
           | ];
           (* [comment removed for export] *)
           assert (HLSI9 : seq_lseg usegs mx LB0 BUF END init lst);
           [ eapply seq_lseg_mem; [exact HLSI| intros y Hy; eapply seq_lseg_in; [exact HLSI| exact Hy] |];
             intros y cs Hy HR Hsz;
             assert (NEX : y <> lst) by (intros ->; exact (HNL Hy));
             pose proof (blocks_apart_in2 _ _ _ _ _ HAPc (seq_lseg_in _ _ _ _ _ _ _ _ HLSI Hy) HINL NEX) as HXL;
             destruct (HFR y ltac:(apply in_or_app; left; exact Hy)) as (HXC & HXD & HXAP);
             eapply (rw_cells_transport usegs _ _ mx); [| exact Hm2| exact Hw2|];
             [ eapply heap_pres_rw_cells; [exact Hl| |];
               [ eapply (rw_cells_transport usegs _ _ mc); [exact HR| exact Hm1| assumption| cbn; exact I]
               | rewrite Hsz; eapply client_range_block; [eapply seq_lseg_in; [exact HLSI| exact Hy] | clear; lia | cbn; clear; lia] ]
             | rewrite Hsz; cbn [disjoint_from];
               first [ clear -HXL HXC SLO HLS ACL; lia
                     | match goal with Hap : forall b k, In (b, k) xLB0 -> _ |- _ => pose proof (Hap y 32 (seq_lseg_in _ _ _ _ _ _ _ _ HLSI Hy)) as HXN end;
                       clear -HXL HXC HXN SLO HLS ACL; lia ] ]
           | ] end end.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hst : stk _ mx lo _, Hfr : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ => release_frame Hfr Hst (bv_unsigned sp + -128) end end.
    (* [comment removed for export] *)
    all: let xLB0 := constr:(LB0) in lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hl : lawP L xLB0 _ [] ?mc ?mp, Hm1 : munch [] _ ?mc', Hm2 : munch ?Wl ?mp' mx |- _ =>
           assert (HBUF9 : bytes_at usegs mx BUF bs);
           [ destruct bs as [|b0 bs'] eqn:Ebs;
             [ apply bytes_at_nil; clear -BBF; lia
             | rewrite <- Ebs in *;
               assert (HB1 : bytes_at usegs mc BUF bs) by (eapply bytes_at_transport; [exact HBUF| exact Hm1| cbn; exact I]);
               assert (HB2 : bytes_at usegs mp BUF bs)
                 by (eapply (heap_pres_bytes_at usegs L); [exact Hl| exact HB1|];
                     intros a Ha; destruct (CRb a Ha) as [S|[D|B]]; [left; clear -S Ha DS3 SLO HLS; lia| right; left; exact D| right; right; exact B]);
               assert (ALB2 : lst + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= lst)
                 by (eapply client_range_apart; [exact CRBUF | rewrite Ebs; cbn [length]; clear; lia | clear; lia | exact ACL | exact HLC | exact HLD | exact HLAP]);
               first [ eapply bytes_at_transport; [exact HB2| exact Hm2| cbn [disjoint_from]; clear -ALB2 D3 DS3 SLO HLS; lia]
                     | match goal with HO3 : lx_fprop (PROPSP L xLB0) 0 [BUF; _] |- _ =>
                         pose proof (obj_apart L HI _ LB0 LB0 _ _ _ _ BUF (Z.of_nat (length bs)) HH2 ltac:(intros bb Hbb; exact Hbb) DIM1 DIM2 HO3 ltac:(clear; lia)) as APB;
                         assert (HBS1 : 1 <= Z.of_nat (length bs)) by (rewrite Ebs; cbn [length]; clear; lia) end;
                       eapply bytes_at_transport; [exact HB2| exact Hm2| cbn [disjoint_from]; clear -ALB2 APB HBS1 D3 DS3 SLO HLS; lia] ] ] | ]
         end end.
    - (* [comment removed for export] *)
      subst LB0.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hlst : rw_cells _ mx lst [_; _; _; _; C8 (Z_to_bv 64 ?v)] |- _ =>
        match goal with Z1 : 0 <= v, Z2 : 0 <= - v |- _ => replace v with 0 in Hlst by (clear -Z1 Z2; lia) end;
        assert (HLS9 : seq_lseg usegs mx (LBof LB (init ++ [lst])) BUF END (init ++ [lst]) 0);
        [ apply seq_lseg_app; split;
          [ cbn [hd]; exact HLSI9
          | cbn [seq_lseg hd]; split; [exact HINL|]; split; [exact HL16|]; split; [exact HLPOS|]; split; [| exact I];
            exists lt, lpad, ll, lp; split; [exact Hlst| clear -HLBUF; lia] ] |];
        apply aevtM_done; unfold cb_post; flexi 15%nat;
        exists mx, lxmo, h2, (init ++ [lst]), ct, cpad, cl, cp, tagw, zpad, j0, (-106)
      end end.
      split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|]. split; [| assumption].
      unfold inv. rewrite last_last.
      (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption.
      + rewrite HT2; exact HT.
    - (* [comment removed for export] *)
      subst LB0.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : rw_cells _ mx (bv_unsigned sp + -128) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?rest) |- _ =>
        destruct (proj1 (rw_cells_app usegs mx _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] rest) Hm) as [HFRT HFRG]; clear Hm;
        match type of HFRG with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -32) in HFRG by (cbn; clear; lia) end
      end end.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hn : rw_cells _ mx ?N [C4 ?t; CB 4 _; C8 ?w; C8 (Z_to_bv 64 ?pq); CB 8 _] |- _ =>
        assert (HNEW : rw_cells usegs mx N (seq_cells t (Z_to_bv 64 0) (bv_unsigned w) pq 0));
        [ unfold seq_cells; rewrite (Z_to_bv_bv_unsigned w); eapply rw_cells_reshape;
          [ exact Hn | cbv [cells_wf cell_wf]; (flsplit; repeat split)
          | cbv [cells_bytes cbytes]; replace (le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4) by (vm_compute; reflexivity);
            replace (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8) by (vm_compute; reflexivity); reflexivity ]
        | clear Hn ]
      end end.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HNEW : rw_cells _ mx ?N (seq_cells _ _ _ _ 0), Hlst : rw_cells _ mx lst [C4 _; C4 _; C8 _; C8 _; C8 (Z_to_bv 64 ?N')],
                          Hap : forall b k, In (b, k) (LBof LB (init ++ [lst])) -> _, Hal : ?N'' mod 2 ^ Z.of_N 4 = 0, Hpos : 0 <= ?N''' + -1,
                          Hc14 : 0 <= alloc_ceiling + (- _ + -32), Hi13 : _ + 32 <= hl_img_lo L \/ _ <= _ |- _ =>
        pose proof (Hap lst 32 HINL) as ANL;
        assert (HAPN0 : forall B j, In (B, j) LB -> N + 32 <= B \/ B + j <= N) by (intros B j HBj; apply Hap; apply HSUB; exact HBj);
        assert (HLS9 : seq_lseg usegs mx ((N, 32) :: LBof LB (init ++ [lst])) BUF END ((init ++ [lst]) ++ [N]) 0);
        [ apply seq_lseg_app; split; [apply seq_lseg_app; split|];
          [ cbn [hd]; eapply seq_lseg_mem; [exact HLSI9| intros y Hy; right; eapply seq_lseg_in; [exact HLSI9| exact Hy] | intros y cs Hy HR Hsz; exact HR]
          | cbn [seq_lseg hd]; split; [right; exact HINL|]; split; [exact HL16|]; split; [exact HLPOS|]; split; [| exact I];
            exists lt, lpad, ll, lp; split; [exact Hlst| clear -HLBUF; lia]
          | cbn [seq_lseg hd]; split; [left; reflexivity|]; split; [change (2 ^ Z.of_N 4) with 16 in Hal; exact Hal|]; split; [clear -Hpos; lia|]; split; [| exact I];
            exists (Z_to_bv 64 tb), (Z_to_bv 64 0), (bv_unsigned Lw), q; split; [exact HNEW| clear -Hq HqL LR; lia] ] |];
        apply aevtM_done; unfold cb_post; flexi 15%nat;
        exists mx, lxmo, h2, ((init ++ [lst]) ++ [N]), ct, cpad, cl, cp, tagw, zpad, j0, 0;
        split; [reflexivity|]; split; [reflexivity|]; split; [left; reflexivity|]; split; [| assumption];
        unfold inv; rewrite last_last; rewrite LBof_snoc; rewrite (hd_app_ne (init ++ [lst]) [N] 0) by (destruct init; cbn; congruence);
        (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption;
        [ rewrite HT2; exact HT
        | apply List.NoDup_app; [exact HND| constructor; [intros HIn; destruct HIn| constructor] |];
          intros y Hy HyN; destruct HyN as [EyN|[]]; subst y;
          apply in_app_or in Hy; destruct Hy as [Hy|[Hy|[]]];
          [ pose proof (Hap N 32 (seq_lseg_in _ _ _ _ _ _ _ _ HLSI9 Hy)) as HNN; clear -HNN; lia
          | subst lst; clear -ANL; lia ]
        | intros y Hy; apply in_app_or in Hy; destruct Hy as [Hy|[<-|[]]]; [exact (HFR y Hy)|];
          split; [clear -Hc14; lia|]; split; [clear -Hi13; lia| exact HAPN0]
        | destruct HBUFOK as [(_ & _ & E)|HB]; [exfalso; destruct init; discriminate| right; exact HB] ]
      end end.
  Qed.

End Walk.
