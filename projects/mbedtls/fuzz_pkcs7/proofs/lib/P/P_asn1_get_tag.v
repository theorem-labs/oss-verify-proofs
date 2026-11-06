(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0063273675b5f2a3 0 2 0 1 33 1P030d62793748a38c 0 2 0 1 22 1P07752bfbcf1e44e3 0 2 0 1 2 1P08592bc93b6cea2f 0 2 0 1 28 1P088094697fc5bded 0 2 0 1 32 1P0bb02bc07ed6c5f3 0 4 0 1 6 1 19 1 20 1P0d1a2eee71d3bdf8 0 2 0 1 6 1P0d84ae59ad6aa129 0 4 0 1 10 1 12 1 15 1P0eca03315acdf2c4 0 2 0 1 9 1P112cf9ca3db55de7 0 2 0 1 32 1P1485a92cfcf792be 0 2 0 1 9 1P155694524555f485 0 3 0 1 10 1 12 1P159262602915fff2 0 4 0 1 11 1 13 1 14 1P15ed9e8df53eefba 0 2 0 1 1 1P18cb8816c9323ef3 0 5 0 1 9 1 10 1 12 1 15 1P197e0daeef21db58 0 5 0 1 15 1 18 1 19 1 21 1P1e5f201d7ecd43e0 0 5 0 1 20 1 23 1 24 1 26 1P221143f5b512f9e2 0 2 0 1 31 1P22401609a15ba29b 0 4 0 1 10 1 12 1 15 1P22b3d2be5e49edf0 0 3 0 1 1 1 15 1P23c5cc4f63e99aa7 0 2 0 1 25 1P25d09c9f64878a05 0 2 0 1 15 1P2d69facdfcc68022 0 5 0 1 9 1 11 1 13 1 14 1P2dfbf8e5a5ed9376 0 2 0 1 1 1P2e71041e4de3ad5e 0 6 0 1 11 1 13 1 14 1 15 1 16 1P2e77dfa69329a49f 0 5 0 1 9 1 10 1 12 1 15 1P2f05a4dc777984cd 0 5 0 1 21 1 24 1 25 1 27 1P30162eb1e4424f81 0 2 0 1 1 1P3065f8388d10154c 0 3 0 1 4 1 23 1P3516d79d23d71116 0 3 0 1 16 1 22 1P3534d55b7e8e2cdc 0 3 0 1 8 1 13 1P3549e183ed5514bb 0 4 0 1 11 1 13 1 14 1P37dafbac8df18dd2 0 3 0 1 1 1 20 1P383c9e1556a1f9a4 0 2 0 1 2 1P39dbb75db7eca8d3 0 2 0 1 5 1P3a6b6704e235483a 0 2 0 1 17 1P3c9352e8759db75c 0 2 0 1 2 1P3cecb3f7959a1a37 0 2 0 1 5 1P3e75e8674c398d64 0 5 0 1 10 1 13 1 14 1 16 1P3f0b6cdc7709cb23 0 5 0 1 9 1 11 1 13 1 14 1P3fd607af045dcf90 0 4 0 1 7 1 9 1 12 1N0006edb77c01d982N001e447a67b25299N00962f8da79a21a7N01998f3f58c0f40fN02252ea087e9843fN025ce7e1f64d2d21N03cb90094f18d3ceN03d6138c744c0bc3N04bae344a5e9c62fN04e13e1099ec39b9N057fc9ca549f25a9N064c83fcc9665778N06b9f273ed7ab9c8N06e1475c675a3726N071c892b1d686f2eN07f2727e05eb075eN0802415de10c8bb3N080f4c737dbd4f5bN08e2100708c6bb7dN08f275de55aad292N0903bdb6a687260dN0905777c67fff2a8N095f764eb1d896cbN099a11793e5aff1eN09c9b71d4be17dd2N0b42cfe4cbf601d5N0c60aee0fefded53N0cb68d25406255a0N0f74c7221b51285cN10029ebda707ed51N102588b329e80ae0N1083757af1f9d08bN11690d1fa3f61a4fN11d7c9929c1dc3ceN12f683d63f6e14f3N13ac3d8fa7f8a861N13c8f6880f01cb20N1513071486708a1eN153a74f18bd96430N158fb791e476df2dN15a9432ca9be08baN16160fe559cec9c1N1624e561c97db944N163d8f49067ecff6N16f4b22edcd4998fN16fdf97a41f1ffffN17211545fa02a22cN18923f2b40cedb0dN189ec270b08ad22cN1986ad51b41910dcN19bfea6e6665d510N19ef82e5ca6459a0N19fabab57e8fccfbN1a038a8141494673N1a361ce2457d472fN1b0d67f7d620faceN1c562ce73938e27bN1dcc29ece1dff2daN1de006b1e0005873N1e1908b021144a2aN1e4f9cb3d002d95bN205adcca09a160a8N20762b733ef616dcN2219a6b6ff736eb4N22856ba2dc83b30fN240ac57633db5ed2N24477041cb42fb92N24a5ea9113fa608eN24b24094f1d963f3N24cf7b94ef34f12dN24ef92d45ed659cbN25aac5f86db6e90aN26cdbd1b5ff9d328N27b7b215233f58eeN2833ea7fe8cde5f1N2839c9128c47267fN28e59638e3a7bb65N293c72370a1faeacN29587e78ef56f290N295f4b9ff61d0b55N29c5b657ba758e95N2aa1f7b4a4dc1403N2c672b601d3c0edbN2e87310c96075745N2f8eb611572be6e5N2fb6bc6a27fb96ebN30d8cd48d9ad346cN33253276ba3798c1N33b0051b6d44150aN34606de0200ddb0bN34c2efeea8bd9146N352bac2b5ab3c179N3579fde58cf709c5N361bbed0f54adfd7N36b80b7ba17525beN3763ae164eb0b9adN37c98cde3ec9434dN37eafe38dbfc9419N38ced8b1971b3863N38f237f4895afc6fN394070f8333f5abdN39e3256e43143673N3a32bfeb2e599afaN3a736e98216cdeddN3b16a03c768b0f3aN3b2348408981831aN3b2fb1f08348054eN3b7b36cc26698743N3c1d13db00aaf302N3c9d1c3b6b9aa100N3d51d04c1f6b2040N3ee18225df5afa83N3f8c9c4c0629b950"%lxh.
Ltac2 gd_tbl_P_asn1_get_tag () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Exec.evt"; "asn1_get_tag_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.P.PImg.psegs"].


Definition P_ASN1_GET_TAG : Z := 0x1de90.

Definition asn1_get_tag_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP LENP P END : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(5.(6.$0.R14.(7.(8.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(9.O17.)O6.(:.(2.&40.))R4.(;.O18.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+8.))(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+8.))(11.(>.$4.$4.))))O1.R4.)(5.(12.O18.O1.R4.)(5.(13.O18.R4.)(5.(6.(2.&40.)R10.(14.&40.R3.))(5.(5.(15.-7?.R3.)(16.R3.=))(5.(17.O18.R4.O5.(=.$18.(19.(14.&40.R2.))(11.$18.)))(5.(17.O18.R4.O4.(=.$18.(19.R1.)(11.$18.)))(5.(5.(16.O3.R2.)(16.R2.O2.))P,(6.$4.R3.=)(5.(16.(10.O3.+2.)R3.)(16.(1:.&40.R2.)(1;.O2.R3.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_tag_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PLENP,$4.PP,$4.PEND,$4.PBUF,$4.Pbs,(1=.(2.&8.))Plenv,(2.&40.)Ptag,$4.P,(17.O2.R9.R8.(=.$18.(19.(14.&40.R6.))(11.$18.)))P,(17.O2.R:.R8.(=.$18.(19.R3.)(11.$18.)))P,(1>.O2.R;.R6.R5.)P,(16.R7.R9.)P,(16.R:.R9.)P,(16.R:.(10.R9.(1?.(20.(2.&8.)R8.))))P,(15.(10.R:.(1?.(20.(2.&8.)R9.)))(21.+2.+3?.))P,(22.(16.(10.R?.+8.)R>.)(16.(10.R>.+8.)R?.))P,(22.(16.(10.R10.+8.)R<.)(16.(10.R<.(1?.(20.(2.&8.)R;.)))R10.))P,(22.(16.(10.R10.+8.)R=.)(16.(10.R=.(1?.(20.(2.&8.)R<.)))R10.))P,(6.$4.(23.R12.+8.)=)P,(6.$4.(23.R12.+8.)=)P,(15.=R14.)P,(15.=R14.)P,(15.=R12.)P,(13.O2.R18.)P,(6.(2.&40.)R31.(14.&40.R18.))P,(6.(2.&40.)R31.(14.&40.R16.))P,(6.(2.&40.)R31.(14.&40.R19.))P,(6.(2.&40.)R31.(14.&40.R14.))(24.O2.(25.O2.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1<.R1;.R1:.R19.R1=.)(7.(8.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(14.&40.O1.)R1>.(:.(2.&40.))R1=.(;.O2.)))")
(* [comment removed for export] *).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF : Z) (bs : list byte) (tag : Z).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation POST := (asn1_get_tag_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END m).


  (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Pk,$26.Pcur,$4.Pstop,$4.PL,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px5,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(6.$26.(27.(1;.R6.R7.))R8.)P,(5.(16.(10.VP,+2.)R8.)(15.R8.R7.))P,(16.R8.VEND,)P,(17.$28.R4.VPP,(=.$18.(19.(14.&40.R:.))(11.$18.)))P,(17.$28.R5.VLENP,(=.$18.(19.R9.)(11.$18.)))P,(1>.$28.R6.VBUF,Vbs,)P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VLENP,(10.VLENP,+8.))(11.(>.$4.$4.))))Vm,R7.)P,(12.$28.Vm,R8.)P,(13.$28.R9.)(24.$28.(25.$28.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(14.&40.VPP,)(14.&40.VEND,)(14.&40.VLENP,)R>.(14.&40.R10.)(14.&40.R?.)R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,R;.Vt6,)VF,(14.&40.+1=?34.)Vfc,(:.(2.&40.))R:.(;.$28.)))")
(* [comment removed for export] *).
  Proof.
  induction k as [|k IH]; intros cur stop L x16 x17 x5 mm Hk Hcur Hstop HPP HLEN HBUF MU WM MI; [lia|].
  destruct (nth_error bs (Z.to_nat (cur - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  pose proof (u8ro_read psegs mm BUF bs (cur - BUF) b _ HBUF NB ltac:(lia) eq_refl) as RD.
  lxp_run (PLAN [0x1de90; 0x1df34] [(0x1dee0, DMerge 14)] 69%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 122676; (lxp_apply (IH (cur + 1) stop)) | lxp_ret ].
Qed.
End Walk.


Lemma land_127_range : forall x, 0 <= Z.land (Z.land x 255) 127 <= 127.
Proof.
  intros x. split. apply Z.land_nonneg; right; lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. rewrite Z.ones_equiv.
  pose proof (Z.mod_pos_bound (Z.land x 255) (2^7) ltac:(lia)) as H. change (2^7) with 128 in *. cbn. lia.
Qed.

Lemma longform_n : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_tag ()) "Pnn,$4.P,(5.(16.=R1.)(16.R1.+7?.))P,(16.+???????????????<.(23.(10.R2.-5.)+10000000000000000.))(5.(16.+1.R3.)(16.R3.+4.))")
(* [comment removed for export] *).
Proof.
  intros nn NR Kn.
  destruct (Z_lt_le_dec nn 5) as [Hl|Hl]; [| rewrite Z.mod_small in Kn by lia; lia].
  destruct (Z_le_gt_dec nn 0) as [Hz|Hz]; [| ].
  - exfalso. assert (E0 : nn = 0) by lia. subst nn. vm_compute in Kn. exact (Kn eq_refl).
  - replace ((nn + -5) mod 18446744073709551616) with (nn + -5 + 18446744073709551616) in Kn; [lia|].
    rewrite <- (Z.mod_small (nn + -5 + 18446744073709551616) 18446744073709551616) by lia.
    rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Section Main.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF : Z) (bs : list byte) (tag : Z).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Notation POST := (asn1_get_tag_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END m).

End Main.

Lemma P_asn1_get_tag_spec : asn1_get_tag_stmt psegs P_ASN1_GET_TAG.
Proof.
  unfold asn1_get_tag_stmt, P_ASN1_GET_TAG.
  intros until tag.
  intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 MI -> -> -> ->.
  pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0.
  lxp_run (PLAN [0x1df34] [(0x1dee0, DMerge 14)] 69%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 122676; lxp_longform nn; lxp_apply loop_walk | lxp_ret ].
Qed.
