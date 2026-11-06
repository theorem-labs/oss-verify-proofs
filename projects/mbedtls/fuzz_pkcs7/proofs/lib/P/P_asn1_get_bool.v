(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02c7d2b6d4f5a8e0 0 2 0 1 11 1P03798850003393d1 0 2 0 1 2 1P04c3be4bf132856f 0 3 0 1 20 1 26 1P06864a95013925d4 0 2 0 1 3 1P0737ef21dca508e6 0 2 0 1 11 1P08b53b6afc5427ba 0 4 0 1 13 1 15 1 16 1P0a3e390e60c2f0cf 0 2 0 1 28 1P0b31ef7ef45a4e0a 0 3 0 1 4 1 23 1P127ec1feae0b4521 0 4 0 1 2 1 3 1 20 1P12f8ae04b467bee0 0 2 0 1 3 1P1498dd37ba7134e5 0 4 0 1 13 1 15 1 16 1P14d06196a5a81ebd 0 2 0 1 3 1P1597fef264f4907d 0 2 0 1 2 1P16042baf946a5bd1 0 2 0 1 21 1P193e8e7eaedc7799 0 2 0 1 32 1P19f9ee3d68230b98 0 2 0 1 5 1P1b4603e6eeaa32d4 0 5 0 1 18 1 21 1 22 1 24 1P1c953f2f787f801f 0 4 0 1 6 1 23 1 24 1P1cc5833c97bc9d90 0 2 0 1 2 1P1d0b7ade5bd00752 0 2 0 1 19 1P2178026fb4d84044 0 2 0 1 1 1P2196c8aba7bf2eb0 0 2 0 1 2 1P2277922a3cd1f325 0 2 0 1 1 1P23e8c45373b4ef1f 0 2 0 1 1 1P2411cae798331a31 0 3 0 1 16 1 21 1P2639b64076b0f1c0 0 2 0 1 5 1P26bf1ee633dcc25e 0 2 0 1 32 1P273201024ccdbb4a 0 3 0 1 1 1 24 1P273999638b2c6d69 0 2 0 1 1 1P2a957924f5880d41 0 2 0 1 1 1P2e27ed9e1fa78d25 0 2 0 1 1 1P2ed5dcc267976977 0 5 0 1 11 1 13 1 15 1 16 1P2f4a388c2e5215b1 0 5 0 1 20 1 23 1 24 1 26 1P31084b2a96d40ddf 0 4 0 1 12 1 14 1 17 1P317762d96078c727 0 2 0 1 2 1P327e13b44a656f66 0 4 0 1 12 1 14 1 17 1P33da48dce92b58de 0 3 0 1 12 1 14 1P34087292e7052dc2 0 2 0 1 2 1P34baf49bb9293627 0 4 0 1 9 1 11 1 14 1P365fb05c3842884c 0 5 0 1 14 1 17 1 18 1 20 1P36e05fe0562f35f0 0 2 0 1 31 1P37bd00f6daa8eab8 0 3 0 1 10 1 15 1P37f768e4dc965718 0 2 0 1 25 1P38215929a4ee1d23 0 5 0 1 19 1 22 1 23 1 25 1P39a1dfea904bfd51 0 2 0 1 26 1P39fc184da726363a 0 3 0 1 1 1 19 1P3a84a68d473fab10 0 2 0 1 2 1P3b6dcaf6cf192e41 0 4 0 1 2 1 3 1 25 1P3b88f4d382c36e95 0 5 0 1 11 1 12 1 14 1 17 1P3b8b79fbae13751a 0 5 0 1 11 1 13 1 15 1 16 1P3c8bcdfb26fd09d7 0 2 0 1 27 1P3ee9241c5d20bbce 0 6 0 1 13 1 15 1 16 1 17 1 18 1P3f070c09a684295f 0 2 0 1 2 1P3fd37aa21790aa59 0 2 0 1 33 1P3fe227ba0b00944d 0 5 0 1 11 1 12 1 14 1 17 1N002ac21413b2bf33N00375ffaf7944f69N005aa69be8f5d67cN0099849e5b407a33N00a181713d3050bfN00ceb59236b30a58N00e0da4be32fb140N00f0a540ffa089caN013ae6f80fdcaa9fN016648e58e55bed4N01b195b8c8e2e917N01c1b49f910325bfN01c637430352a68fN01c8d27dcdc8686aN01cae47aa5c3c03dN01cbe0da05b71b06N01dd99eb20100116N01ef402015afda97N02211346427a85c4N0227e56cf6d6f665N03111046cf4c7321N03505cc67a382468N035e194ef5c0421dN041937dbeda75d57N044e290bf911707dN0470e9d8b43db386N0481355c9f9e2791N049dde793f081b64N050713a145373068N0515cec1aea273aeN052bfe607390323cN0571b7daec1b5d36N05bcd7d0cfeb931cN05be449d797fc806N05eeb396a9021886N05fb72440bb46f2aN06bcb49d3ecb571aN06ce57b9a421a7ebN0748ccb42f327edeN07c0e2f193b95d8aN07cbace0c708e9dcN083ad12c36fcc432N088a8b7e993f0b03N089ab3efd9321d4aN097020ca23f72e04N09b4dc26fadfc16aN0a2834ed37bda3e5N0a339c8465b2ef76N0a6c5bb2b4704728N0ab037c676c689eeN0b05b0f22eb1266bN0bc58a688fb76ba3N0bff07144152f5a1N0c1337ef51b01f55N0c2e5d6213b723a5N0c5ef817adea01baN0ca18de3c003eb51N0d58504b950ac31aN0d5b5a7f63929471N0d5b899c94d50129N0d76f510e2d8a73eN0d9954a1a8f6b59fN0dbd5c4094fb2865N0dc61332bca1947eN0df2e0372bcac25eN0df644dcae498704N0e1c19db35d12377N0e902d6c6e29d17aN0e9126c5a520250bN0eb13db9a2634b28N0eba7a4e702f657eN0ec631b9528092e9N0f0e5bdbc600f4c8N0f79642790d15342N0fdda09460bbfc18N1012699ffdbb8209N102aa41cec6170eaN10596d163f15da23N10f04959dfaea186N115313e8b9014b75N116332d63026583fN11c9f09dc5d691f6N1279f0c4bb288d61N12e207e7a54c868aN13122d3db64b9838N13419e1f6470070bN137471fa70221542N13bc14ce3bd09818N143fab3c542e0bf8N14c5810d37053b1aN14f12e33e2633ff7N151aae68abf0d363N153537602351af24N15454863fb7ad5b2N157eab31e9262765N15acaa297c2ba3dfN1635fde70d03062bN1637a961ec8058fdN167605c9240f0d4fN16b449fe71d097b4N16c317717a712e73N171c767fcf6af9c1N1758917b11e0941cN1762403b7c91d6e9N17ecc206e7cbee7dN17fa98a882fa6acaN191e4dd45f6ee400N1946a160da0d15a6N1959a341802f2186N19639dd88122c5bcN197f2b83962dd069N19c1942cf6269555N19f15be35b55912aN1a0025aaa159bb24N1a30615a494229b6N1a5765dfbd8e8577N1a60741d2e32b7a2N1a881083b24599d6N1aa77591d6573fdeN1ae33ab8f9e8ded3N1b4070c782942762N1b5f930c9627af36N1ba9e978a079f1a6N1bfadefcc79321fdN1c281f0bdfee8709N1c3ef97216b8b25dN1cb5f29bf3e165aaN1cdfc97870d5e06aN1d2e3fa85d5c1a09N1d451bb32d70649cN1d67d5c7c9520adaN1e06ccd4f7f992afN1e440a2f471e04fcN1e6e4c87d1586912N1e6fcee83bd2f0b7N1e77c5496b70faefN1ea4e7f7daf942bbN1eb67730b1f22889N1f8e16c2a489bb44N200e85fa5ecb39f6N20df180109cd7610N20ef0f54f5fae1abN214d4e91a533ed78N21dbeb74f89c4befN22294e8ccf9a37f6N22311164c874c616N223bc3958796ce88N227d632859d78968N22a27f294961ca18N22a9c8f8552896d2N22b1bee2c72bc039N22d3a8246fec662aN2356f772b5f4129dN236e2c9ff1cb1cf5N23b5ad70315d2420N23c8e231668b6cddN2409950058a03864N24670aae56b71b7aN250a8c0c6b95f10cN260229e71f0c141fN2648b948a7425e43N26c3c953c2282997N26ee4dbd67e13eceN2783a41841c0739cN27c848b86aa32244N27d2be790b4d5aacN27fc8d3f80720accN281c9decfaec0c2dN2855474b60d1569fN2876efcb1ddd7714N288ae8c1eca3ea51N289656e22fa7f808N29143035050c168bN2994303510a8d7c4N2994794ee69f658aN29bc2e93e78582a5N29c7eea315bbf74eN29e1c31722adc818N2a07cec59d3e9262N2a2fc425590ee215N2a30fbd9e8a8e8a9N2a6bbdca3312d6ebN2a8336e17bddc6ebN2a950931cdf53f31N2b363d15cce9ba9aN2b3e1b4bdb01f49dN2b67e98c852a917fN2ba0428d30c14997N2bcf30bbe6969a2fN2bcf6c797094c5beN2c0184df75051996N2c375c689f6bf001N2c9a36969870c034N2ccf49f9f2924d08N2cd264d8cb375404N2d17a2273133c688N2d44c4d3304b588aN2d464b6ac7188a6bN2d506b201e1c636eN2d795fbd9b5c0235N2d9562db722c9474N2ddcb2d21d3b8b1cN2e231a44408dd26dN2e2509a72f7881acN2ecbe6a9b67d3843N2f3d05d9b78d46e5N2fa3a1042f7e7c80N303ad96654688304N30d79cd8ddf0a995N30ef7566a422a87aN31b8af0412cd4d2aN321465564449433bN3228b1badd3e3ac3N3268076f9f743ec6N3295939f9b88129cN32c22044560ccd7fN32df7c9085716675N32f861fadbec0de2N330eb8dd6e498db3N3330252329c03eabN3355ae68977f1054N3367a8f3c7be2993N33728246bf32fbdaN339db2292188cf56N33b4b66e8e6971e9N33e7693712b98c63N33e814c7aa8b9344N340e1ea92d067cb3N341b451efac31259N348b6673182a20cbN348ff4eda01ce6eaN349ada007a763865N34c63a4fb999c6deN34fabfe16a56207cN3580d6f0318062e2N365230cb9c861d90N3667379ec2f7d657N368b95ffa9d99701N36b5a4634dcbeafdN36d9efc831c787beN374cf37f22fc2f74N37a60c0c04d2c90bN37c0e8a36157eeddN380db8d43c82f81cN38511a84407f4b3cN38af8d34f6ee3d52N38bf05c547136e20N39394678805fb6c1N3965a8086275b7caN39c039f3df7f6df7N3a1925a14b1031ccN3a3335f6a743100eN3a4400b4fb6319e8N3a595e94bbede6dfN3a5ad963846b0ac5N3a812dfa76753a7eN3a92bfb093e7c660N3a98bef39181009cN3bd5fd4f02184c55N3bf1096132f4771cN3c4f6b58e5f3804eN3c7742140f42ccf6N3cc4170164a78559N3cfe05b85caa16f4N3d0c3a25de91e901N3d15a6abe31d2ddbN3d5ce1f817835e6eN3d61f1acf3ddd014N3d91735fbe5a7eacN3e535f6a7cd35dc5N3e5c6defa620435bN3e9657f71e1ff4b0N3e99bbe2bf056241N3eca1758250fa6d8N3fb03535fb340f83N3fbaa4b72952ceff"%lxh.
Ltac2 gd_tbl_P_asn1_get_bool () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Frame.stk"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Exec.evt"; "asn1_get_bool_post"].


Definition P_ASN1_GET_BOOL : Z := 0x1df54.

(* [comment removed for export] *)
Notation ASN1_GET_BOOL_STACK := 32 (only parsing).

Definition asn1_get_bool_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP VALP P END lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bool ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Lv,(2.&40.)(5.(6.$0.R14.(7.(8.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(9.O18.)O7.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+8.))(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)+20.)(12.&40.O17.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(5.(17.-7?.R3.)(18.R3.=))(5.(19.O19.R4.O6.(=.$1:.(1;.(16.&40.R2.))(13.$1:.)))(5.(19.O19.R4.O5.(=.$1:.(1<.R1.)(13.$1:.)))(5.(1=.O19.R4.O2.(12.&40.O17.))(5.(5.(18.O4.R2.)(18.R2.O3.))P,(6.$4.R3.=)(18.(10.O4.+3.)R3.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_bool_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP VALP P END BUF lo : Z) (bs : list byte) (valv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m VALP [C4 valv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= VALP \/ VALP + 4 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP) ->
  (* [comment removed for export] *)
  PP mod 8 = 0 -> VALP mod 4 = 0 -> 0 < PP -> 0 < VALP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_BOOL_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (VALP + 4 <= lo \/ bv_unsigned sp <= VALP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 VALP ->
  evt segs (asn1_get_bool_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_BOOL_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_bool_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).


  (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bool ()) "Pk,$1>.Pcur,$4.Pstop,$4.PL,(2.&40.)Pvalv,(2.&40.)Px5,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))P,(6.$1>.(1?.(11.R6.R7.))R8.)P,(5.(18.(10.VP,+2.)R8.)(17.R8.R7.))P,(18.R8.VEND,)P,(19.$20.R4.VPP,(=.$1:.(1;.(16.&40.R:.))(13.$1:.)))P,(19.$20.R5.VVALP,(=.$1:.(1<.R8.)(13.$1:.)))P,(21.$20.R6.VBUF,Vbs,)P,(1=.$20.R7.Vlo,(12.&40.Vsp,))P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VVALP,(10.VVALP,+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+20.)(12.&40.Vsp,))(13.(>.$4.$4.)))))Vm,R8.)P,(14.$20.Vm,R9.)P,(15.$20.R:.)(22.$20.(23.$20.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VVALP,VP,VEND,Vlo,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,R=.Vt1,Vt2,Vs0,Vs1,(16.&40.-60.)(16.&40.VEND,)(16.&40.VVALP,)(16.&40.VPP,)(16.&40.R11.)(16.&40.R10.)R?.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>00<.)Vfc,(:.(2.&40.))R;.(;.$20.)))")
(* [comment removed for export] *).
  Proof.
  induction k as [|k IH]; intros cur stop L valv x5 x17 mm Hk Hcur Hstop HPP HVAL HBUF ST MU WM MI; [lia|].
  destruct (nth_error bs (Z.to_nat (cur - BUF))) as [b|] eqn:NB; [| apply nth_error_None in NB; lia].
  read_at HBUF NB (cur - BUF) RD.
  lxp_run (PLAN [0x1df54; 0x1e00c] [(0x1dfe0, DMerge 0); (0x1e028, DMerge 10)] 74%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 122892; (lxp_apply (IH (cur + 1) stop)) | lxp_ret ].
Qed.

End Walk.

Lemma P_asn1_get_bool_spec {L : heap_layout} : asn1_get_bool_stmt psegs P_ASN1_GET_BOOL.
Proof.
  unfold asn1_get_bool_stmt, P_ASN1_GET_BOOL.
  intros until valv.
  intros HPP HVAL HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof (munch_refl [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_BOOL_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HVAL) as VALB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, VALB.
  pose proof (proj1 HBUF) as BUF0.
  lxp_run (PLAN [0x1e00c] [(0x1dfe0, DMerge 0); (0x1e028, DMerge 10)] 74%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 122892; lxp_longform nn; lxp_apply loop_walk | lxp_ret ].
Qed.
