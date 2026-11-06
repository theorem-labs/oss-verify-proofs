(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import AKitRV W_bnum0.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4bool46Stdlib6ZArith6BinInt1Zjb3leb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB9BJIfaceU8~~~~~~l95u8lenjb2le37Corelib4Init5Logicq63andq62eqjb2ltjb3divq63not04Npos35stdpp9bitvectorbdefinitionstc2bv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsvedmachine_state3h5LinuxProcessSemantics5Riscv7Preludehk55bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB6AKitRV~~~~~~hn42rv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~hr73memjb3addhc4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ig84cellq62ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~il15asegshn43rsphc4prodig82C1hc3nilhc4pairtcbbv_unsignedhn43rgphn43rrahn43rs0hn43rs1hn44rs10hn44rs11hn43rs2hn43rs3hn43rs4hn43rs5hn43rs6hn43rs7hn43rs8hn43rs9hn43rtp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jif8rw_cellstc7Z_to_bvhc4Nonehn44mkRrig82C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jp55munchjp53stkjp55wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jua2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kid7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kn27seg_romjb3powhc4Somehc6optionhn43ra0hn43ra189OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB9BJIfaceU83HCW~~~~~~ku0bu8leaf_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7W_bnum0~~~~~~lj33sh879OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsConst~~~~~~ln86ACONST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~lrf4aapplrf5aceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~mge3evtkid3mrdkid2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~mld2b8jb6modulo" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition u8len : ltac2:(zQ "10!h9>2cp$0$0") := ltac2:(zQ "30!j4!h9!l3\2cp$1M0\0$0$1@2$2^1+nf+1M0\0$0$1@2$2^1+nvf+2M0\0$0$1@2$2^1+vvvf+3+4").
Lemma u8len_range : ltac2:(zQ "40!p9!q1!ra!h9>2cp$3@2$2@2$1+1@1$0^1@2$1@1$0^1+4").
Proof. intros cp. unfold u8len. destruct (cp <=? 127); [lia|]. destruct (cp <=? 2047); [lia|]. destruct (cp <=? 65535); lia. Qed.
Lemma u8len_bmp : ltac2:(zQ "30!q1!h9!p9>2cp$1>0@2$0^1+vvvf@2$0@1$2^2+3").
Proof. intros cp H. unfold u8len. destruct (cp <=? 127); [lia|]. destruct (cp <=? 2047); [lia|]. rewrite (proj2 (Z.leb_le _ _) H). lia. Qed.
(* [comment removed for export] *)
Lemma u8len_1 : ltac2:(zQ "40!h9!s0!p9!q1>2cp$0>0@2$3^1+nf@3$1$0@1$2^2+1").
Proof. intros cp H. unfold u8len. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.
Lemma u8len_2 : ltac2:(zQ "50!h9!s0!p9!q1!s5>2cp$0>0@2$4+nf^1>0@2$3^2+nvf@3$1$0@1$2^3+2").
Proof. intros cp H1 H2. unfold u8len. rewrite (proj2 (Z.leb_gt _ _) H1). rewrite (proj2 (Z.leb_le _ _) H2). reflexivity. Qed.
Lemma u8len_3 : ltac2:(zQ "60!h9!s0!p9!sa!q1!s5>2cp$0>0@2$4Z^1>0@2$5+nvf^2>0@3$1$0@2$3^3+hggg0Z@3$1$0@1$2^4+3").
Proof. intros cp H0 H1 H2. unfold u8len. rewrite (proj2 (Z.leb_gt cp 127)) by lia. rewrite (proj2 (Z.leb_gt cp 2047)) by lia.
       rewrite (proj2 (Z.leb_le cp 65535)); [reflexivity|]. Z.div_mod_to_equations. lia. Qed.
Lemma u8len_4 : ltac2:(zQ "60!h9!s0!t0!p9!sa!q1>2cp$0>0@2$5Z^1>0@1$2@3$1$0@2$4^2+hggg0Z@3$1$0@1$3^3+4").
Proof. intros cp H0 H2. unfold u8len. assert (65535 < cp) by (Z.div_mod_to_equations; lia).
       rewrite (proj2 (Z.leb_gt cp 127)) by lia. rewrite (proj2 (Z.leb_gt cp 2047)) by lia. rewrite (proj2 (Z.leb_gt cp 65535)) by lia. reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition u8leaf_post : ltac2:(zQ "70!h9!t6!v9!hj5!hmb!hr1!hv4>1r$5>1F@2$4@1$1#5@1$2@1$1#k0>2fc@1$2@1$1#i0>1m$6>2lo$0>3raz$0>2ff$0>2sz$0>2cp$0>0$3P") := ltac2:(zQ "if0!t6!v9!ra!h9!s0!hvb!ig1!ik4!ikc!ioc!ip5!ipc!iq3!iq9!iqf!hr1!hv4!ir6!hj5!is4!isb!it2!it9!iu0!iu8!iv0!iv7!ive!jg5!jgc!jh3!jha!ji1!ji8!jma!jn6!jo0!hmb!jo7!p9!jof!jt1!jta!ju1!ki7!km7!kr1\1r$f\1F@2$i5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$h0\2lo$3\3raz$3\2ff$3\2sz$3\2cp$3\2ms$h2@2$8$f\2r'$f@2$8$h0\2m'$h0@2$8@1$1@1$0#8\2x0@1$1@1$0#8@2$8@1$1@1$0#8\2x1@1$1@1$0#8@2$8@1$1@1$0#8\2x2@1$1@1$0#8@2$8@1$1@1$0#8\2x3@1$1@1$0#8@2$2@3$4$h2^7@7$ic@1$i6^6^f@2$i3@1$0#k0^b^e@1$i4@1$1@1$0#k0^5@1$ie$9@2$2@3$i9@3$6@2$b$3$3@4$e$3$3@2$5@2$h1@1$0#k0@1$a^h0-h0@2$h1@1$0#k0@1$a^h0@3$6@2$b$3$3@4$e$3$3@2$5^a+hi0@2$5^a+hi8@3$6@2$b$3$3@4$e$3$3@2$5@2$5^a+i0^9@2$5@2$5@2$5^a+i0^9+4@1$d@2$b$3$3^d^5@2$2@3$ib$9^d^5@2$2@2$id$9^5@2$2@4$ia$9^5^c@2$h1@1$0#k0@1$a^h0@2$2@3$4@1$1@1$0#k0@1$a^6@1$a^h0@2$2@3$4@1$1@1$0#k0@1$h3^6@1$h3^h0@2$2@3$4@1$1@1$0#k0@1$i1^6@1$i1^h0@2$2@3$4@1$1@1$0#k0@1$h4^6@1$h4^h0@2$2@3$4@1$1@1$0#k0@1$h5^6@1$h5^h0@2$2@3$4@1$1@1$0#k0@1$h6^6@1$h6^h0@2$2@3$4@1$1@1$0#k0@1$h9^6@1$h9^h0@2$2@3$4@1$1@1$0#k0@1$ha^6@1$ha^h0@2$2@3$4@1$1@1$0#k0@1$hb^6@1$hb^h0@2$2@3$4@1$1@1$0#k0@1$hc^6@1$hc^h0@2$2@3$4@1$1@1$0#k0@1$hd^6@1$hd^h0@2$2@3$4@1$1@1$0#k0@1$he^6@1$he^h0@2$2@3$4@1$1@1$0#k0@1$hf^6@1$hf^h0@2$2@3$4@1$1@1$0#k0@1$i0^6@1$i0^h0@2$2@3$4@1$1@1$0#k0@1$h7^6@1$h7^h0@2$2@3$4@1$1@1$0#k0@1$h8^6@1$h8^h0@2$2@4$i2$9^5@2$5^a+hi0@3$6$7@1$i8@2$i3@1$0#k0@2$5^9@1$i7^8@1$d$7@4$i2$9^5@2$5@2$5^a+i0^9@3$6$7@1$c^4@3$6$7@1$c^3@3$6$7@1$c^2@3$6$7@1$c^1@1$d$7").

  (* [comment removed for export] *)
  Definition u8leaf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "ib0!t6!v9!hvb!q1!h9!ioc!ik4!ig1!s0!jn6!iq3!ip5!ir6!iq9!ra!jma!s5!krc!jo0!ks2!ks9!hmb!jo7!kt2!kt9!isb!hr1!li4!ln1!lr5!hv4!lvd!mg5!jof!mk9!jta!ki7!km7!ml0!ml7!kr1!mp8!mpe>1r$ha>1F@2$h5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$he>2lo$4>3raz$4>2ff$4>2sz$4>2cp$4>2j0@1$1@1$0#8>2j1@1$1@1$0#8>2j2@1$1@1$0#8>2j3@1$1@1$0#8>0@3$8@1$1@1$0#k0@1$h7^d@2$9@1$0#k0@2$2^7+i0>0@3$8@1$1@1$0#k0@1$h8^e@2$9@1$0#k0^6>0@3$8@1$1@1$0#k0@1$h9^f@2$9@1$0#k0^a>0@2$e@2$3Z^b@2$h0^b@2$h1+2+k0>0@3$8$4@2$ia^c+2Z>0@2$e@2$3Z^a@2$3^a+hgvvvf>0@2$i5$5^h0>0@1$hd^h1>0@4$i3$5^h2^h1@2$c@1$0#k0@1$b^h5>0@2$3@1$i0?5HCEIL^h2>0@2$3@2$2^h3+h0@2$c@1$0#k0@1$b^h7>0@2$3@2$c@1$0#k0@1$b^h8@2$h1+2+if>0@3$hf?5HCEIL@2$2^h3+i0+hg8>0>1x$4>0@2$3@2$2^h5+i0^1>0@2$h0^2@2$2^h6+hi8@3$8@1$h4@1$1@1$0#8@3$i6$5^ha@1$i7@1$hc^3@2$h3@1$1@1$0#8@1$i9Z>0@4$f$5^h8@2$2^h5+hi0@3$7$6@1$i1@2$9@1$0#k0^h4@1$d$6>0@4$f$5^h9@2$2@2$2^h6+i0^h5@3$7$6@1$a^h3@3$7$6@1$a^h2@3$7$6@1$a^h1@3$7$6@1$a^h0@1$d$6>0@2$3Z^h6>0@2$3@2$2^h7+4+hg0@3$i2$5@9$hb^hf^he^hd^hc^hb^ha^h9^h8^h7@7$i4@1$h6^hf^he@2$9@1$0#k0+hgoqh4^hd@1$h2@1$1@1$0#k0^hc@1$i8$5").
End HCW.
