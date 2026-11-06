(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~jacROPNEW_STACKja8eh_STACK04Npos35stdpp9bitvectorbdefinitionspe2bv37Corelib4Init9Datatypess04list3h5LinuxProcessSemanticsfLinuxProcessSem3Runtf6config3h5LinuxProcessSemanticsfLinuxProcessSem5Statehh45Model3h5LinuxProcessSemantics5Riscv7Preludehkb5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU5BJRep~~~~~~hna6vstack79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hs05blockhs03mem37Corelib4Init5Logicihb2exihb3andihb2eqhna6vsitems03apps06optiontf9cfg_modelhna8vs_itemshna7vs_temp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ine6PStates04Nones04conss03nil3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsit8dmachine_statetf6cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface~~~~~~ji9bbj_env_postji94vs_Xhna5VSkeyhna9blocks_vshna5vs_athna8vs_chars79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jq93mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~juc2MSjuc6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kj97seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~ko35xpresja7hs_KRELja8hs_MPRESja8hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~kub5rsegspebbv_unsignedja5frameit86ms_mems04prodhnaabj_staticsja6EH_IVSja4eh_Xhc2lehc2lthc3powihb2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~loc2wzhs08blk_addrhc6modulos06lengthtf5mkCfgji96bj_envji98chain_at89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUaBJIfaceKey5Iface~~~~~~mg9dRVS_KEY_STACKmg9dpush_key_postmg9cpush_key_unw79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUaBJIfaceKey~~~~~~mo2cRVS_PUSH_KEYhna4vs_n69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mtb5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~nhf8bytes_atja3csrja7fr_liveja5hs_SRja5mkCSRjabsaves_clearhs08blk_size36Stdlib5Lists4Listnpf2Inhc6of_nathc3subja3hmfja3ehk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition RVS_PUSH_KEY : Z := 0x59cf0.   (* [comment removed for export] *)
Definition RKEY_CV1 : Z := 0x6e9ac.       (* [comment removed for export] *)
Definition RKEY_CV2 : Z := 0x6eabc.       (* [comment removed for export] *)
Definition RKEY_CTOR2 : Z := 0x6eb90.     (* [comment removed for export] *)

Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!ns7$0").
  Variable E : ltac2:(zQ "10!nsd$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).

  (* [comment removed for export] *)
  Definition RVS_KEY_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!j4!ne!od@2$0@2$0+q0$1@1$2?1E").

  Definition push_key_post : ltac2:(zQ "a0!p8!rb!h9!t8!hgb!hk2!hn1!hr6!igb!ih4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$8>2va$2>2st$7>2lo$2>1B$2>1m$9>2mo$5>0$4P") := ltac2:(zQ "i91!p8!rb!iif!ij5!h9!ijc!ik2!igb!hr6!ikc!t8!il2!ilb!im7!in3!ira!is4!isb!it2!jgf!ji0!hgb!hk2!hn1!jm7!jn6!jne!jo7!jp4!jpd!ju5!ki9!kif!kn8!ks2!ksb!kt5!ku0!ih4!li8!lj1&>0@1$1@1$0#k0@1$b@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h7@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$a$7\2va$4\2st$8\2lo$4\1B$4\1m$i6\2mo$h6\1c$h5@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$f\2s'$f@2$2$8\3st'$8@2$2$7\1b$7@2$3@3$5$h3@1$h4^h4@7$hf@hf$he^id^ic^ib^ia^h3^h2^h1^i9^i8^h0^f^e^d^c^b^a^9^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^8^7^6^5^hd@1$i0^id^hc@1$h0@1$1@1$0#k0^4@1$i1$i7@2$3@3$i3?1H^3@1$c^h4@2$3@3$i4?1H^h5@1$c^h4@2$3@4$i5?1H^3@3$9$7@1$hb^2^hb^4@2$3@4$hc?5HCEIL^4^ha^2@2$3@3$5@1$a$6@1$d^2@3$9$6@1$d^h9@3$h1$6@1$ha^1@1$h2$6@2$3@3$5$4@1$hd^2Z@2$3@3$5$4@1$e^2@1$e^h9@2$3@7$h8?1H?1E^4^ic^ia^h8^h7@5$i2^hb@2$i8@1$0#k0^ic@1$h9^ha^h6^4").

  (* [comment removed for export] *)
  Definition push_key_unw : ltac2:(zQ "a0!h9!t8!p8!rb!hgb!hk2!hr6!ljf!igb!ih4>2sp@1$3@1$2#k0>1G@1$1$7>4REST@1$1$8>2va$0>2st$6>2lo$0>1B$0>2fc@1$3@1$2#i0>1m$9>2mo$5>0$4P") := ltac2:(zQ "i00!ij5!h9!t8!ijc!p8!lk7!ji0!hr6!ikc!iif!im7!in3!igb!ira!rb!ll1!ilb!hgb!hk2!jn6!ll8!jo7!jp4!jpd!ik2!ks2!lm6!lmf!ljf!kt5!ih4!lj1\2sp@1$e@1$4#k0\1G@1$2$hc\4REST@1$2$c\2va$1\2st$7\2lo$1\1B$1\2fc@1$e@1$4#i0\1m$he\2mo$h2\1c$h1@2$9$d\2s'$d@2$9$7\3st'$7@2$0@8$hb?1E^c^2@3$8$c@1$h5^1^b^8^7^6^3@2$0@3$hd?1H^4@1$h0^3@2$0@4$h6?5HCEIL@1$5@1$6^3^a^1@2$0@1$h4@1$5@1$6^3@2$0@3$3@1$2$h8@1$a^1@1$a^9@2$0@3$3$1@1$h7^1Z@2$0@3$3$1@1$b^1@1$b^9@5$h9^b@2$hf@1$4#k0^d@3$8@2$f$1$1@1$h3^a$ha^5@1$5@1$6^3").

  (* [comment removed for export] *)
  Definition push_key_stmt : ltac2:(zQ "00P") := ltac2:(zQ "ja1!p8!rb!lj1!ln6!j4!h9!ijc!ljf!igb!lnb!ij5!lo0!isb!t8!lo6!ls7!in3!lsd!li8!lt9!is4!ikc!lu2!iif!hgb!lub!hk2!hn1!lv3!lvd!jn6!ml0!mm1!mn2!ms3!jo7!jp4!jpd!mt3!hr6!nh6!ju5!ki9!nl9!kn8!nm5!nmb!ksb!ku0!nn5!nnd!no5!np3!ih4!ira!nr2!nr8!ns1&@3$6@1$1@1$0#k0^ib@1$f^9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hb@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j5>1s$j6>4REST@1$d$8>2st$i7>2lo$5>1B$5>4errv@1$1@1$0#k0>2mo$ha>1g$7>1G@1$d$7>3sbs@1$d@1$1@1$0#8>3src$5>1n$5>0@4$j0?1H^c@3$h5$8@1$i3^a^b^d>0@3$if?1H^d^7>0@b$hc?5HCEIL?1H?1E^f^if^id^b^a$hf^9^h0>0@4$i4?5HCEIL^h0@2$2@1$0#k0^i8^d>0@2$9@2$4@1$i6^e+1@2$b+2+ha>0@2$a@2$3@2$2@1$0#k0^j2@2$2@1$0#k0^ia@2$3@2$4@2$2@1$0#k0^ia+k0^d>0@2$a@2$3@1$i8?5HCEIL@1$h0^h0@2$9@1$h0^h0@2$b+2+k0>0~0>0~0>0@2$3Z^a>0@2$9@2$4^b@1$i5^h4@2$j9@2$b+2+hf+1>0@2$9Z^d>0@2$9@2$4^e^d@2$b+2+jf>0@4$ib$h2^ha^f^h0>0@3$6$5@1$j8@2$h6@1$1@1$0#8^h1^f>0@2$e@2$3@2$2@1$0#k0^jc^h1@2$h7$8\1b$8@2$a@3$j7$8^1^hb@2$a@2$3@1$h1^1^h2@2$3@2$4^h2^h1@2$4@1$h1^1@1$j4^1>0@2$e@2$3@2$4^h2^h1@2$2@1$0#k0^j5@2$3@2$4@2$2@1$0#k0^j5+k0^h2>0@5$hd?1E@3$c$7^h6^h5^he^je^jf>0@3$6$id@1$ie^h7@d$j2^jf^j9^j8^if^ie^id^ic^ib^ia^i9^i8^i7^i6>0@3$j3?1E@3$c$7^h8^h7@1$he@2$2@1$0#k0^j8>0@3$6$5@2$h3@2$2@1$0#k0^j9+8Z>0@3$6$5@2$h3@2$2@1$0#k0^k2+h0Z@3$j1?1H\1c$h8@2$e@ha$i0^k5^k4^k3^k2^je^jd^j4^j3^j2^j1^j0^if^ie^id^ic^ib^i6^i5^i2@2$2@1$0#k0^jc^i1^i0^hf^i4^hd^1@b$i1^k4@3$c$7^hc^hb^i2@2$2@1$0#k0^jc^i1^i0^hf^i5^i4^hd^1@2$h9@7$ia@hf$i9^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5@1$f$i2^i4@1$h4@1$1@1$0#k0^i3@1$ic$h2^hc").
End Iface.
