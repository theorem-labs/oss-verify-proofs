(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothImages BothPlanImages AsHSTab BsStartupHSF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv3h5LinuxProcessSemanticsfLinuxProcessSem3Runk46config3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutn99EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem5Stater99ProcInput37Corelib4Init5Logicv33andv32exr97in_argvr97in_envp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~hi63acs37Corelib4Init9Datatypeshmb6optionv32eqr98in_hwcapr96in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~hq65ASEGShmb3natr95Model3h5LinuxProcessSemantics5Riscv7Preludehvf5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~iie3envhq63APH69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainState~~~~~~ind6A_MAINhmb4Somek4h0entry_stack_fitsk4avalid_argvk49valid_brkk4avalid_envpk4bvalid_hwcapk48valid_idk4fvalid_mmap_basek48valid_spr95in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~jk55LIMITjk55SINV0jk55argH0hi62pc79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~jq16cfg_ofjq15cs_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~jv86BOTH_H69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSF~~~~~~kjf8HSF_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~koa3fx0" s.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

(* [comment removed for export] *)
Definition A_MAIN : Z := 0xbe8bc.   (* [comment removed for export] *)

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition P_main : ltac2:(zQ "50!hc!jf!n0!qd!u7>3sp0@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>5rdraw$3>3inp$4>1c$2P") := ltac2:(zQ "i91!hg7!hc!jf!hgd!hh2!hhc!hm4!ho3!hod!hp2!hpd!hu7!hv0!n0!hv7!ii5!imf!in6!irb!is5!h9!isd!iu1!iue!iva!jg7!jh5!ji0!jj2!qd!u7!jjd!jo0!jo9!jp2!jpb!ju5!juf!kj5!kne!ks5&>0@1$2@1$1#k0@1$7@1$2@1$1#8\3sp0@1$2@1$1#k0\4brk0@1$2@1$1#k0\5mbase@1$2@1$1#k0\5rdraw$hd\3inp$he\1c$d@2$0@2$0@1$hc^6@2$0@2$h7$b^5@2$0@1$hb^4@2$0@1$h6@1$4^2@2$0@1$h8@1$5^2@2$0@3$h5^6@1$4^2@1$5^2@2$0@1$ha@1$a^2@1$h9@1$9^2@2$3$c\1h$c@2$3$6\2ch$6@2$3$h0\1E$h0@2$3@2$f@1$1#5@1$2@1$1#k0\1R@2$f@1$1#5@1$2@1$1#k0@2$3~0\4FULL~0@2$3$e\5model$e@2$0@3$8@1$7$6@1$i7^6@2$h3$6^5@2$0@3$8$h4@1$i3^5$h2@2$0@3$8$d^7@6$i4$i8$b^3$h2^2^1@b$i5$b$i6$i0@8$i1$h1^c^9^b@1$4^8@1$5^8@1$a^8@1$9^8@7$i2$h1^c^9@1$4^8@1$5^8@1$a^8@1$9^8@1$hf^8^4^5^3^2^1").
(* [comment removed for export] *)
