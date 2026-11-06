(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsImages AsPlanImages AsHSTab AsStartupHSF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv3h5LinuxProcessSemanticsfLinuxProcessSem3Runk46config3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutn99EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem5Stater99ProcInput37Corelib4Init5Logicv33andv32exr97in_argvr97in_envp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~hi63acs37Corelib4Init9Datatypeshmb6optionv32eqr98in_hwcapr96in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~hq65ASEGShmb3natr95Model3h5LinuxProcessSemantics5Riscv7Preludehvd5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainState~~~~~~iic6A_MAINhq63APH79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~inb3envhmb4Somek4h0entry_stack_fitsk4avalid_argvk49valid_brkk4avalid_envpk4bvalid_hwcapk48valid_idk4fvalid_mmap_basek48valid_spr95in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~jk36ASAN_H69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~jo88HSF_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~jt35LIMITjt35SINV0jt35argH0hi62pc79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~kif6cfg_ofkif5cs_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ko63fx0" s.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

(* [comment removed for export] *)
Definition A_MAIN : Z := 0xbe920.   (* [comment removed for export] *)

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition P_main : ltac2:(zQ "50!hc!jf!n0!qd!u7>3sp0@1$1@1$0#k0>4brk0@1$1@1$0#k0>5mbase@1$1@1$0#k0>5rdraw$3>3inp$4>1c$2P") := ltac2:(zQ "i91!hg7!hc!jf!hgd!hh2!hhc!hm4!ho3!hod!hp2!hpd!hu5!hue!n0!hv5!ii3!ima!in4!irc!is3!h9!isb!itf!iuc!iv8!jg5!jh3!jhe!jj0!qd!u7!jjb!jne!js7!kge!kh7!ki0!ki9!kn3!knd!ks1&>0@1$2@1$1#k0@1$7@1$2@1$1#8\3sp0@1$2@1$1#k0\4brk0@1$2@1$1#k0\5mbase@1$2@1$1#k0\5rdraw$hd\3inp$he\1c$d@2$0@2$0@1$hc^6@2$0@2$h7$b^5@2$0@1$hb^4@2$0@1$h6@1$4^2@2$0@1$h8@1$5^2@2$0@3$h5^6@1$4^2@1$5^2@2$0@1$ha@1$a^2@1$h9@1$9^2@2$3$c\1h$c@2$3$6\2ch$6@2$3$h2\1E$h2@2$3@2$f@1$1#5@1$2@1$1#k0\1R@2$f@1$1#5@1$2@1$1#k0@2$3~0\4FULL~0@2$3$e\5model$e@2$0@3$8@1$7$6@1$i1^6@2$h3$6^5@2$0@3$8$h4@1$i5^5$h0@2$0@3$8$d^7@6$i6$i8$b^3$h0^2^1@b$i7$b$i0$i2@8$i3$h1^c^9^b@1$4^8@1$5^8@1$a^8@1$9^8@7$i4$h1^c^9@1$4^8@1$5^8@1$a^8@1$9^8@1$hf^8^4^5^3^2^1").
(* [comment removed for export] *)
