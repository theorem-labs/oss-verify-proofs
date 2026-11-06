(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Scfg PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SReach SymExec Frame SymExec2 SymExec2Sound SymRun SymDrive
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~m08sidecond04prod37Corelib4Init5Logicr02eqm06kentry04bool06option04pair3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsu6dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhid5mkCfgm07scriptsm09sym_state03nil03nathe1Z3h5LinuxProcessSemanticsfLinuxProcessSem5Stateho65Model3h5LinuxProcessSemantics5Riscv7Preludehrd5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~huc8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~ij74lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~in84mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~irb8realizesm05s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~jga7know_okjga7regs_okjga9scs_denotje7Z_to_bv04truehuch5same_but_materializedij78hid_sameirb4TSetm02SSm05carrym03envm04exprm04s_pcm06s_regsm06sentrym08sym_execjga9mem_denot3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejvb7Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!h8!kj0@1$0$1").
(* [comment removed for export] *)
Context {SC : StepCfg}.
Variables L S Zr : list (word * word).

(* [comment removed for export] *)
Theorem rz_run_lazy : ltac2:(zQ "i91!h8!j7!lb!pf!qa!s4!s9!t2!t8!u0!hhd!hl9!hm2!hmc!hn8!hnd!ho2!hr4!hu3!iib!in0!ir3!iv6!jg2!jkf!jla!jm5!jn2!jnc!jo2!jpc!jq8!jr0!jr5!jrd!js3!jsa!jt1!jta!ju3!jue&>0@1$2@1$1#k0@1$8@1$2@1$1#8>4fuel$f>5stops@1$0$h0>3scr$c>2pc$h0>2sr@1$0$i3>2kn@1$0$6>2nx$f>3ss'$d>3scs@1$0$3>4scr'$c>3kn'@1$0$6>4scs2@1$0$3>3hs2@1$0$7>1E$i2>1M~0>3rom~0>1R@2$h2@1$1#5@1$2@1$1#k0>3msF$a>5model$h1>1T$hf>0@3$5@2$4@2$4$d@1$0$3$c@7$i7?4segs^h4$hc^h3^h2@5$i0^h1^h0@1$e$i6^f^e@1$e$3@4$9@2$4$d@1$0$3$c@4$9$d@1$0$3^d^c^b>0@3$5@2$4@2$4@1$0$6@1$0$3@1$0$7@3$i1@1$h7^e^h0@1$e$7@4$9@2$4@1$0$6@1$0$3@1$0$7@4$9@1$0$6@1$0$3^b^a^9>0@3$h9^9^h2^6>0@4$h8?4segs^a^9^h2>0@4$ha?4segs^a^b^h0>0@4$ha?4segs^b^c^e>0@5$h4?4segs?1L?1S?2Zr@2$b^9^8>0@3$5$a@3$h3?1L?1S^a@5$h5?2fx^b@2$hb@1$1#k0^h8^d^c>0>2R'@2$h2@1$1#5@1$2@1$1#k0>2M'~0>4msF'$a>6model'$h1>0@3$h9^h3@1$i5^h9^4>0@4$h8?4segs^h4^4^h7>0@3$5~0^5@3$i8^h5^h4@1$h7^hb>0@5$h4?4segs?1L?1S?2Zr@2$b^5^4>0@2$hd^h2^5>0@4$he?1L?1S^h4^7>0@3$5$a@3$h3?1L?1S^8@5$h5?2fx^a@2$hb@1$1#k0@1$i4^hf^9^h7@4$h6?4segs?2SC@2$b^9^8^h4@4$h6?4segs?2SC@2$b^c^b^a").
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF model T
         Hex Hc HR HK Hsc Hsc2 Hok Hr Hcont.
  ndestruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  rewrite <- Hr in Hms.
  destruct (msteps_restrict segs L S (lzok_ranges Hok) msF _ model (lzok_inv Hok) (lzok_halted Hok) Hms)
    as (model' & Hd & Hinv' & Hsame & Hh' & Hrestr).
  eapply rz_dsteps; [exact Hd|].
  apply (Hcont R' (mem_denot E M (s_log ss')) _ model' HR'); [| reflexivity | | exact Hsame | apply hid_same_unrestrict | exact Hrestr].
  - eapply carry_after; eassumption.
  - eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)

End WithSegs.
(* [comment removed for export] *)
