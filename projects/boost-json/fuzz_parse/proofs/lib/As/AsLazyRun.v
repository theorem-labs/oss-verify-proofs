(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SReach Frame
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazySR.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runk65mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statena5Model69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~r08restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~va4lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hjadhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ho28realizes37Corelib4Init5Logichs92eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~hu36mstepsr0h5same_but_materializedva8hid_sameho24TSet37Corelib7Numbers7BinNumsil24Npos35stdpp9bitvectorbdefinitionsin32bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ip64mkst37Corelib4Init9Datatypesit96option3h5LinuxProcessSemantics5Riscv7Preludeivb5bvmapit94list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejj27Segment" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!jia!jm7@1$0$1").
Variables L S Zr : list (word * word).

Theorem rz_msteps_lazy : ltac2:(zQ "c0!j7!n2!q8!uf!hj3!hn1!hrd!htd!ihc!ii6!ijf!ika>3msF$0>3ms1$0>2mo$2>1T$b>0@5$4?4segs?1L?1S?2Zr@2$1^4^2>0@3$8?4segs@3$3?1L?1S^5^4>0>4msF'$0>3mo'$2>0@5$4?4segs?1L?1S?2Zr@2$1^2^1>0@2$9^7^2>0@4$a?1L?1S^a^4>0@3$7$0@3$3?1L?1S^5^a@4$6?4segs$5@2$1^6^5^9@4$6?4segs$5@2$1^7^5^4").
Proof.
  intros msF ms1 mo T Hok Hms Hcont.
  destruct (msteps_restrict segs L S (lzok_ranges Hok) msF _ mo (lzok_inv Hok) (lzok_halted Hok) Hms)
    as (mo' & Hd & Hinv' & Hsame & Hh' & Hrestr).
  eapply rz_dsteps; [exact Hd|].
  apply Hcont; [| exact Hsame | apply hid_same_unrestrict | exact Hrestr].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)
Corollary rz_msteps_lazy_mkst : ltac2:(zQ "h11!imb!ip0!j7!n2!it1!iv1!htd!q8!ji1!uf!hj3!hn1!hrd!ihc!ii6!ijf!ika&>0@1$1@1$0#k0@1$5@1$1@1$0#8>3msF$2>4regs@2$8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5regs'@2$8@1$0#5@1$1@1$0#k0>3pc'@1$1@1$0#k0>4mem'~0>2mo$7>1T$h0>0@5$a?4segs?1L?1S?2Zr@2$3^a^2>0@3$6$2@3$9?1L?1S^b@5$4?2fx^a^9^8^7>0@3$d?4segs@5$4?2fx^b^a^9^8@5$4?2fx^7^6^5^8>0>4msF'$2>3mo'$7>0@5$a?4segs?1L?1S?2Zr@2$3^2^1>0@2$e^8^2>0@4$f?1L?1S^h1^4>0@3$6$2@3$9?1L?1S^5@5$4?2fx^d^c^b^e@4$c?4segs$b@2$3^6^5^a@4$c?4segs$b@2$3^e^6^5").
Proof.
  intros msF regs pc mem rom regs' pc' mem' mo T Hok Hr Hms Hcont.
  eapply rz_msteps_lazy; [exact Hok | rewrite Hr; exact Hms | exact Hcont].
Qed.
End WithSegs.
