(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocKit AllocRep AllocWalkKit AsDepotInv AW_MallocBase AW_Put1 AW_Enqueue1 AW_Put2 AW_Drain AllocTacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~k14cell37Corelib4Init9Datatypeso44consk12C846Stdlib6ZArith6BinInt1Zq83add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~s65asegshfbbv_unsigned01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hha8rw_cellso43nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hm72wzhf7Z_to_bvo44Noneo43appo46length37Corelib5Lists7ListDefhs83map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AW_Put1~~~~~~hu69put_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AW_Put2~~~~~~ij0dfree_ret_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ine3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~is36u64arrk12CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jgc3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jke3mkRjke3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jp82MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jtb7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ki07seg_romq86of_natq82leo43nat37Corelib4Init5Logickne2eq37Corelib4Init3Natkp83sub37Corelib4Init5Peanokr12lekne3and" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section HCW.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Variables (sp ra0 s0v s1v s2v s3v s4v s5v : word).
  Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (T : list Z) (rest : list word) (jk : list byte).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : ltac2:(zQ "40!h9!s0!kn3!hg9@2$2@2$1?2lo+ps0@2$3@1$0#k0?2sp").
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis LR : ltac2:(zQ "70!hrf!kn8!kp2!kqa!h9!hh7!jc@3$2$1@2$0@1$6@1$4#k0?4rest@2$3Nvf@2$0$5?1T").
  Hypothesis NR : ltac2:(zQ "40!hrf!ks5!hh7!ksb@2$3@2$1N1@2$0$2?1T@2$1@2$0$2?1TNhe").

  Theorem put_after_recycle : ltac2:(zQ "hd1!h9!jc!nd!pc!q3!s0!hg1!hg9!hh7!hl5!hm1!hq2!hq8!hr2!hr9!hrf!htf!ii3!imd!irc!ivd!jg7!jk7!joa!jp1!jt5!kh5!klf!kma&@2$5@2$5@2$7@1$0#k0?2sp-ol0+h0>3rax@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2x0@1$1@1$0#k0>2x1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1m$h3>1U$8>2TH$8>0@2$ha$6^3>0@4$h8$6^4?2lo@2$5@2$7@1$0#k0?2sp-oq0>0@4$9$6^5@2$5@2$7@1$0#k0?2sp-oq0@4$h1?2sp?2s6^4^3>0@4$9$6^6@2$5@2$7@1$0#k0?2sp-ol0@3$3$2@1$4@1$b~0@3$3$2@1$4@1$b@1$hc@2$f$8?1T@1$a$2>0@4$h4$6^7~0@3$e@1$1@1$0#k0@4$h0$8@1$1@1$0#k0$b?1T?4rest>0@4$9$6^8@2$5@2$7@1$0#k0?2sp-k8@3$3$2@1$4?2sp@1$a$2>0@4$9$6^9@2$5@2$7@1$0#k0?2sp-k0@3$3$2@2$h5N8?2jk@3$3$2@1$4?3s5v@3$3$2@1$4?3s4v@3$3$2@1$4?3s3v@3$3$2@1$4?3s2v@3$3$2@1$4?3s1v@3$3$2@1$4?3s0v@3$3$2@1$4?3ra0@1$a$2@3$h6$6@h4$h2?2sp?3ra0?3s0v?3s1v?3s2v?3s3v?3s4v?3s5v?2gp?2tp?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?2lo^a@7$h9@hf$h7^i1@2$c@1$0#k0@2$5@2$7@1$0#k0?2sp-oq0?2gp?2tp^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f?2s7?2s8?2s9?3s10?3s11^e^d^c^b?1F@2$c@1$0#k0+mtlic?2fc@1$d@1$1@1$0#k0^a@1$hb$6").
  Proof.
    intros until m. intros U TH MI ST PFR ESO TRB TFB F4.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR. acb.
    unfold put_frame, OT_TQ, OT_CACHE, wz in *.
    (* [comment removed for export] *)
    do 8 step. step. step.
    release_frame PFR ST (bv_unsigned sp + -2128).
    step. do 7 step. step. step.
    apply evt_done. unfold free_ret_post. neexists 15. split; [reflexivity|]. eapply icpt_frame_release; eassumption.
  Qed.
End HCW.
(* [comment removed for export] *)
