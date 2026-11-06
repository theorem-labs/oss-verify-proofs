(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach LazyRestrict LazyLedger LazySR AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepX AsDepotInv
     AG_MallocModel AG_Malloc2 AG_RepQ AG_WriteSet AG_RecycleDefs AG_RecyclePrim AG_RecycleSec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06astate37Corelib4Init9Datatypesk94list06effectk94prod37Corelib4Init5Logicn72ex3h5LinuxProcessSemanticsfLinuxProcessSem3Runp05mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~s4fsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hha5asegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~hle6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hq1dhunspell_scfgk94Somek96optionk94pairn73andn72eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsigbdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateil35Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecycleDefs~~~~~~ioaarstep_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~itc4a_st0acb_recycle0cch_chunk_beg37Corelib7Numbers7BinNumsjjc4Npos35stdpp9bitvectorbdefinitionsjld2bvjldbbv_unsigned46Stdlib6ZArith6BinInt1Zjof3addjjc1Zjof2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jr92wzjld7Z_to_bvk94consitc5AINSTitc3a_Litc3a_S05chunk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kia4celljof3powk94Nonek94boolk93nilk94truep06config3h5LinuxProcessSemantics5Riscv7Preludekp95bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~ks8cdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~lh85AREPQ79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~lle6B_PRIMlle6pusageitc3ATPitc4a_Zritc7a_cacheitc3ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~lt47AMODELXlt48awin_vislt49depot_covlt4aflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~mk55DEPOTmk55depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~mp75aceilmp73mem0bCQuarantine0fas_cache_inited08ch_state0achunk_list06cstate69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~ni18restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~nmc4lzokkia2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~nr33mkRnr33stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~nvd2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ok07mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~oo57seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~osf8rw_cells36Stdlib5Lists4Listph62Injof6modulo" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section RCStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (ch : chunk) (d : depot) (lo cb : Z).

  Hypothesis RQ : ltac2:(zQ "40!kg5!jqe!ll5!jie@5$2?5HCEIL?1s@3$0$1@1$3?2ch?2XC?2XB?1m").
  Hypothesis CHIN : ltac2:(zQ "40!jha!ki3!ngd!pi9@3$3$1?2ch@1$2@1$0?1s").
  Hypothesis QUAR : ltac2:(zQ "40!ig6!mu5!ng3!nh9@3$0$3@1$2?2ch$1").
  Hypothesis INIT : ltac2:(zQ "50!knc!ko9!ig6!jha!mv2@3$2$0@1$4@1$3?1s$1").
  Hypothesis AX : ltac2:(zQ "30!ig0!mhe!mj7@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!mh3@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!hl5!mo5@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!lg8@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!mia@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!hl5!ona@2$1$0?1m").
  Hypothesis LO : ltac2:(zQ "20!mt5!jr3@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!jl5!jq7!jr3!jo0@2$2@2$1?2lo+ji0@2$3@1$0#k0?2sp").
  Hypothesis SPT : ltac2:(zQ "50!jl5!jq7!jr3!kme!jo0@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SPA : ltac2:(zQ "50!ig6!jl5!jqe!pif!jo0@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis ST : ltac2:(zQ "40!jl5!hl5!nv6!jo0@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis TP : ltac2:(zQ "50!ig6!jl5!jqe!lr3!jo0@3$0$2@2$4@1$1#k0?2tp$3").
  Hypothesis PROOM : ltac2:(zQ "50!lpf!lq9!jha!jq7!jr3@2$4@2$3@1$1@1$2?1s+kqgg0$0").
  Hypothesis CBR : ltac2:(zQ "60!jr3!ig0!jl5!jq7!kme!jo0@2$1@2$0@2$5@1$2#k0?2sp?2cb@2$0@2$3?2cb+8@2$4+2+jf").
  Hypothesis CBC : ltac2:(zQ "80!km6!kg5!ko3!hl5!ls2!nqd!pga!jv4@4$6$3?1m?2cb@3$1$0@1$5@1$7@1$4?1s@1$2$0").
  Hypothesis OK : ltac2:(zQ "60!rc!hl5!kh5!khc!lra!nq5@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "f0!jl5!jv4!kn5!ig6!ik2!hl5!kh5!khc!jie!nm0!nuf!oja!os4!jva!jna@3$3$4@3$9@1$6?1s@1$7?1s?3msF@7$b@hf$a?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$1?2cb@1$1@1$8?2ch?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$d@1$0#k0+mrjpc?2fc@1$2@1$e@1$0#k0?1m@1$c$5").

  Theorem recycle_chunk_arepq : ltac2:(zQ "h50!k1!m1!m8!n0!ob!rc!hg8!hl5!hp7!ht8!hu9!hv0!hv9!ig0!ig6!ik2!io1!ise!jha!ji2!jie>0>4msF'$f>3mo'$h0>0@he$h1?5HCEIL?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1s?1d?2lo?1m?2mo?2XC?2XB?2XB\3st'$0>3stA$0>0@2$6^1@1$h2?1s@2$4$0\4stA'$0@2$4@1$1$2\2ev@1$1$2@2$d@3$e@1$b@2$3$0@1$1$2@2$h3^4@1$h4?2ch@2$a@2$3$0@1$1$2@4$c$0@1$1$2^2^1@2$6^2^5^2^1@4$8$7$9?1Q@2$5^3^2@4$8$7$9?1Q@2$5?3msF?2mo").
  Proof.
    intros K. destruct (ch_primary ch) eqn:PRIM.
    - apply (recycle_prim_arepq ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s XC XB ch d lo cb
               RQ CHIN PRIM QUAR INIT AX AMX DEP DPL DCOV MI LO ltac:(clear - HI; lia) SPT SPA ST TP PROOM CBR CBC OK VISE).
      intros msF' mo' P. apply K. exact P.
    - apply (recycle_sec_arepq ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s XC XB ch d lo cb
               RQ CHIN PRIM QUAR INIT AX AMX DEP DPL DCOV MI LO HI SPA ST TP OK VISE).
      intros msF' mo' P. apply K. exact P.
  Qed.
End RCStep.

(* [comment removed for export] *)
Theorem step_chunk_real : ltac2:(zQ "ka0!jl5!jna!jo0!jq7!hl5!m1!k1!ig6!jqe!jr3!m8!jv4!jha!ig0!ik2!rc!jie!jva!kg5!n0!ob!io1!hg8!kgc!kh5!khc!ki3!km6!hp7!ht8!kme!kn5!hu9!knc!ko3!hv0!hv9!ko9!kp0!krf!lg8!ise!ll5!lpf!lq9!lr3!lra!ls2!lsd!mh3!mhe!mia!mj7!mo5!moe!mt5!mte!mu5!mv2!ji2!ng3!ngd!nh9!nm0!nq5!nqd!nuf!nv6!oja!ona!os4!pga!pi9!pif>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>1F@2$i7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1Q>0$i6P>2d'$j6>2lo$8>3spD@1$1@1$0#k0>3ra1@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>4s10x@1$1@1$0#k0>4s11x@1$1@1$0#k0>2m0$j8>3msF$e>2mo$h5>2sx$j0>2XC@1$5$8>2XB@1$5$8>3chx$ha>0@5$ia?5HCEIL^4@3$h2$8@1$h0^1^3^2^7>0@3$k8$ha^2@1$jd@1$c^5>0@3$7$je@1$jc^3$j9>0@3$7$i1@1$ja@1$c^7$i5>0@2$d@2$j2^8^b@1$j4^b>0@3$j1?5HCEIL^9^a>0@3$j5$4^i8^d>0@3$i8?5HCEIL^b^i9>0@2$j3^ia^d>0@2$k5$4^h0>0@2$9@1$j7?5HCEIL^ib>0@2$9@2$3^ic+ji0@2$2@1$0#k0^ib>0@2$9@2$3@2$2@1$0#k0^ic+h0@2$he+2+if>0@3$7$8@2$k9@2$2@1$0#k0^id+h0Z>0@4$k3$4^h5^if@2$2@1$0#k0^ie>0@3$7$8@2$2@1$0#k0^j5$id>0@2$9@2$3@1$ic@1$c^h4+kqgg0$ib>0@2$d@2$9@2$2@1$0#k0^j1@2$3@2$2@1$0#k0^j1+8@2$9@2$3@2$3@2$2@1$0#k0^j1+8+8@2$he+2+jf>0@4$k7$4^h9@2$3@2$2@1$0#k0^j2+8@3$h2$hb@1$k1@1$b@1$if^h6@1$i2$hb>0@5$k0$4@1$h8^h7@1$h9^h7@1$ie^h7@2$f^h9^h8>0@3$7$e@3$jf@1$h8^h8@1$h9^h8^ha@7$k4@hf$k2^j3^j4^jb^ja^j2^j1^j0@2$h1@1$0#k0@2$3@2$2@1$0#k0^j4+n0@1$b$h7@1$b@2$3@2$2@1$0#k0^j4+8@1$b@1$h0^h5^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^hd^hc^i1^i0^hf^he^j9@2$h1@1$0#k0+mrjpc^j8@1$hf@1$1@1$0#k0^hb@1$k6$4>0>4msF'$e>3mo'$h5>0@he$i9?5HCEIL^j6^j7^je^jd@2$h1@1$0#k0@2$3@2$2@1$0#k0^j7+n0@1$b$h7^ic^ib^ia^i9^i8^i7^i6^i5^i0^hf^jc^jb^hb^j9^j8^he^hc^ha^h9^h9\3st'$6>3stA$6>0@2$h6^1@1$c^hd@2$h4$6\4stA'$6@2$h4@1$5$a\2ev@1$5$a@2$d@3$7@1$i3@2$h3$6@1$5$a@2$jb^4@1$h0^hd@2$i0@2$h3$6@1$5$a@4$i4$6@1$5$a^2^1@2$h6^2^5^2^1@4$hc$4$hd^jb@2$f^3^2@4$hc$4$hd^j9@2$f^hc^hb").
Proof.
  intros gp tp F fc Q d' lo spD ra1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 s10x s11x m0 msF mo sx XC XB chx.
  intros RQ CHIN QUAR INIT AX AMX DEP DPL DCOV MI LO HI SPT SPA ST TP PROOM CBR CBC OK VISE K.
  exact (recycle_chunk_arepq ra1 spD gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x t3 t4 t5 t6
           F fc m0 msF mo Q sx XC XB chx d' lo (bv_unsigned spD + 8)
           RQ CHIN QUAR INIT AX AMX DEP DPL DCOV MI LO HI SPT SPA ST TP PROOM CBR CBC OK VISE K).
Qed.
End HCW.
