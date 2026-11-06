(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AsDepotHash AsDepotPut AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_LargeAlloc1 AW_SysconfPg
     SecLazy AS_LargeAlloc AS_CombinedLarge AW_AllocSec1 AW_AllocSec2 AS_AllocSec1 AS_AllocSec2 AllocTacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eqhc3and46Stdlib6ZArith6BinInt1Zjb3add69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~l98round_up37Corelib4Init9Datatypesq56length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAllocWalkKit~~~~~~s66hidden79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsDepotHash~~~~~~hh1adepot_hash79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~hm07d_putidjb3maxjb3muljb6of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hs05asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ig47mem_inv04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ikf3stk35stdpp9bitvectorbdefinitionsip2bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~ire5aceiljb2lejb6modulojb3powjb2lths08AIMG_TOP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~jia5akobjire4aapphc2orl9h0kPtrArrayReservehm04d_nbhm04d_sbl9akSpaceSizeire6AHI_LOhc2exl94zlen37Corelib5Lists7ListDefjs56Forallhm08d_frameshm05d_ids79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAW_AllocBase~~~~~~jvb4AENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BseAW_LargeAlloc1~~~~~~kk54SENVjvb6aframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kpb4cellq54conskpb2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kuc2wzq53niljia5AINST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ljc8rw_cellsjia5wlist79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~loc6u64arrhm05DEPOT3h5LinuxProcessSemanticsfLinuxProcessSem5Statelt98m_vmmapslt97vm_maps69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~mheeentries_nowraplt9bvm_noaccessmhe9nooverlaplt99page_sizelt98vm_limit69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~mq2aeager_usedmq2bpages_totaljb3divip22bvq53appq54boolq54prodq54truelt99alloc_toplt9bregion_freelt9bvm_reservedhs07AIMG_LOmq2ain_rangesbire9ALOWSH_LO69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~nn65hceilire2shq54Noneq56optionhc3not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsnt65wviewlt9cmap_containsq55false3h5LinuxProcessSemanticsfLinuxProcessSem3Runoie5mkCfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~om34lzokip27Z_to_bvnt6dmachine_statemq28restrictikf3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ot32MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ph67seg_rom" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AllocSec.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  (* [comment removed for export] *)
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).   (* [comment removed for export] *)
  Variables (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j8 : list byte).
  Variables (lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 nT id : Z) (chunks T : list Z) (rest : list word) (d : depot).
  Hypothesis DEFS : ltac2:(zQ "c0!h9!j0!j5!l3!pa!rd!hg8!hl2!hq0!hqb!hr1!hr7@1$6@2$2@3$1$0?6needed@2$3@2$4@2$9?4size+8+8+hgg0@2$2@3$1$0?3msz@2$3@2$4?6needed+hgg0+hgg0@2$2@3$1$0?4size@2$3@2$a+8?2q8?2r8@2$2@3$1$0?2nT@1$b@2$5$0?1T@3$1$0?2id@2$8?1d@1$7?1T").
  Hypothesis MI : ltac2:(zQ "20!hvb!ije@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "50!ik9!hvb!iob!l3!iqf@4$2$1?1m?2lo@2$3@2$4@1$0#k0?2sp-o0").
  Hypothesis LO : ltac2:(zQ "20!ivc!jg5@2$1@1$0?5HCEIL?2lo").  Hypothesis HI : ltac2:(zQ "40!ik9!l3!jg5!iqf@2$2@2$1?2lo+jg0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "60!j0!ik9!h9!hg8!jga!iqf@1$3@3$0$2@2$4@2$5@1$1#k0?2sp+h0Z"). Hypothesis SPH : ltac2:(zQ "50!ik9!l3!jg5!jh3!iqf@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SZ : ltac2:(zQ "30!jh9!j5!jh3@2$1@2$0+vsg0?4size@2$0?4size@2$2+2+i0"). Hypothesis R8 : ltac2:(zQ "30!j5!jg5!jh9@2$0@2$1Z?2r8@2$2?2r8+8").
  Hypothesis TPR : ltac2:(zQ "70!ik9!jg5!iqf!j5!jhe!hg8!l3@1$5@2$3@2$1+mpvgs8@2$2@1$0#k0?2tp@2$1@2$6@2$2@1$0#k0?2tp+hgg0$4").
  Hypothesis RNG : ltac2:(zQ "b0!j5!jg5!l3!ivc!j0!h9!jhe!jm8!hg8!jn1!jga@1$8@2$0@2$1+mpvgn0?3TSD@2$0@2$1@2$2?3TSD+8$6@2$0@3$9?5HCEIL?3CTX+q0@2$0@2$1@2$2?3CTX+q0@1$3?5HCEIL@2$0@3$7?5HCEIL?2TH+hgg0@2$0@2$1@2$2?2TH+hgg0@1$3?5HCEIL@3$4$5@2$a?2TH+h0Z").
  Hypothesis PLC0 : ltac2:(zQ "60!l3!jg5!jn9!j5!jne!hg8@1$5@2$3@2$2@2$1@2$0?3CTX+q0?2TH@2$1@2$0?2TH+hgg0?3CTX@2$3@2$2@2$1@2$0?2pa$4?2TH@2$1@2$0?2TH+hgg0?2pa@2$2@2$1@2$0?2pa$4?3CTX@2$1@2$0?3CTX+q0?2pa").
  Hypothesis PLCD0 : ltac2:(zQ "a1!l3!jg5!hr1!j5!jp2!jpa!jn9!jne!jn1!hg8&@2$0@1$4?1d@2$2+h0+hggg0@1$9@2$3@2$6@2$1@2$0?2TH+hgg0@1$4?1d@2$1~0?2TH@2$3@2$6@2$1@2$0?2TH+hgg0@1$5?1d@2$1@2$0@1$5?1d@2$2+8+ogg0?2TH@2$3@2$6@2$1@2$0?3CTX+q0@1$4?1d@2$1~0?3CTX@2$3@2$6@2$1@2$0?3CTX+q0@1$5?1d@2$1@2$0@1$5?1d@2$2+8+ogg0?3CTX@2$3@2$6@2$1@2$0?2pa$7@1$4?1d@2$1~0?2pa@2$3@2$6@2$1@2$0?2pa$7@1$5?1d@2$1@2$0@1$5?1d@2$2+8+ogg0?2pa@2$3@3$8?5HCEIL@1$4?1d@2$2+h0+hggg0@3$8?5HCEIL@1$5?1d@2$2+8+ogg0").
  Hypothesis SBR : ltac2:(zQ "70!jg5!j5!jq2!hg8!jqf!ivc!l3@1$3@2$1@2$0$4?2sb@2$0@2$6?2sb$2@1$5?5HCEIL").
  Hypothesis SOR : ltac2:(zQ "70!jg5!j5!ik9!hg8!l3!jh3!iqf@1$3@2$1@2$0@2$6@1$2#k0?2sp?2SO@2$0@2$4?2SO+oh0@2$5+2+if").
  Hypothesis PAR : ltac2:(zQ "90!j5!jne!j0!h9!jn1!ivc!l3!jg5!jga@2$0@3$4?5HCEIL?2pa$1@2$0@2$7@2$6?2pa$1@1$5?5HCEIL@3$2$3@2$8?2pa+hgg0Z").
  Hypothesis NCH : ltac2:(zQ "40!jg5!j5!l3!jh3@2$1@2$1@2$0Z?3nch@2$0?3nch?4nres@2$0@2$2?4nres+kgg0@2$3+2+h4"). Hypothesis NRQ : ltac2:(zQ "40!h9!j0!jr9!hr1@2$2$0\1q$0@3$1$0?4nres@2$3+ig0^1").
  Hypothesis LEN : ltac2:(zQ "30!h9!j0!jre@3$1$0@2$2$0?6chunks?3nch").
  Hypothesis NR : ltac2:(zQ "20!jg5!j5@2$1@2$0+1?2nT@2$0?2nT+ve"). Hypothesis TRNG : ltac2:(zQ "60!h9!j5!jtc!jg5!jh9!jh3@3$2$0\1x$0@2$1@2$3Z^1@2$4^1@2$5+2+k0?1T").
  Hypothesis DCAP : ltac2:(zQ "60!l3!j5!ju6!jv2!jg5!jh9@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@2$0@1$2?1d?2nT+1+ogg0").
  Hypothesis DLO : ltac2:(zQ "60!l3!jg5!hr1!j5!jp2!jpa@2$3@2$1@2$0@1$4?1d@2$2+h0+hggg0?2lo@2$1@2$0@1$5?1d@2$2+8+ogg0?2lo").
  (* [comment removed for export] *)
  Hypothesis AEN : ltac2:(zQ "10!kjd@9$0?2tp?3TSD?3CTX?2TH?2sb?2SO?1T?4rest?1m").
  Hypothesis SEN : ltac2:(zQ "10!ko9@5$0?2tp?3TSD?3CTX?2TH?1m").
  Hypothesis FR : ltac2:(zQ "10!kp1@h0$0?2sp?2ra?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1m?2j8").
  Hypothesis INST64 : ltac2:(zQ "90!kt7!ktf!ku6!li7!lid!hvb!lj3!ln7!l3@4$7$5?1m@2$8$6+k0@3$1$0@1$2@1$3+hgg0@3$1$0@1$2@1$3?2pa@3$1$0@1$2@1$3?2pa@1$4$0").
  Hypothesis NRES : ltac2:(zQ "90!kt7!ktf!ku6!li7!lid!hvb!lj3!ln7!l3@4$7$5?1m@2$8$6+n0@3$1$0@1$2@1$3?4nres@3$1$0@1$2@1$3?3nch@3$1$0@1$2@1$3Z@1$4$0").
  Hypothesis SST : ltac2:(zQ "40!lj3!l3!hvb!iob@4$3$2?1m@2$1$0+o8@2$1$0+iq8").
  Hypothesis MTX : ltac2:(zQ "90!kt7!ktf!lid!hvb!lj3!ku6!ln7!li7!l3@4$6$3?1m@2$8$4+iq8@3$1$0@1$5@1$7Z@1$2$0").
  Hypothesis GST : ltac2:(zQ "40!lj3!l3!hvb!iob@4$3$2?1m@2$1$0+ir0@2$1$0+it8").
  Hypothesis TST : ltac2:(zQ "30!l3!hvb!iob@4$2$1?1m@2$0?2TH+qv0@2$0?2TH+sm0").
  Hypothesis PA : ltac2:(zQ "30!hvb!lo3!ls6@4$2$0?1m?2pa@1$1?6chunks").
  Hypothesis PAJ : ltac2:(zQ "40!l3!hr1!hvb!iob@4$3$2?1m@2$0?2pa@2$1+8?3nch@2$0?2pa@2$1+8?4nres").
  Hypothesis DEP : ltac2:(zQ "20!hvb!lt0@3$1$0?1d?1m").
  (* [comment removed for export] *)
  Hypothesis NW : ltac2:(zQ "30!mg7!mh3!mlb@1$2@1$1@1$0?2mo"). Hypothesis NWA : ltac2:(zQ "30!mg7!mmd!mlb@1$2@1$1@1$0?2mo").
  Hypothesis NOV : ltac2:(zQ "30!mg7!mh3!mnc@1$2@1$1@1$0?2mo").
  Hypothesis BUD : ltac2:(zQ "90!l3!mo9!hr1!mg7!mp6!mu1!muf!mve!jg5@2$8@2$0@2$0@2$0@2$0@1$5?2mo@2$2@1$6?1S$1?3msz@2$2@2$0@2$7?3msz+ogg0+2$1+iggg0@1$4@1$3?2mo").
  Hypothesis GAP : ltac2:(zQ "h60!ik9!ng4!j5!mg7!iqf!j0!nga!nh0!nh7!nhe!jr9!h9!ni5!mo9!nj2!mh3!nk1!li7!l3!jg5!jh9!jga@2$a@1$1@1$0#k0\1g@1$1@1$0#k0@2$2@3$5$b@2$h5@2$4@1$0#k0^1$dZ@2$2@2$h4Z@2$4@1$0#k0^1@2$2@2$h3@2$h2@2$4@1$0#k0^1?3msz@1$c@1$3?2mo@3$5$7@3$e@3$6@2$8@1$1@1$0#k0@1$1@1$0#k0@1$h0@1$3?2mo@1$f@1$3?2mo^1@1$h1?3msz$9").
  (* [comment removed for export] *)
  Hypothesis IMGR : ltac2:(zQ "e0!ik9!iqf!nh0!nhe!j5!j0!mg7!nk1!nl0!jhe!nlb!jg5!jh9!ng4>1x@1$d@1$0#k0>0@2$4@2$b$8@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1$9@3$5$2@2$a^2@1$7@1$6?2mo$3").
  Hypothesis SHLAND : ltac2:(zQ "e0!ik9!iqf!nh0!nhe!j5!j0!mg7!mh3!jqf!nm9!nlb!jg5!jh9!ng4>1x@1$d@1$0#k0>0@2$4@2$b$9@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1$8@3$5$2@2$a^2@1$7@1$6?2mo$3").
  (* [comment removed for export] *)
  Hypothesis ATOP : ltac2:(zQ "50!j0!h9!ni5!mg7!nr1@3$0$1@1$2@1$3?2mo@1$4?5HCEIL").
  Hypothesis ZRSH : ltac2:(zQ "h00!ik9!nra!iqf!j5!jg5!jh9!nh0!nhe!j0!jn9!jhe!jqf!nm9!ivc!nlb!ng4>1x@1$f@1$0#k0>0@2$9@2$3@2$4@1$1$b@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1@1$d?5HCEIL@2$3@2$4@1$1$a@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1$c@3$8$6@2$e^2?2Zr$7").   (* [comment removed for export] *)
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.
  Hypothesis SVIS : ltac2:(zQ "b0!ik9!ng4!j0!ns0!nh0!ns7!nhe!nt0!ogd!hvb!nlb>1x@1$1@1$0#k0>0@3$2$4@2$a^1?1S$6@1$7@3$2@1$5@1$1@1$0#8@3$8$9?1m^2@1$3@1$1@1$0#8").
  Hypothesis TMAPS : ltac2:(zQ "d0!ik9!iqf!nh0!nhe!j5!j0!mg7!mh3!nlb!l3!jg5!jh9!ng4>1x@1$c@1$0#k0>0@2$4@2$a?2TH@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?2TH+hgg0@3$5$2@2$8^2@1$7@1$6?2mo$3").
  Hypothesis CMAPS : ltac2:(zQ "d0!ik9!iqf!nh0!nhe!j5!j0!mg7!mh3!nlb!l3!jg5!jh9!ng4>1x@1$c@1$0#k0>0@2$4@2$a?3CTX@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?3CTX+q0@3$5$2@2$8^2@1$7@1$6?2mo$3").
  Hypothesis PMAPS : ltac2:(zQ "e0!ik9!iqf!nh0!nhe!j5!j0!mg7!mh3!jne!nlb!l3!jg5!jh9!ng4>1x@1$d@1$0#k0>0@2$4@2$b?2pa@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1@2$a?2pa$8@3$5$2@2$9^2@1$7@1$6?2mo$3").
  Hypothesis SBMAPS : ltac2:(zQ "e0!ik9!iqf!nh0!nhe!j5!j0!mg7!mh3!jq2!nlb!l3!jg5!jh9!ng4>1x@1$d@1$0#k0>0@2$4@2$b?2sb@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1@2$a?2sb$8@3$5$2@2$9^2@1$7@1$6?2mo$3").
  Hypothesis DNMAPS : ltac2:(zQ "f0!ik9!jp2!iqf!nh0!nhe!j5!j0!mg7!mh3!nlb!l3!jg5!jh9!hr1!ng4>1x@1$e@1$0#k0>0@2$5@2$b@1$1?1d@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a@1$1?1d@2$d+h0+hggg0@3$6$3@2$9^2@1$8@1$7?2mo$4").
  Hypothesis DSMAPS : ltac2:(zQ "f0!ik9!jpa!iqf!nh0!nhe!j5!j0!mg7!mh3!nlb!l3!jg5!jh9!hr1!ng4>1x@1$e@1$0#k0>0@2$5@2$b@1$1?1d@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a@1$1?1d@2$d+8+ogg0@3$6$3@2$9^2@1$8@1$7?2mo$4").
  Hypothesis PAMC : ltac2:(zQ "a0!j0!li7!nh0!nhe!h9!mg7!oh6!mh3!l3!hr1>0@3$0$4?3nch?4nres@3$0$2@3$6@1$7@1$5?2mo@1$1@2$8?2pa@2$9+8?4nres@1$1+iggg0$3").
  Hypothesis PARF : ltac2:(zQ "a0!j0!li7!nh0!nhe!h9!mg7!nj2!nk1!l3!hr1>0@3$0$4?3nch?4nres@3$0$2@3$6@1$7@1$5?2mo@1$1@2$8?2pa@2$9+8?4nres@1$1+iggg0$3").
  Hypothesis PAZR : ltac2:(zQ "d0!ik9!l3!j0!hr1!iqf!nh0!oi6!j5!h9!nlb!jg5!jh9!ng4>0@3$2$8?3nch?4nres>1x@1$c@1$0#k0>0@2$7@2$a@2$1?2pa@2$3+8?4nres@2$4@1$0#k0^1@2$b@2$4@1$0#k0^1@2$1@2$1?2pa@2$3+8?4nres+iggg0@3$2$5@2$9^2?2Zr$6").
  Hypothesis OK : ltac2:(zQ "30!ola!hvb!opc@5$2$1?1L?1S?2Zr@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "f0!li7!ik9!oq4!lj3!l3!ns0!j0!oqf!hvb!os0!osc!ph0!pl5!ng4!iqf@3$6$7@3$9?1L?1S?3msF@7$b@hf$a@1$0+mpis8@2$2@1$1#k0@2$4@2$e@1$1#k0?2sp-o0?2gp?2tp?2x5?2x6?2x7@1$0Z@1$0?4size@1$0$3@1$0@2$4?2TH+t0@1$0?6needed@1$0+8?3x14?3x15?3x16?3x17@1$0+8@1$0?6needed@1$0+og0@1$0?4size@1$0$3@1$0?2SO@2$2@1$1#k0-8@1$0+7@1$0?2TH@1$0+1?3x28?3x29?3x30?3x31?1F@2$2@1$1#k0+mtno4?2fc@1$5@1$d@1$1#k0?1m@1$c$8").

  Let PAE : 7417856 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let POST := alloc_sec_sr_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb SO pa nres nch id nT chunks T rest d.
  Let MID := alloc_sec_mid L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 id nT chunks T rest d.

  (* [comment removed for export] *)
  Theorem alloc_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. eapply alloc_sec_head; try eassumption. intros msF3 mo3 M3.
    eapply alloc_sec_small; try eassumption.
  Qed.
End AllocSec.
