(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AW_Leaves AW_PoisonShadow AW_AllocBase AW_LargeAlloc1 AW_SysconfPg AW_PoisonRemap1
     SecLazy SecLazy2 AW_GetBlockBegin AW_SecRecycle1 AW_LargeDealloc1 AW_LargeDealloc2 AW_LargeDealloc3 AS_SecRecycle1 AS_SecRecycle2 AllocTacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~05asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~k27mem_inv37Corelib7Numbers7BinNumso64Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~q63stk35stdpp9bitvectorbdefinitionsu8bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hh35aceil46Stdlib6ZArith6BinInt1Zhla2lehla3add37Corelib4Init5Logichnf2eqo61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAllocWalkKit~~~~~~hpd6hiddenhla6modulohnf3andhh34aapphla2lthla3powhnf2or69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~ih5akSpaceSizehh36AHI_LO08AIMG_TOP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~in85akobjih5h0kPtrArrayReserveih54zlen37Corelib4Init9Datatypesitc4Someitc6option36Stdlib5Lists4Listjg69nth_errorhla6to_nathla3sub37Corelib5Lists7ListDefjj76Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAW_LargeAlloc1~~~~~~jl84SENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_PoisonRemap1~~~~~~jq44RENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jv14cellitc4consitc3niljv12C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kka8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kp12wzin85wlist79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~ktb6u64arrjv12C1jv12C2jv12C4hh32shktb5u8arritc6lengthhla3divhla6of_natu82bv3h5LinuxProcessSemanticsfLinuxProcessSem3Runlm05mkCfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~lp54lzokitc4None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsltedmachine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~mi68restrictq63mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mn72MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mra7seg_romu87Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSem5Statenge8m_vmmapsnge7vm_maps69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~nl3eentries_nowrapngebvm_noaccessnl39nooverlapitc4boolitc4truehh39ALOWSH_LOmi6ain_rangesbngebregion_freengebvm_reservedngecmap_containsnge7map_hasitc5false" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SecRecycle.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz sz idx pa nres nch lst lidx TSD CTX TH sb n actx : Z) (chunks : list Z) (ob0 ob1 : byte) (sbs : list byte) (g : word) (b244 : byte).
  Hypothesis MI : ltac2:(zQ "20!jb!nc@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!pf!jb!u2!hg5@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!hl1!hn2@2$1@1$0?5HCEIL?2lo").  Hypothesis HI : ltac2:(zQ "40!pf!hn8!hn2!hg5@2$2@2$1?2lo+ji0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "60!hp3!pf!hp9!htf!hu9!hg5@1$3@3$0$2@2$4@2$5@1$1#k0?2sp+h0Z").
  Hypothesis AR : ltac2:(zQ "a0!hv3!hp3!hp9!hn2!hu9!hva!hl1!hn8!ig2!ig8@2$0@3$5?5HCEIL?1a?3msz@2$0@2$3@2$7?1a?3msz@1$6?5HCEIL@2$0@3$1$2@2$4?1a+hgg0Z@2$0@3$1$2@2$4?3msz+hgg0Z@2$0@2$3+hhgg0?3msz@2$8?3msz@2$9+2+i8").
  Hypothesis SBX : ltac2:(zQ "50!hn8!hn2!igf!htf!il6@1$3@2$2@2$1@2$0?1a?3msz?2sb@2$1@2$0?2sb$4?1a").
  Hypothesis SBR : ltac2:(zQ "70!hn2!hv3!htf!im4!hl1!il6!hn8@1$2@2$1@2$0$3?2sb@2$0@2$6?2sb$5@1$4?5HCEIL").
  Hypothesis TPR : ltac2:(zQ "70!pf!hn2!hg5!hv3!ime!htf!hn8@1$5@2$3@2$1+mqiho8@2$2@1$0#k0?2tp@2$1@2$6@2$2@1$0#k0?2tp+hgg0$4").
  Hypothesis RNG : ltac2:(zQ "b0!hv3!hn2!hn8!hl1!hp3!hp9!ime!ir6!htf!hva!hu9@1$8@2$0@2$1+mqihj0?3TSD@2$0@2$1@2$2?3TSD+8$6@2$0@3$9?5HCEIL?3CTX+q0@2$0@2$1@2$2?3CTX+q0@1$3?5HCEIL@2$0@3$7?5HCEIL?2TH+hgg0@2$0@2$1@2$2?2TH+hgg0@1$3?5HCEIL@3$4$5@2$a?2TH+h0Z").
  (* [comment removed for export] *)
  Hypothesis PLC : ltac2:(zQ "60!hn8!hn2!igf!hv3!irf!htf@1$5@2$3@2$2@2$1@2$0?3CTX+q0?2TH@2$1@2$0?2TH+hgg0?3CTX@2$3@2$2@2$1@2$0?2pa$4?2TH@2$1@2$0?2TH+hgg0?2pa@2$3@2$2@2$1@2$0?2pa$4?3CTX@2$1@2$0?3CTX+q0?2pa@2$3@2$2@2$1@2$0?1a?3msz?2TH@2$1@2$0?2TH+hgg0?1a@2$3@2$2@2$1@2$0?1a?3msz?3CTX@2$1@2$0?3CTX+q0?1a@2$2@2$1@2$0?1a?3msz?2pa@2$1@2$0?2pa$4?1a").
  Hypothesis PAR : ltac2:(zQ "90!hv3!irf!hp3!hp9!hva!hl1!hn8!hn2!hu9@2$0@3$4?5HCEIL?2pa$1@2$0@2$7@2$6?2pa$1@1$5?5HCEIL@3$2$3@2$8?2pa+hgg0Z").
  Hypothesis NCH : ltac2:(zQ "70!hv3!hn2!hp9!hp3!it4!ig2!ig8@2$0@3$3$2@2$4$2?6chunks?3nch@2$0@2$0@2$1Z?3idx@2$5?3idx?3nch@2$0@2$1?3nch?4nres@2$1?4nres@2$6+2+h4").
  Hypothesis IDX : ltac2:(zQ "60!hp9!iv4!ivc!hp3!jh9!ji6@3$3@1$2$0@3$4$0?6chunks@1$5?3idx@2$1$0?1a").
  Hypothesis LNTH : ltac2:(zQ "70!hp9!iv4!ivc!hp3!jh9!jj0!ji6@3$3@1$2$0@3$4$0?6chunks@1$6@2$5?3nch+1@2$1$0?3lst").
  Hypothesis LR : ltac2:(zQ "50!hv3!hva!hl1!hn8!hn2@2$0@3$1?5HCEIL?3lst+hgg0@2$4@2$3?3lst+hgg0@1$2?5HCEIL").
  Hypothesis PLCL : ltac2:(zQ "80!hn8!hn2!igf!hv3!htf!irf!ig2!jj0>0@2$6?3idx@2$7?3nch+1@1$4@2$3@2$2@2$1@2$0?1a?3msz?3lst@2$1@2$0?3lst+hgg0?1a@2$3@2$2@2$1@2$0?3lst+hgg0?2pa@2$1@2$0?2pa$5?3lst@2$3@2$2@2$1@2$0?3lst+hgg0?2TH@2$1@2$0?2TH+hgg0?3lst@2$2@2$1@2$0?3lst+hgg0?3CTX@2$1@2$0?3CTX+q0?3lst").
  Hypothesis LSTA : ltac2:(zQ "30!hp3!hp9!jj0>0@3$0$1?3idx@2$2?3nch+1@3$0$1?3lst?1a").
  (* [comment removed for export] *)
  Hypothesis DISJ : ltac2:(zQ "70!hn2!hv3!hp9!jke!hn8!ig2!ig8@3$3$2\1c$2@2$1@2$1@2$0Z^1@2$5^1@2$6+2+if>0@2$0^1@2$4?1a+hnv0@2$0^2?1a?6chunks").
  Hypothesis NR : 0 <= n < 2^32.
  (* [comment removed for export] *)
  Hypothesis SEN : ltac2:(zQ "10!jpc@5$0?2tp?3TSD?3CTX?2TH?1m").
  Hypothesis REN : ltac2:(zQ "10!ju9@3$0?1g?4b244?1m").
  Hypothesis SB32 : ltac2:(zQ "70!kid!kj5!kjd!jb!kk4!ko5!ksc@4$5$3?1m+hrsrv8@3$1$0@1$4@1$6?2sb@1$2$0").
  Hypothesis INST64 : ltac2:(zQ "70!kid!kj5!kk4!ksc!kjd!jb!ko5@4$6$5?1m+hrssh8@3$1$0@1$2@1$3+hgg0@3$1$0@1$2@1$3?2pa@3$1$0@1$2@1$3?2pa@1$4$0").
  Hypothesis NRES : ltac2:(zQ "70!kid!kj5!kk4!ksc!kjd!jb!ko5@4$6$5?1m+hrssk8@3$1$0@1$2@1$3?4nres@3$1$0@1$2@1$3?3nch@3$1$0@1$2@1$3Z@1$4$0").
  Hypothesis SST : ltac2:(zQ "20!jb!u2@4$1$0?1m+hrssm0+hrsuo0").
  Hypothesis MTX : ltac2:(zQ "70!kid!kj5!kjd!jb!kk4!ko5!ksc@4$5$3?1m+hrsuo0@3$1$0@1$4@1$6Z@1$2$0").
  Hypothesis GST : ltac2:(zQ "20!jb!u2@4$1$0?1m+hrsuo8+hrsur0").
  Hypothesis PA : ltac2:(zQ "30!jb!kt2!lh5@4$2$0?1m?2pa@1$1?6chunks").
  Hypothesis HDR : ltac2:(zQ "70!kid!kj5!kk4!ksc!kjd!jb!ko5@4$6$5?1m?1a@3$1$0@1$2@1$3?1a@3$1$0@1$2@1$3?3msz@3$1$0@1$2@1$3?2sz@3$1$0@1$2@1$3?3idx@1$4$0").
  Hypothesis LSTC : ltac2:(zQ "a0!kid!kj5!kjd!jb!kk4!ko5!ksc!hn8!ig2!jj0>0@2$8?3idx@2$9?3nch+1@4$5$3?1m@2$7?3lst+h8@3$1$0@1$4@1$6?4lidx@1$2$0").
  Hypothesis CHDR : ltac2:(zQ "b0!kid!kj5!ksc!lhf!kjd!jb!li5!lib!kk4!ko5!hn8@4$9$5?1m@2$a?1a+hnv0@3$1$0@1$3?3ob0@3$1$0@1$3?3ob1@3$1$0@1$6@1$2Z@3$1$0@1$7@1$2?1n@3$1$0@1$8@1$2?4actx@1$4$0").
  Hypothesis TST : ltac2:(zQ "30!hn8!jb!u2@4$2$1?1m@2$0?2TH+qv0@2$0?2TH+sm0").
  Hypothesis SHD : ltac2:(zQ "30!jb!lj1!lj7@4$2$0?1m@1$1?1a?3sbs"). Hypothesis SHDL : ltac2:(zQ "70!lk0!hp3!pf!hp9!lka!ll1!llb@3$1$3@1$5@2$0@1$6@1$2#8?3sbs@2$4?3msz+8").
  Hypothesis OK : ltac2:(zQ "30!loc!jb!lse@5$2$1?1L?1S?2Zr@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "d0!pf!lt6!hp3!mh5!jb!mm5!mn1!mr4!mv9!ksc!hn8!ng4!llb@3$2$3@3$5?1L?1S?3msF@7$7@hf$6?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0@1$9@2$a?1a+hnv0?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$b@1$0#k0+mrjpc?2fc@1$1@1$c@1$0#k0?1m@1$8$4").

  (* [comment removed for export] *)
  Hypothesis NW : ltac2:(zQ "30!njc!nk8!np0@1$2@1$1@1$0?2mo"). Hypothesis NWA : ltac2:(zQ "30!njc!nq2!np0@1$2@1$1@1$0?2mo").
  Hypothesis NOV : ltac2:(zQ "30!njc!nk8!nr1@1$2@1$1@1$0?2mo").
  (* [comment removed for export] *)
  Hypothesis ZRSH : ltac2:(zQ "h00!pf!lj1!hg5!hv3!hn2!ig2!nre!ns6!hp3!igf!ime!im4!nse!hl1!ntb!llb>1x@1$f@1$0#k0>0@2$9@2$3@2$4@1$1$b@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1@1$d?5HCEIL@2$3@2$4@1$1$a@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1$c@3$8$6@2$e^2?2Zr$7").
  Hypothesis HSRF : ltac2:(zQ "h21!pf!hg5!lj1!hn2!hv3!hn8!llb!nre!ns6!hp3!igf!njc!nu9!nv8!ime!im4!nse!hl1&@2$5@2$1@1$0#k0^2@2$1@1$0#k0^1>1a@1$6@1$0#k0>1n@1$6@1$0#k0>0@2$a@2$4@2$3@1$2$f@2$1@1$0#k0^2@2$3~0@1$2@1$h1?5HCEIL@2$4@2$3@1$2$e@2$1@1$0#k0^2@2$3~0@1$2$h0@3$9$7@3$c@1$d@1$b?2mo^3^2$8").
  Hypothesis HSMC : ltac2:(zQ "h31!pf!hg5!lj1!hn2!hv3!hn8!llb!nre!ns6!hp3!igf!njc!og7!nk8!ime!im4!nse!hl1!ig2&@2$5@2$1@1$0#k0^3@2$1@1$0#k0^2>1a@1$6@1$0#k0>1n@1$6@1$0#k0>0@2$h2Z@2$1@1$0#k0^1>0@2$a@2$4@2$3@1$2$f@2$1@1$0#k0^3@2$3~0@1$2@1$h1?5HCEIL@2$4@2$3@1$2$e@2$1@1$0#k0^3@2$3~0@1$2$h0@3$9$7@3$c@1$d@1$b?2mo^4^3$8").
  (* [comment removed for export] *)
  Hypothesis HSNA : ltac2:(zQ "h21!pf!hg5!lj1!hn2!hv3!hn8!llb!nre!ns6!hp3!igf!njc!nu9!nq2!ime!im4!nse!hl1&@2$5@2$1@1$0#k0^2@2$1@1$0#k0^1>1a@1$6@1$0#k0>1n@1$6@1$0#k0>0@2$a@2$4@2$3@1$2$f@2$1@1$0#k0^2@2$3~0@1$2@1$h1?5HCEIL@2$4@2$3@1$2$e@2$1@1$0#k0^2@2$3~0@1$2$h0@3$9$7@3$c@1$d@1$b?2mo^3^2$8").
  (* [comment removed for export] *)
  Hypothesis WIN : ltac2:(zQ "d0!pf!lj1!hg5!nre!ns6!hv3!hp3!ntb!hn8!lka!hn2!ig2!llb>1x@1$c@1$0#k0>0@2$5@2$a@1$1?1a@2$2@1$0#k0^1@2$b@2$2@1$0#k0^1@2$8@1$1?1a@2$9?3msz+8@3$6$3@2$7^2?1S$4").
  Hypothesis HAS : ltac2:(zQ "70!ksc!nre!ns6!hp3!njc!oh7!nk8@3$3$1@3$5@1$6@1$4?2mo@1$0?1a@1$0?3msz$2").
  Hypothesis NOL : ltac2:(zQ "b0!pf!hg5!nre!oi2!hv3!hp3!ntb!hn8!hn2!ig2!llb>1x@1$a@1$0#k0>0@2$4@2$8?1a@2$1@1$0#k0^1@2$9@2$1@1$0#k0^1@2$7?1a?3msz@3$5$2@2$6^2?1L$3").
  Hypothesis NOACC : ltac2:(zQ "d0!pf!hg5!nre!oi2!hv3!hp3!njc!nq2!ntb!hn8!hn2!ig2!llb>1x@1$c@1$0#k0>0@2$4@2$a?1a@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?1a?3msz@3$5$2@2$8^2@1$7@1$6?2mo$3").
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Let ARE : 7430144 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 7430144 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let LRE : 7430144 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Let POST := recycle_sec_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.

  (* [comment removed for export] *)
  Theorem recycle_sec_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    assert (NWL : entries_nowrap L) by (apply (lazy_ranges_okb_nowrap asegs); exact (lzok_ranges OK)).
    eapply recycle_sec_head; try eassumption. intros msF3 mo3 M3.
    (* [comment removed for export] *)
    eapply recycle_sec_poison; try eassumption. intros msF4 mo4 M4.
    eapply recycle_sec_unmap with (L := L) (S := S) (Zr := Zr); try eassumption.   (* [comment removed for export] *)
  Qed.
End SecRecycle.
