(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W8 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_I ASlot_M0 ASlot_M1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv4.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~k16mstatehf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~p25asegsk14aptrhfbbv_unsigned37Corelib4Init9Datatypesv26optionv24prod37Corelib4Init5Logichha2eqk14optr46Stdlib6ZArith6BinInt1Zhjb3addv24Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hm18rw_cellsv24None01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hr24cellk14conc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hvd5ps_fahvd4ps_mhvd5ps_sov24consv24listv23nilv24pairv24unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~in54ALLCin59ENTRY_RELin57ag_body79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~it56ta_rel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W10~~~~~~ji08ag_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~jme3ISTjme7ta_fail79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~js72bSjs72kS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~kh53CTXkh59meta_slotkh54mrepkh58ticks_okkh52wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~ko56am_relko57auxv_okko5bbrk_link_psko55implTko57leaf_ofko53memko5bpres_except79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~lh69malloc_fplh69unk_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface~~~~~~ln26MEDTABln2cmedtab_cellshr22C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lt73mkRlt73stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mi12MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mm47mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mq97seg_romk16activek1aalloc_metak1cget_meta_reck14metak15meta0k1asize_classhvd6PState" s.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section EPI2.
Variables (lo : Z).
Hypothesis CLO : alloc_ceiling <= lo.
End EPI2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.

(* [comment removed for export] *)
Definition HAG_stmt : ltac2:(zQ "00P") := ltac2:(zQ "k00!h9!jc!nf!o8!t5!td!u4!hga!hh3!hie!hj4!hl3!hla!hpc!hq8!hqf!hue!hv6!ij9!ik2!ika!il3!ila!im1!im7!ime!ir5!ird!isa!jh6!jm2!jr5!jrc!kg9!kgf!kl7!kle!kmb!kn3!knf!ks8!kt2!ktd!kuc!kv5!lg0!lg7!ll8!lm5!lr7!ls1!lt1!mh3!mha!mle!mpe!mu8!mv3!mvc!ng9!nh8!nhf!ni7!nj4>3st1$2>3st2$2>2mm$5>2m3>0@1$1@1$0#k0@1$7@1$1@1$0#8>2s'$jf>5errv'@1$1@1$0#k0>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>1j@1$h6@1$1@1$0#8>2oo$id>0@3$i0?2sc?2st^h5>0@3$hd?2sc?2st^h6>0@3$9$a@2$j9^h7?2sc@1$e$5>0@4$ic@1$7@2$8$2$a^4@4$ja@1$7@2$8$2$a^h8@2$i2$2$a@1$i1@2$8$2$a@2$c@2$8$2@1$7$5@4$h8$2@1$7$5^h7@2$c$5^h6>0@2$hf?3st0^h8>0@2$hb?3st0^h9>0@1$ha^ha>0@3$i8^hc^hb@2$c$5^ha>0@3$9$jc@2$jb^hc^hb$jd>0@2$i4^hd^hc>0@2$i5^he^hc>0@1$i6^hf>0@3$j0^i0?1o^he>0@2$j7$4^hf>0@4$j5$4^i0?2lo@2$b@2$6@1$0#k0?2sp-m0>0@4$d$4^i1@2$b@2$6@1$0#k0?2sp-m0@8$he?2sc^h1?2s4?2s3?2s2?2s1?2s0?2ra>0@4$d$4^i2@2$b@2$6@1$0#k0?2tp-q4@3$h5$h0@1$j3^i0@1$h7$h0>0@2$i9^i3@2$6@1$0#k0?2sp>0@4$d$4^i4$j1$j2>0@3$ie@4$if?3st0^i7?2lo@2$6@1$0#k0?2sp?1m^i5>0@2$ia^i8^i5>0@3$9$2@1$h3^i6@1$h3?1s>0@3$9@2$8$f$f@1$h2^i7@1$h2?1s>0@3$9$h9@1$h4^i8@1$h4?1s@7$ib?5HCEIL?1R?1o@8$hc?1R?1f?2sc?3req?1k?4bail^ic^ib^i9?1Q@7$j6@hf$j4@2$3@1$0#k0+hmjvc@2$3@1$0#k0@2$b@2$6@1$0#k0?2sp-m0?2gp?2tp^i7^i6^i5@2$3@1$0#k0?2sc@2$3@1$0#k0$i3@2$3@1$0#k0@2$h1^ic^ib^i4^i3^i2^i1^i0^hf@2$3@1$0#k0@2$h1^ic^ib@2$3@1$0#k0@2$b?2sc+a@1$i7@1$je?2sc?2a1?2s5?2s6?2s7?2s8?2s9?3s10?3s11^he^hd^hc^hb?1F@2$3@1$0#k0+hmkg4?2fc@1$e@1$1@1$0#k0^ia@1$j8$4").
Hypothesis HAG : HAG_stmt.
End LEVEL.

End HCW.

(* [comment removed for export] *)
