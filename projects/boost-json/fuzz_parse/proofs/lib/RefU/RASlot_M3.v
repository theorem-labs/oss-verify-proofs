(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W11 ASlot_I ASlot_M0 ASlot_M3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W11 RASlot_M0 RASlot_M2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RBand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv4.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hf3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~m86mstate35stdpp9bitvectorbdefinitionsqf2bv37Corelib4Init9Datatypest14listm84aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~v76PState37Corelib4Init5Logichjc3andt14prodhjc2eqm84optrqfbbv_unsignedt16option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ho25rsegst14Some46Stdlib6ZArith6BinInt1Zhsf3add01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hv14cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ij58rw_cellsv75ps_fav74ps_mv75ps_sot14Nonet14const13nilt14pairt14unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~ir54ALLCir59ENTRY_REL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~jga6ta_rel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~jl53ISTjl57ta_fail79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~jqe2bSjqe2kS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~jvc9meta_slotjvc8ticks_okhf6am_relhfbbrk_link_pshf7leaf_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~kn89unk_agreehv12C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ksd3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~lh07mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU9RASlot_M2~~~~~~ll54rFRM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~lpe5rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~lu98rauxv_oklu9crpres_except79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMalloc_fp~~~~~~mk8armalloc_fpm86activem8aalloc_metam8cget_meta_recm84metam85meta03h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmscdmachine_stateqf7Z_to_bvjvc2wzhsf3mulm84UNITm8asize_classlpe6RMLOCKksd3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~nl02MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~np37seg_romlpe4RCTXlpedRSIZE_CLASSESlpeaRSSP_GUARDm84concm85usagehsf2leir57ag_mmap99OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU9RASlot_M33HCW5LEVEL~~~~~~oi47rag_ctxoi4arcnt_statelu96rimplThsf2ltir57ag_nestll59rHAG_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~or0bAREACH_fromlpecref_reservedhsf3powoi49rHMM_stmtoi4brHNEST_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : ltac2:(zQ "20!ov5!pg4@4$0?4HSEC@1$1?5HCEIL?3st0?2LB").
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : ltac2:(zQ "30!hl0!oh3!op2@2$0@2$1Z?2sc@2$2?2sc+j0").
Hypothesis RQ : ltac2:(zQ "40!hl0!oh3!op2!ph4@2$0@2$1Z?3req@2$2?3req@2$3+2+i0").
Hypothesis FIT : ltac2:(zQ "40!nj2!hu7!oh3!ni4@2$2@2$1?3req+4@2$3+h0@1$0?2sc").
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : hceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

(* [comment removed for export] *)
Definition rag_ctx : ltac2:(zQ "70!h9!m2!q6!sc!u9!v0!hj3>3st1$2>3st2$2>2mm$5>2m3$1>2s'$6>5errv'@1$3@1$0#k0>4junk@1$4@1$3@1$0#8>2oo$1P") := ltac2:(zQ "j50!hl0!q6!h9!v0!hl7!hle!hm4!hmb!hn9!hrf!hs8!hu7!hue!m2!iid!in0!inc!io4!iob!sc!ip3!ipa!u9!iq1!iq7!iqe!iv5!ivd!jkb!jpc!jq3!jv0!jv6!kje!kkb!kl7!km0!kme!kra!ks7!lg9!lka!lp6!lu0!mic!mj8!moa!mp8!mq1!mqe!mrd!ms4!hj3\3st1$1\3st2$1\2mm$3\2m3$d\2s'$j4\5errv'@1$h3@1$2#k0\4junk@1$h6@1$h3@1$2#8\2oo$d@2$0@3$he?2sc?2st^8@2$0@3$hc?2sc?2st^8@2$0@3$5$6@2$if^8?2sc@1$h4$3@2$0@4$i5@1$8@2$4$1$6^1@4$j0@1$8@2$4$1$6^8@2$i0$1$6@1$hf@2$4$1$6@2$a@2$4$1@1$8$3@4$h8$1@1$8$3^7@2$a$3^6@2$0@2$hd?3st0^7@2$0@2$hb?3st0^7@2$0@1$ha^7@2$0@3$i3^8^7@2$a$3^6@2$0@3$5$j2@2$j1^7^6$j3@2$0@2$i1^7^6@2$0@4$ib?5HCEIL?4HSEC^7^5@2$0@1$i2^7@2$0@3$i6^7?1o^5@2$0@2$i9$9^5@2$0@4$i8$9^5?2lo@2$b@2$7@1$2#k0?2sp-p0@2$0@4$f$9^5@2$b@2$7@1$2#k0?2sp-p0@d$ia?4HSEC?2ra?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9^2@2$0@4$f$9^5@2$b@2$7@1$2#k0?2tp-q4@3$h5$e@1$i7^3@1$h7$e@2$0@4$ic?5HCEIL?4HSEC^5@2$7@1$2#k0?2sp@2$0@3$id@4$ie?3st0^7?2lo@2$7@1$2#k0?2sp?1m^5@2$0@2$i4^7^4@2$0@3$5$1@1$h1^4@1$h1?1s@2$0@3$5@2$4$c$c@1$h0^4@1$h0?1s@3$5$h9@1$h2^4@1$h2?1s").

(* [comment removed for export] *)
Definition rcnt_state : ltac2:(zQ "70!h9!sc!hue!ng3!m2!v0!q6>2pc$2>3st2$6>2mm$5>4cnt1$2>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>2m3$4$3") := ltac2:(zQ "h80!h9!nh4!sc!nhe!ni4!hu7!nib!nj2!hue!njf!ip3!m2!nk9!nod!nt2!ntd!nu5!nv6!hrf!v0!og4!q6!ogb!hmb\2pc$8\3st2$h5\2mm$h3\4cnt1$8\3t0'@1$2@1$0#k0\3t1'@1$2@1$0#k0\3t2'@1$2@1$0#k0\3a6'@1$2@1$0#k0\3a7'@1$2@1$0#k0\3t3'@1$2@1$0#k0\3t4'@1$2@1$0#k0\3t5'@1$2@1$0#k0\3t6'@1$2@1$0#k0\2m3$b@7$d@hf$c@2$1@1$0#k0+ugttc@2$1@1$0#k0@2$5@2$h7@1$0#k0?2sp-p0?2gp?2tp^a^9^8@2$1@1$0#k0?2sc@2$1@1$0#k0@2$h4^d^c@1$3@2$h6^d?2sc@1$3+hgg0@1$3@2$5@2$4@1$7?2sc$6+h0@1$3+og0@1$3@2$4@2$4@1$7?2sc$6^b@1$3@2$5@2$4@2$4@1$7?2sc$6^b+h0^7^6?2a1@1$3^b@2$1@1$0#k0$h1@2$1@1$0#k0@2$5@2$5$f+l0@2$4+8?2sc@2$1@1$0#k0$9@2$1@1$0#k0@2$5$9@2$4+8?2sc@1$3@2$4@1$7?2sc$6@2$1@1$0#k0$h0?3s10?3s11^5^4^3^2?1F@2$1@1$0#k0^e?2fc@1$a@1$2@1$0#k0^1@1$e$h2").

Definition rHMM_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h30!h9!sc!m2!nib!q6!oh3!ni4!u9!hl0!hue!oh9!omf!ona!oo8!v0!nj2!hj3!hu7!op2>3st1$4>3st2$4>2mm$e>2m3$2>2s'$h0>5errv'@1$1@1$0#k0>4junk@1$7@1$1@1$0#8>2oo$2>4cnt1$9>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@8$b^h2^h1^h0^f^e^d^c^b>0@2$8@2$5+1^b@2$5^b+i0>0@2$h2+og0@2$h1@2$6@2$6@1$f?2sc$3^c$3@7$d?5HCEIL?1R?1o@8$a?1R?2sc?3req?1k?4bail^h4^h3^d^h1?1Q@e$c+ugur0^h4^h3^d^c^b^a^9^8^7^6^5^4^h2").

Definition rHNEST_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h20!h9!sc!oh3!m2!nib!q6!ni4!u9!hl0!hue!op8!omf!ona!oo8!v0!nj2!hj3!hu7>3st1$5>3st2$5>2mm$e>2m3$3>2s'$h0>5errv'@1$1@1$0#k0>4junk@1$7@1$1@1$0#8>2oo$3>4cnt1$9>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@8$b^h2^h1^h0^f^e^d^c^b>0@2$8@2$2+1^b@2$2^b+i0>0@2$2@2$h1@2$6@2$6@1$f?2sc$4^c$4+og0@7$d?5HCEIL?1R?1o@8$a?1R?1f?2sc?1k?4bail^h4^h3^d^h1?1Q@e$c+uguv4^h4^h3^d^c^b^a^9^8^7^6^5^4^h2").

Hypothesis HMM : ltac2:(zQ "10!phb$0").
Hypothesis HNEST : ltac2:(zQ "10!pi8$0").

Lemma rhag_ok : ltac2:(zQ "10!oq3@i2$0?5HCEIL?4HSEC?1R?1f?1k?4bail?1o?1s?1Q?2ra?2sp?2gp?2tp?2s0?2s1?2a1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1m?3st0?2st?2lo?2sc?3req").
Proof. try hcb. try hsb.
  intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
  intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
  assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
  pose proof (size_class_range sc SC) as SZR.
  rewrite (ag_body_eq f sc req k bail st2 mm).
  riprefixT. unfold rag_regs.
  eapply evt_cut.
  { eapply (rcount_walk st2 m3 sc MR3 SC UR). exact MI3. }
  cbv beta. (intros ms' nd_i1; ndestruct nd_i1 as (a2'' & a3'' & a4'' & ->)).
  set (size := size_class sc * UNIT).
  set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
  assert (C0R : 1 <= cnt0 <= 32).
  { pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
    subst cnt0. destruct (Z.ltb_spec sc 9).
    - unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
      destruct (negb _); [lia|]. destruct (negb _); lia.
    - apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
      pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
  eapply evt_cut.
  { eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
  cbv beta. intros ms' ->. unfold rcnt_regs.
  set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
  assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
  assert (EC : ag_cnt1 sc st2 = cnt1).
  { unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
  rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
  apply evt_done.
  destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
  - pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
  - pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.

End HCW.

