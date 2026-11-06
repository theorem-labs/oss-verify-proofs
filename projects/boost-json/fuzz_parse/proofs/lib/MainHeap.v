(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec StoreOk ShapeAlg SReach RegsEquivM MainEqv MainDefs HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv04cons37Corelib4Init5Logicm61Ije2BVje4BvWf03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~of4getrhe1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~t55rsegsjebbv_unsignedm62eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hic4cellje7Z_to_bv46Stdlib6ZArith6BinInt1Zhna2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hp84bptr69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~htcfloaded_segments04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iib8rw_cells06option04pairm63and3h5LinuxProcessSemanticsfLinuxProcessSem3Runio65mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateirb5Model3h5LinuxProcessSemantics5Riscv7Preludeiv25bvmaphic2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ji73stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jma7mem_invof4mkstof7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~js07hs_KRELjs08hs_RHEAPjs0bhs_rauxv_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ki9dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kn18realizeshp86PStatehna3addhna2lthna3pow69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~kt65hceilhic2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainHeap4Heap~~~~~~li09heap_keptjs08hs_MPRESjs0bhs_alloc_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~lo84RATPlo8dRMALLOC_STACKlo8bRMALLOC_SYMlo85blocklo8crblock_rangelo8arheap_preskn14TSet36Stdlib5Lists4Listmi92Inhna6modulohna3subhna6to_natjs0chs_lb_removelo8bRFREE_STACKlo89RFREE_SYMjs03hsrjs0cheap_sr_hyps69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs~~~~~~mq0aheap_extra" s.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section Heap.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable HS : ltac2:(zQ "10!mo9$0").
  Hypothesis HH : ltac2:(zQ "10!mp0@2$0?5HCEIL?2HS").
  Hypothesis HX : ltac2:(zQ "10!mtb@1$0?2HS").

  Let MALLOC : malloc_sr_stmt HS.
  Proof. ndestruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M & _). exact M. Qed.
  Let FREE : free_sr_stmt HS.
  Proof. ndestruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _). exact F. Qed.
  Let KREL_h : forall s mo, hs_KREL HS s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. ndestruct HH as (_ & K & _). exact K. Qed.

  (* [comment removed for export] *)
  Definition heap_kept : ltac2:(zQ "30!h8!j7!lb@1$0@1$2@1$1#5") := ltac2:(zQ "70!j7!lb!m0!na!ne!o3!oa@3$2@1$1@1$0#5@3$4@1$0#5+2Kv$3@2$5@1$0#5+2@3$2@1$1@1$0#5@3$4@1$0#5+3Kv$3@2$5@1$0#5+3@3$2@1$1@1$0#5@3$4@1$0#5+4Kv$3@2$5@1$0#5+4@3$2@1$1@1$0#5@3$4@1$0#5+8Kv$3@2$5@1$0#5+8@3$2@1$1@1$0#5@3$4@1$0#5+9Kv$3@2$5@1$0#5+9@3$2@1$1@1$0#5@3$4@1$0#5+h2Kv$3@2$5@1$0#5+h2@3$2@1$1@1$0#5@3$4@1$0#5+h3Kv$3@2$5@1$0#5+h3@3$2@1$1@1$0#5@3$4@1$0#5+h4Kv$3@2$5@1$0#5+h4@3$2@1$1@1$0#5@3$4@1$0#5+h5Kv$3@2$5@1$0#5+h5@3$2@1$1@1$0#5@3$4@1$0#5+h6Kv$3@2$5@1$0#5+h6@3$2@1$1@1$0#5@3$4@1$0#5+h7Kv$3@2$5@1$0#5+h7@3$2@1$1@1$0#5@3$4@1$0#5+h8Kv$3@2$5@1$0#5+h8@3$2@1$1@1$0#5@3$4@1$0#5+h9Kv$3@2$5@1$0#5+h9@3$2@1$1@1$0#5@3$4@1$0#5+haKv$3@2$5@1$0#5+ha@3$2@1$1@1$0#5@3$4@1$0#5+hbKv$3@2$5@1$0#5+hb@1$6@1$1@1$0#5").

  (* [comment removed for export] *)
  Lemma malloc_call : ltac2:(zQ "j84!j7!lb!sa!na!t1!ne!o3!hh1!hh9!hi7!hm8!hn0!hp2!m0!ht4!ih2!oa!ii5!im6!h8!in2!ina!io0!ir2!iu9!jh8!ji1!jm3!jq4!jqf!jr6!kg3!kge!kha!km0!kqc!kr8!ks2!ks9!ksf!lh1!lha!lm0!lmd!ln9!lt2!lta!lub!lva!mg3!mh3!mi1!mjc!mk2!mkc!ml3&>0@1$1@1$0#k0@1$h4@1$1@1$0#8&@3$5@1$0#5+4Kv$3@2$6@1$0#5+4&@3$5@1$0#5+aKv$3@2$6@1$0#5+a&@3$5@1$0#5+2Kv$3@2$6@1$0#5+2>4regs@2$h9@1$0#5@1$1@1$0#k0>3mem~0>5model$h8>1s$i4>2LB@1$h3$j0>1n$4>2lo$4>1B$4>4errv@1$1@1$0#k0>2ra$4>1K$j3>0@3$9@1$1@1$0#k0@2$2^b@3$5@1$0#5+1Kv$3@2$6@1$0#5+1@2$b@1$0#k0^2>0@2$h6@2$cZ^3@2$i6^3@2$i7+2+k0>0@3$9$4@2$j5^4+2Z>0@3$9@1$1@1$0#k0@2$2^e~1@2$b@1$0#k0$id>0@3$9@1$1@1$0#k0@2$2^f~2@2$b@1$0#k0^a>0@2$h6@2$c+1^b@2$i6^b@2$i7+2+i0>0@4$i0?2HS^e^d^h0>0@3$hf?2HS^f^h0>0@4$ic?2HS^h0^f^e>0@3$i1?2HS^h3^d>0@2$c@2$8@1$0#k0@2$2^h5~3^e>0@4$hb$7^h5^h0@2$8@1$0#k0@2$2^h6~3>0@2$c@1$i8?5HCEIL^h1>0@2$c^h2@2$j6@2$8@1$0#k0@2$2^h8~3$ie>0@4$h2$7^h8@2$i5@2$8@1$0#k0@2$2^h9~1-q4@3$d$a@1$ha^h1@1$h0$a>0@2$hc$7^h9>0>5regs'@2$h9@1$0#5@1$1@1$0#k0>4mem'~0>6model'$h8>1A$4>1p$e>2s'$i4>5errv'@1$1@1$0#k0>4junk@1$h3@1$1@1$0#8>0>1r@1$1@1$0#5>0@3$j4@1$1@1$0#5^1$ia@3$9@1$1@1$0#k0@2$2^a^2@2$2^i5^2>0@3$9@1$1@1$0#k0@2$2^9~2@2$b@1$0#k0^6>0@3$hf?2HS^5^8>0@3$ib?2HS^i4^9>0@2$hc$7^b>0@4$hb$7^c^i2@2$8@1$0#k0@2$2^i8~3>0@4$h2$7^d@2$i5@2$8@1$0#k0@2$2^i9~1-q4@3$d$a@1$ha^8@1$h0$a>0@3$i1?2HS^e^i3>0@4$j2^i7@2$8@1$0#k0@2$2^ib~3^ia^f>0@3$j1?5HCEIL^e^i7>0@4$i0?2HS^d@3$d@2$h1@2$h1$e$4$4@4$h5@2$h1$e$4$4@4$h5$e$4^e^f^i8^i9^h1>0@4$h2$7^h2^h0@3$d$a@2$i9@1$j7^i9^c@1$h0$a@4$i3$f$i2@2$h7@5$hd?2fx^h4@2$b@1$0#k0^i6^h3@1$he$f^h2^i5@4$i3$f$i2@2$h7@5$hd?2fx^hc@2$b@1$0#k0$if^hb@1$he$f^ha^h2").
  Proof.
    intros regs mem model s LB n lo B errv ra K Hra Hra64 Hra2 Htp Ha0 Hn HRH HKR HAL HAU HB HSTK HLO HLO2 HERR HINV HK.
    (* [comment removed for export] *)
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) fp_regs (Z_to_bv 64 RMALLOC_SYM) fp_csr None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Htp, Ha0.
    eapply sreach_realizes.
    { apply (hx_sr HS HX).
      apply (MALLOC (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 RATP) (getr regs 5) (getr regs 6) (getr regs 7)
                    (getr regs 8) (getr regs 9) (Z_to_bv 64 n) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                    (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                    (getr regs 29) (getr regs 30) (getr regs 31)
                    fp_regs fp_csr mem s LB n lo B errv model);
        try assumption; try reflexivity.
      rewrite <- Htp. exact HERR. }
    (intros c' nd_i1; ndestruct nd_i1 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & A & junk & p & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HBR & HRH' & HBLK)).
    destruct c' as [ms' mo']. cbn [cfg_ms cfg_model] in *. subst ms'.
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m' mo' A p s' errv' junk); try exact HKR'; try exact HMP; try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HBR; try exact HRH'; try exact HBLK.
    - intros r Hr. unfold heap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). reflexivity.
    - rewrite Htp. exact HERR'.
  Qed.

  (* [comment removed for export] *)
  Lemma free_call : ltac2:(zQ "j53!j7!lb!sa!t1!na!ne!o3!hh9!hh1!hi7!hn0!hm8!ht4!ih2!hp2!ii5!m0!oa!in2!ina!ir2!iu9!jh8!ji1!jm3!jq4!im6!jqf!jr6!kg3!kge!mld!kha!km0!kqc!kr8!mjc!ks2!h8!io0!lh1!lm0!lmd!lt2!mmd!mnc!lva!mh3!mi1!ks9!mk2!ksf!mkc&>0@1$1@1$0#k0@1$h2@1$1@1$0#8&@3$5@1$0#5+4Kv$4@2$6@1$0#5+4&@3$5@1$0#5+2Kv$4@2$6@1$0#5+2>4regs@2$h6@1$0#5@1$1@1$0#k0>3mem~0>5model$h5>1s$i3>2LB@1$i6$ie>1p$c>1A$3>1n$3>2lo$3>1B$3>4errv@1$1@1$0#k0>2ra$3>1K$j0>0@3$9@1$1@1$0#k0@2$2^d@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@2$a@1$0#k0^2>0@2$i7@2$eZ^3@2$j1^3@2$j3+2+k0>0@3$9$3@2$j2^4+2Z>0@3$9@1$1@1$0#k0@2$2^h0~1@2$a@1$0#k0$ib>0@3$9@1$1@1$0#k0@2$2^h1@3$5@1$0#5+aKv$4@2$6@1$0#5+a@2$a@1$0#k0^b>0@4$he?2HS^f^e^h1>0@3$hd?2HS^h0^h1>0@3$i4@2$f@2$f$c$3$3@4$h3@2$f$c$3$3@4$h3$c$3^f^e^d^h0>0@3$i0?2HS^h4^c>0@2$e@2$7@1$0#k0@2$2^h6~2^d>0@4$h8$8^h6^f@2$7@1$0#k0@2$2^h7~2>0@2$e@1$i8?5HCEIL^h0>0@2$e^h1@2$j4@2$7@1$0#k0@2$2^h9~2$ic>0@4$ha$8^h9@2$i5@2$7@1$0#k0@2$2^ha~1-q4@3$h0$b@1$h7^h0@1$h1$b>0@2$h9$8^ha>0>5regs'@2$h6@1$0#5@1$1@1$0#k0>4mem'~0>6model'$h5>2s'$i3>0>1r@1$1@1$0#5>0@3$i4@1$1@1$0#5^1$i9@3$9@1$1@1$0#k0@2$2^6^2@2$2^i2^2>0@3$hd?2HS^2^3>0@3$ia?2HS^i0^4>0@2$h9$8^6>0@4$h8$8^7^hc@2$7@1$0#k0@2$2^i4~2>0@4$ha$8^8@2$i5@2$7@1$0#k0@2$2^i5~1-q4@3$h0$b@1$h7^hb@1$h1$b>0@3$i0?2HS^9^hd>0@4$if@3$hf?2HS^i2^i3@2$7@1$0#k0@2$2^i7~2^i6^a>0@4$he?2HS^9@3$hf?2HS^i3^i4^b@4$i2$d$i1@2$h4@5$hb?2fx^d@2$a@1$0#k0^he^c@1$hc$d^b^hd@4$i2$d$i1@2$h4@5$hb?2fx^hd@2$a@1$0#k0$id^hc@1$hc$d^hb^h1").
  Proof.
    intros regs mem model s LB p A n lo B errv ra K Hra Hra64 Hra2 Htp Ha0 HRH HKR HIN HAU HB HSTK HLO HLO2 HERR HINV HK.
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) fp_regs (Z_to_bv 64 RFREE_SYM) fp_csr None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Htp, Ha0.
    eapply sreach_realizes.
    { apply (hx_sr HS HX).
      apply (FREE (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 RATP) (getr regs 5) (getr regs 6) (getr regs 7)
                  (getr regs 8) (getr regs 9) (Z_to_bv 64 A) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                  (getr regs 29) (getr regs 30) (getr regs 31)
                  fp_regs fp_csr mem s LB p A n lo B errv model);
        try assumption; try reflexivity.
      rewrite <- Htp. exact HERR. }
    (intros c' nd_i2; ndestruct nd_i2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s' &
               Hms & HKR' & HMP & HINV' & HSTK' & HERR' & HAU' & HPRES & HRH')).
    destruct c' as [ms' mo']. cbn [cfg_ms cfg_model] in *. subst ms'.
    rewrite (ret_pc_even ra Hra64 Hra2).
    change (MS ?R ?F ?pc ?fc None ?m ?rom) with (mkst R pc m rom).
    eapply (HK _ m' mo' s'); try exact HKR'; try exact HMP; try exact HINV'; try exact HSTK'; try exact HAU';
      try exact HPRES; try exact HRH'.
    - intros r Hr. unfold heap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite Htp. exact HERR'.
  Qed.
End Heap.
