(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec StoreOk ShapeAlg SReach RegsEquivM MainEqv HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import MainDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import MainHeap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~k14getr01Z37Corelib4Init5Logico61Ihf2BVhf4BvWfhfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~r85rsegso62eqhf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hgc4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hl04bptr69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hp4floaded_segments46Stdlib6ZArith6BinInt1Zhtd2le37Corelib4Init9Datatypeshvb4prodhvb4conshvb3nilhvb6optionhvb4pair3h5LinuxProcessSemanticsfLinuxProcessSem3Runijc5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statein15Model3h5LinuxProcessSemantics5Riscv7Preludeiq85bvmaphgc2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~itd3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ji07mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jm58rw_cellsk14mkstk17seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~jrd7hs_KRELjrd8hs_RHEAPjrdchs_lb_removejrdbhs_rauxv_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~kj7dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~knf8realizeshl06PState36Stdlib5Lists4Listkt02Inhtd3addhvb4listo63and69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~kve5hceiljrd8hs_MPRES79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~lke4RATPlkebRFREE_STACKlke9RFREE_SYMlke5blocklkearheap_presknf4TSet79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainHeap~~~~~~ltc9heap_kepthtd2lthtd6modulohtd3powhtd3subjrd3hmf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs~~~~~~mkbbheap_extraM" s.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section HeapM.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable HM : ltac2:(zQ "10!mk4$0").
  Hypothesis HXM : ltac2:(zQ "10!mo8@2$0?5HCEIL?2HM").
  Let FREE : HeapMF_iface.free_mf_stmt HM. Proof. exact (hm_free HM HXM). Qed.

(* [comment removed for export] *)
  Lemma free_callM : ltac2:(zQ "j53!h9!jc!nc!o3!pa!pe!q3!qa!v5!vd!hg2!hk8!hoc!hsa!hv5!ih3!ihb!ii3!iia!ij4!im8!ipf!ise!it7!jh9!jla!jq0!jqc!jr3!kg1!kgc!kh8!ki8!kme!kra!ks6!ku3!ku9!kv0!kv8!lj9!lk2!lp9!lq1!lr0!lrd!ls6!lt4!mh9!mi6!mic!mj6!mjd&>0@1$1@1$0#k0@1$h2@1$1@1$0#8&@3$5@1$0#5+4Kv$4@2$6@1$0#5+4&@3$5@1$0#5+2Kv$4@2$6@1$0#5+2>4regs@2$h6@1$0#5@1$1@1$0#k0>3mem~0>5model$h5>1s$i3>2LB@1$i6$id>1p$c>1A$3>1n$3>2lo$3>1B$3>4errv@1$1@1$0#k0>2ra$3>1K$if>0@3$9@1$1@1$0#k0@2$2^d@3$5@1$0#5+1Kv$4@2$6@1$0#5+1@2$a@1$0#k0^2>0@2$i7@2$eZ^3@2$j1^3@2$j3+2+k0>0@3$9$3@2$j2^4+2Z>0@3$9@1$1@1$0#k0@2$2^h0~1@2$a@1$0#k0$ia>0@3$9@1$1@1$0#k0@2$2^h1@3$5@1$0#5+aKv$4@2$6@1$0#5+a@2$a@1$0#k0^b>0@4$he?2HM^f^e^h1>0@3$hd?2HM^h0^h1>0@3$i4@2$f@2$f$c$3$3@4$h3@2$f$c$3$3@4$h3$c$3^f^e^d^h0>0@3$i0?2HM^h4^c>0@2$e@2$7@1$0#k0@2$2^h6~2^d>0@4$h8$8^h6^f@2$7@1$0#k0@2$2^h7~2>0@2$e@1$i8?5HCEIL^h0>0@2$e^h1@2$j4@2$7@1$0#k0@2$2^h9~2$ib>0@4$ha$8^h9@2$i5@2$7@1$0#k0@2$2^ha~1-q4@3$h0$b@1$h7^h0@1$h1$b>0@2$h9$8^ha>0>5regs'@2$h6@1$0#5@1$1@1$0#k0>4mem'~0>6model'$h5>2s'$i3>0>1r@1$1@1$0#5>0@3$i4@1$1@1$0#5^1$j0@3$9@1$1@1$0#k0@2$2^6^2@2$2^i2^2>0@3$hd?2HM^2^3>0@3$i9?2HM^i0^4>0@2$h9$8^6>0@4$h8$8^7^hc@2$7@1$0#k0@2$2^i4~2>0@4$ha$8^8@2$i5@2$7@1$0#k0@2$2^i5~1-q4@3$h0$b@1$h7^hb@1$h1$b>0@3$i0?2HM^9^hd>0@4$ie@3$hf?2HM^i2^i3@2$7@1$0#k0@2$2^i7~2^i6^a>0@4$he?2HM^9@3$hf?2HM^i3^i4^b@4$i2$d$i1@2$h4@5$hb?2fx^d@2$a@1$0#k0^he^c@1$hc$d^b^hd@4$i2$d$i1@2$h4@5$hb?2fx^hd@2$a@1$0#k0$ic^hc@1$hc$d^hb^h1").
  Proof.
    intros regs mem model s LB p A n lo B errv ra K Hra Hra64 Hra2 Htp Ha0 HRH HKR HIN HAU HB HSTK HLO HLO2 HERR HINV HK.
    apply (realizes_eqv RSEGS (mkCfg (MS (mkR_of regs) fp_regs (Z_to_bv 64 RFREE_SYM) fp_csr None mem (seg_rom RSEGS)) model)).
    2:{ split; [apply ms_eqv_sym; apply mkst_as_MS | reflexivity]. }
    rewrite mkR_of_getr. rewrite Hra, Htp, Ha0.
    eapply sreach_realizes.
    { apply (hm_sr HM HXM).
      apply (FREE (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 RATP) (getr regs 5) (getr regs 6) (getr regs 7)
                  (getr regs 8) (getr regs 9) (Z_to_bv 64 A) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                  (getr regs 29) (getr regs 30) (getr regs 31)
                  fp_regs fp_csr mem s LB p A n lo B errv model);
        try assumption; try reflexivity.
      rewrite <- Htp. exact HERR. }
    (intros c' nd_i1; ndestruct nd_i1 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & s' &
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
End HeapM.
