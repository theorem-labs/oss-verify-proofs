(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M5D.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_M0 RASlot_M2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RBand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv4.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hf4conchf6mstate35stdpp9bitvectorbdefinitionsmd2bv37Corelib4Init9Datatypesof6option37Corelib4Init5Logicr02eq01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~sc9meta_slot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~hha4mrel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~hm45rmrephf4aptrhf6region01N25stdpp9countablehs1bN_countable35stdpp7numbers1Nhu16eq_decr03andof4Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMalloc_fp~~~~~~ig9armalloc_fphf6r_basehf6r_kindhf5r_lenhf9s_regions46Stdlib6ZArith6BinInt1Zine2le25stdpp4baseipc6lookup25stdpp4gmapir24gmapir2bgmap_lookupr02exhf5rkindsc2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iu72wahf5Knownhf7RKGrouphf9cell_readhf7cellvalhfaget_shadowhfbround_up_pgine3addine2lthm44RATPmd7Z_to_bvmdbbv_unsigned3h5LinuxProcessSemantics5Riscv7Preludejp75bvmapine3mulsc2wzhm46RMLOCK79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_M5D~~~~~~jtc4ncls79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ki63mkRhm44RCTXhm4dRSIZE_CLASSEShm4aRSSP_GUARDhf4UNIThfasize_class79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~kq43mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~kue6PStateof4listof4prodhf4optr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~lk95rsegsine3subof4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~lpc2bSlpc2kSkq47leaf_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~lv54cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mj98rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~mo0crpres_excepthfec_mmap_counterhf3ctxkue5ps_fakue4ps_mkue5ps_soof4Noneof4consof3nilof4unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~nhe4ALLCnhe9ENTRY_RELnhe7as_inv2jtc4nreq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~no66ta_rel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~nt13ISTnt17ta_failsc8ticks_okkq46am_relkq4bbrk_link_pshha9unk_agreelv52C4ki63stkiu77mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref9RASlot_M2~~~~~~on34rFRMmo08rauxv_okhf6activehfaalloc_metahfaalloc_slothf8full_layhfcget_meta_rechf4metahf5meta0ine3pownhe5as_kq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~pi32MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~pm67seg_rom99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRASlot_M5D3HCW5LEVEL~~~~~~pr09rnest_ctxpr0arnest_regsmo06rimplThf9free_metahfaget_strideof3sndof3fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~qk53rdvkq48pans_memhha7slot_okhf7ag_tailhfcm_set_maplenhfbnest_layouthf7slot_ofhf8upd_metaipc5emptyir2agmap_empty" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rconc_meta_stable' : ltac2:(zQ "b0!h9!ld!m4!oa!q7!s4!s9!hge!hlc!hq5!hqe>2st$2>3stE$2>1m>0@1$3@1$0#k0@1$4@1$3@1$0#8>1q$a>0@4$9?5HCEIL?4HSEC^4^2>0@2$8^5^4>0@2$7^6^3@3$5$6@2$1^6^4@2$1^7^4").
Proof. intros st stE m q. try hcb. try hsb.
  (intros MR REL nd_i1; ndestruct nd_i1 as (ar & arr & kk & Ha & Hk & ->)). pose proof MR as (WF & _). npose WF as (_ & _ & _ & WA & _).
  ndestruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rmalloc_fp_widen : ltac2:(zQ "h50!hr5!hre!s9!s4!ht2!hv2!hvc!m4!ig2!q7!ika!il8!im1!ima!in2!ip6!iq8!ire!is6!it5!ita>3st0$7>3stA$7>3stB$7>2lo$2>2sp$2>3sp'$2>1a$2>0@2$f^2^3>0>3rid$1>1r$0>0@3$3@1$9$0@6$h0$1$0@4$h1$1$5$4$0@4$h2$1$5$4$0^2@1$e^9@2$8$0^1@2$h3$0\2r'$0@2$6@3$3@1$9$0@6$h0$1$0@4$h1$1$5$4$0@4$h2$1$5$4$0^4@1$e^a@2$8$0^1@2$6@3$3$h4@1$c^1@1$c^3@2$6@3$3$2@1$b^1@1$b^3@2$f@1$d^3@1$d^1>0@5$a^9^8^6^4^3@5$a^a^8^7^6^4").
Proof. intros st0 stA stB lo sp sp' a. try hcb. try hsb.
  intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
Lemma rregion_byte_raw : ltac2:(zQ "i00!hr5!s4!hre!h9!oa!q7!ig2!s9!ht2!hv2!hvc!iu2!ji1!hq5!ji7!jif!jj9!jk5!jkf!m4!il8!im1!ima!ita!jlc!in2!jma!ip6!jn1!iq8!ire!is6>2st$h3>1m>0@1$4@1$3#k0@1$5@1$4@1$3#8>3rid$2>1r$0>3off$7>1v$7>0@4$d?5HCEIL?4HSEC^6^5>0@3$1@1$5$0@6$hd$2$0@4$he$2$9$8$0@4$hf$2$9$8$0^5@1$h9^7@2$6$0^4>0@3$1$h7@1$h5^5$f>0@2$a@2$hbZ^5@2$hc^5@1$h8@1$h6^6>0@3$1$h1@2$h0@2$h2^a^8^6@1$e^5@3$1@1$5@1$4@1$3#8@1^a@1$c@2$ha@1$h4^8^7@2$6@1$4@1$3#8@1$b^6").
Proof. intros st m rid r off v. try hcb. try hsb.
  intros MR Hr Hk Ho Hc.
  destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  ndestruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rerrno_lit5 : ltac2:(zQ "80!h9!s4!oa!s9!jn7!jma!jnf!jo9>2tp@1$2@1$0#k0>0@3$1@1$2@1$0#k0^1@2$6@1$0#k0$4@3$1$3@2$5@2$7@1$0#k0^2-q4+hgrmh4").
Proof. intros tp. try hcb. try hsb. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
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
Definition rnest_regs : ltac2:(zQ "60!h9!oa!s9!jrd!hqe!m4>3st2$5>2mm$4>4cnt1$2>3a0v@1$1@1$0#k0>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0@2$3@1$0#5@1$1@1$0#k0") := ltac2:(zQ "h30!h9!oa!jnf!jma!js6!jsd!jt2!s9!khe!km2!km9!kn1!ko2!kp0!hqe!ld!m4!kp7!jo9\3st2$h0\2mm$e\4cnt1$7\3a0v@1$1@1$0#k0\3t0'@1$1@1$0#k0\3t1'@1$1@1$0#k0\3t2'@1$1@1$0#k0\3a1'@1$1@1$0#k0\3a2'@1$1@1$0#k0\3a3'@1$1@1$0#k0\3a4'@1$1@1$0#k0\3a5'@1$1@1$0#k0\3a6'@1$1@1$0#k0\3a7'@1$1@1$0#k0\3t3'@1$1@1$0#k0\3t4'@1$1@1$0#k0\3t5'@1$1@1$0#k0\3t6'@1$1@1$0#k0@hf$9@2$2@1$0#k0+ttrhc@2$2@1$0#k0@2$3@2$h2@1$0#k0?2sp-p0?2gp?2tp^e^d^c@2$2@1$0#k0?2sc@2$2@1$0#k0@2$f^h2^h1^f^b^a^9^8^7^6^5@2$2@1$0#k0@2$8?2sc^h0@1$5^h0@2$2@1$0#k0$c@2$2@1$0#k0@2$3@2$3$a+l0@2$4+8?2sc@2$2@1$0#k0$6@2$2@1$0#k0@2$3$6@2$4+8?2sc@1$5@2$4@1$h1?2sc$d@2$2@1$0#k0$b?3s10?3s11^4^3^2^1").

(* [comment removed for export] *)
Definition rnest_ctx : ltac2:(zQ "80!ku7!m4!h9!s9!lia!oa!lj4!hqe>3st1$1>3st2$1>2mm$7>4cnt1$3>3st3$1>3idx$3>2m4$0>3m''$0>2s'$4>3s''$4>6errv''@1$5@1$2#k0>4junk@1$6@1$5@1$2#8>2oo$0>2o3$0P") := ltac2:(zQ "k40!hvc!m4!s9!ljb!h9!q7!hqe!jo9!s4!lk2!ig2!ku7!lo5!ip6!loe!lp5!khe!lte!lu4!lua!mj1!mn4!hq5!ms2!ika!kp0!mt2!mu3!lia!mu9!mv2!mva!jma!js6!oa!ng3!nga!lj4!nh1!nh7!nle!nm6!nn3!nne!ns7!oh8!ohf!hge!oia!oj5!ojf!hlc!oke!olb!om1!om8!or3!orb!os7!ot0!otd!oua!ov5!pg4!pgb!kp7!jn1!ph3\3st1$1\3st2$1\2mm$6\4cnt1$2\3st3$1\3idx$2\2m4$b\3m''$b\2s'$hc\3s''$hc\6errv''@1$i2@1$4#k0\4junk@1$i5@1$i2@1$4#8\2oo$b\2o3$b@2$0@3$ie?2sc?2st^e@2$0@3$ic?2sc?2st^e@2$0@3$8$9@2$ja^e?2sc@1$i3$6@2$0@4$h3@1$5@2$3$1$9^2@4$jb@1$5@2$3$1$9^e@2$h2$1$9@1$h1@2$3$1$9@2$a@2$3$1@1$5$6@4$f$1@1$5$6^d@2$a$6^c@2$0@2$id?3st0^d@2$0@2$i9?3st0^d@2$0@1$i8^d@2$0@3$j1^e^d@2$a$6^c@2$0@3$8$jf@2$je^d^c$k0@2$0@2$if^d^c@2$0@2$0@2$d+1^b@2$d^b+i0@2$0@2$d@2$i0@2$i1@2$i1@1$k1?2sc$h9^b$h9+og0@2$0@4$h3@1$5@2$3$1$2^1@8$jc@1$5@2$3$1$2$jd?1f^d@2$h0?2sc^b@2$ib?2sc^b@2$h2$1$2@1$h1@2$3$1$2@2$a@2$3$1$2@4$f$1$2^a^9@2$0@2$j7$c^7@2$0@4$j6$c^7?2lo@2$e@2$7@1$4#k0?2sp+p0@2$0@4$h5$c^7@2$i0@2$7@1$4#k0?2tp-q4@3$i4$h4@1$j5^4@1$i6$h4@2$0@4$j9?5HCEIL?4HSEC^7@2$e@2$7@1$4#k0?2sp+p0@2$0@4$h6?5HCEIL?4HSEC^a^7@2$0@1$j0^a@2$0@3$j4^a?1o^7@2$0@3$h7@4$h8?3st0^a?2lo@2$e@2$7@1$4#k0?2sp+p0^8^7@2$0@2$j3^d^a@2$0@2$j2^a^5@2$0@3$8$1@1$he^5@1$he?1s@2$0@3$8@2$3$2$2@1$hd^5@1$hd?1s@2$0@3$8$i7@1$hf^5@1$hf?1s@2$0@5$ia?3st0^d^a@2$h0?2sc^b^9@2$0@2$0@2$dZ@1$ha@1$hb^a@2$k2@1$ha@1$hb^a@2$k3+2+i0@2$0@4$h5$c^7@2$e@2$7@1$4#k0?2sp+p0@d$j8?4HSEC?2ra?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9^3@2$0@3$h7@4$h8?3st0^d?2lo@2$7@1$4#k0?2sp?1m^8@4$h6?5HCEIL?4HSEC^d^8").

Definition rNFAIL_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h20!h9!oa!ku7!m4!ng3!hqe!lia!jnf!lj4!s9!pha!pm0!pq5!pvb!qg8!qh6!lo5!qi0>3st1$3>3st2$3>2mm$5>4cnt1$9>3st3$3>2m4$2>3m''$2>2s'$6>3s''$6>6errv''@1$1@1$0#k0>4junk@1$8@1$1@1$0#8>2oo$2>2o3$2>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@e$d^hb^ha^h9^h8^h7-1^h6^h5^h4^h3^h2^h1^h0^f@7$f?5HCEIL?1R?1o@5$h1?1R^ha^h8\3st4$3@6$a?1R?2sc?1k?4bail^1@1$4$5?4bail^h4?1Q@7$b@h2$e^hb^ha^h9@2$7@1$0#k0-1^f^e^d^c^b^a^9^8^7^6^5^4^3^2?1F@2$7@1$0#k0+ttrp4?2fc@1$4@1$1@1$0#k0^h6@1$c$h0").

Definition rNSUCC_stmt : ltac2:(zQ "00P") := ltac2:(zQ "j82!h9!oa!jma!s9!hre!ku7!hqe!ov5!qic!hr5!js6!loe!qj9!s4!m4!ht2!hv2!khe!il8!lia!ip6!jnf!ire!ng3!ig2!qjf!lj4!lp5!hvc!pha!nne!qof!qp6!qq2!pm0!pq5!pvb!qg8!qh6!ika!lo5!kp0!os7!qqd!oua!qr7!qs6!lk2!in2!kp7!qt4!qte!jn1!qu9!jo9!qv2&@2$2@2$2@1$h2^h4@3$c$4$3^h5+h0&@2$2~0@2$a@1$8@2$7^i0^h6^hf>3st1$e>3st2$e>2mm$6>4cnt1$3>3st3$e>3idx$3>2m4$5>3m''$5>2s'$h3>3s''$h3>6errv''@1$1@1$0#k0>4junk@1$ha@1$1@1$0#8>2oo$5>2o3$5>2g3$6>2b3$6>2r3$9>3t0'@1$1@1$0#k0>3t1'@1$1@1$0#k0>3t2'@1$1@1$0#k0>3a1'@1$1@1$0#k0>3a2'@1$1@1$0#k0>3a3'@1$1@1$0#k0>3a4'@1$1@1$0#k0>3a5'@1$1@1$0#k0>3a6'@1$1@1$0#k0>3a7'@1$1@1$0#k0>3t3'@1$1@1$0#k0>3t4'@1$1@1$0#k0>3t5'@1$1@1$0#k0>3t6'@1$1@1$0#k0>0@e$i4^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2>0@2$h4Z^hb>0@3$d$if@2$ia^hd@2$h1?2sc^he@2$h8$6^h3>0@6$i1^he^h4^h3^h2^hd@2$he?2sc^hf>0>1a$3>0@2$hc@2$h4@2$b~1+4^1@2$j4^1@2$b@2$2~1@1$8@2$7^i0^h6+4@5$i7?3st0^i1?2lo@2$b@2$j6@1$0#k0?2sp+p0^2>0>0@3$d@4$h6$4$h0$f$9@1$j0?3st0@2$j5@4$h6$4$h0$f$9@4$j7$4$h0$f$9@3$d$3@5$hf$5$i0?1o^i1@4$hb$4$3@3$h9$4$3^h6@2$2@2$2@3$c$4$3^h6@2$2+h0@2$a@1$8@2$7^i1^h7^i0-3Z@7$i6?5HCEIL?1R?1o@9$ib?1R$ic@3$j3^i3@1$idZ@6$ie^i1^h7^i0@2$h1?2sc^i2@2$a$i9@1$j1?2sc^i2?2sc^i3@3$j2^i1^h7^i0^i2@2$b^i2+1@4$hd?1R?2sc?1k?4bail^hc?1Q@7$i2@h2$i5^i4^i3^i2@2$h5@1$0#k0^i0^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7?1F@2$h5@1$0#k0+ttri0?2fc@1$h7@1$1@1$0#k0^he@1$i3$i8").
End LEVEL.

End HCW.

