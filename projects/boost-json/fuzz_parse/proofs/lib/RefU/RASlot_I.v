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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W1 ASlot_I.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstate37Corelib4Init9Datatypesm33nat37Corelib4Init5Logico13and46Stdlib6ZArith6BinInt1Zpb2lem34list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~rf5blockpb2lto12ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~hh64ALLChh69ENTRY_RELrfbAREACH_from79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~hn93IST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~hs7cref_reservedhcasize_classpb3addpb3mulpb3pow04Npos35stdpp9bitvectorbdefinitionsije2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~im13mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~iqb6PState3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiv1dmachine_state3h5LinuxProcessSemantics5Riscv7Preludejj95bvmapo12eq01Nhc4aptrhc6regionijebbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~jof5rsegshccget_meta_rechcaget_stridem33snd25stdpp9countablejv7bN_countable35stdpp7numbers1Nkh76eq_decm36option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kjb4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMalloc_fp~~~~~~knfarmalloc_fphcec_mmap_counterhc3ctxhc6r_baseiqb5ps_faiqb4ps_miqb5ps_sopb3sub25stdpp4gmaplgf4gmapm34Nonem34Somem34consm33fstm33nilm34pairm34prodm34unito12orhh67as_inv279OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~lm93rdv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~lra8ticks_okim1bbrk_link_psim18pans_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~mi34mrelmi37slot_okmi39unk_agreekjb2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mob3mkRmob3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mt52MSmt56ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ni27mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nm77seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nr18rw_cellshs75rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~og18rauxv_okog1crpres_excepthc6activehc4optrhc9s_regions25stdpp4baseonc5emptyije7Z_to_bvlgfagmap_emptyog16rimplThc1M69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~or85hceil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8RASlot_I3HCW~~~~~~ovc9ras_post2ovc8ras_pre279OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh0RAllocSlot_iface~~~~~~pl99RAS_STACKhs74RATPhs7h1ralloc_slot_entryhcaalloc_slothc8full_lay79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~pu52bSpu52kSim17leaf_ofovch1ralloc_slot_stmt2hcaalloc_metahs7h1ralloc_meta_entryog19RAM_STACKog1h0ralloc_meta_stmtog18ram_post" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof. try hcb. try hsb.
  intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof. try hcb. try hsb.
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 : ltac2:(zQ "30!h9!la!nb>3st0$1>2st$1>2sc$0>3req$0>4fuel$2P") := ltac2:(zQ "h20!p5!r3!r8!h9!hg4!la!hgc!nb!hh1!hl6!hle!hmb!hs0!ig9!ih9!ii6!iic!ij2\3st0$5\2st$5\2sc$3\3req$3\4fuel$7@2$0@2$8@1$2$4\2LB@1$2$4@2$0@4$b?4HSEC@1$d?5HCEIL^6^1@2$c^6^5@2$0@2$a^5^4@2$0@1$9^4@2$0@2$0@2$1Z^3@2$6^3+j0@2$0@2$0@2$1Z^2@2$6^2@2$h1+2+i0@2$1@2$f^2+4@2$h0+h0@1$e^3").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post2 : ltac2:(zQ "80!ij8!ilb!h9!la!iq4!iu7!ji8!jlf>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1o$4>1m$4>3st0$3>2st$3>1s$5>2lo$2>2sc$2>3req$2>3st1$3>3idx$2>2s'$5>0$6P") := ltac2:(zQ "k73!ij8!ilb!p5!hh1!h9!ii6!jm8!jmd!jn0!jn7!jo0!jsc!jt5!ju4!la!jv1!iq4!r3!iic!kg8!ki8!kj2!ji8!kn7!ks1!ksf!ku0!ku6!iu7!kuf!kv8!lg0!hgc!lg9!lhb!li3!lia!lj1!lj8!lje!lk4!lkb!ll2!ll9!jlf!lle!lr3!lvc!mg8!mh7!mm5!mmd!mn8!mo5!ms7!mse!nh2!nh8!nlc!nq6!nuc!nv8!ok4!ol0!om0!om9!on0!ij2!oo8!op1!opc&>0@1$1@1$0#k0@1$h5@1$1@1$0#8&@2$5@2$5@1$hb^2@3$f$7$4^3+h0&@2$5~1@2$h2@1$d@2$c^h8^4^h7\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$ic@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1o$h0\1m$h0\3st0$e\2st$e\1s$hc\2lo$4\2sc$4\3req$4\3st1$e\3idx$4\2s'$hc\3ms'$h6@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$3@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2@3$6$h6^h1@7$j8@hf$j6^ie^id^ic^ib^h0^f^e^ia^i9@2$k5@1$0#k0^h3^d^c^b^a^9^8^7^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^6^5^4^3^he@1$j9^ie^hd@1$i3@1$1@1$0#k0^2@1$jb$b@2$2@2$ja$b^2@2$2@4$j7$b^2^h7@2$a@1$0#k0^id@2$2@4$jc$b^2@2$5@2$a@1$0#k0^ib-q4@3$i5$h7@1$j5^1@1$i7$h7@2$2@4$je?5HCEIL?4HSEC^2@2$a@1$0#k0^id@2$2@4$jd?5HCEIL?4HSEC^h4^2@2$2@1$if^h4@2$2@3$j4^h4^hc^2@2$2@3$jf@4$h8^ha^h4^h7@2$a@1$0#k0^id^hb^2@2$2@2$j2^h9^h4@2$2@2$j0^h4^h2@2$2@3$6$e@1$he^h2@1$he^h8@2$2@3$6@2$i9$4$4@1$hd^h2@1$hd^h8@2$2@3$6$ia@1$hf^h2@1$hf^h8@2$2@5$id^ha^h9^h4^h6^h3@2$2@2$2@2$h1Z@1$h9@1$ha^h4@2$i0@1$h9@1$ha^h4@2$k3+2+i0@2$ib@3$6$4^h3-1@2$2@2$h1Z^h3@2$3$8\1g$8@2$3$8\1b$8@2$3$9\1r$9@2$2@3$6$k1@2$k0^h7^h9@2$i4$8^3@2$2@6$j3^h7^3^2^1^h6^h8@2$2>1a$4>0@2$2@2$h1@2$i1~2+4^1@2$i0^1@2$i1@2$5~2@1$d@2$c^h8^4+4@5$h8^hf^h9^hc@2$a@1$0#k0^j2^2>0@3$6@4$i2$7$h4$h3$9@1$k2^hd@2$k4@4$i2$7$h4$h3$9@4$k6$7$h4$h3$9@3$6$4@5$ie$h0$j1^i0^h8@4$i8$7$4@3$i6$7$4^3@2$5@2$5@3$f$7$4^3@2$5+h0@2$h2@1$d@2$c^h8^4^h7-3Z").

Definition ralloc_slot_stmt2 : ltac2:(zQ "10!nb>4fuel$0P") := ltac2:(zQ "ia1!ij8!ilb!h9!jsc!la!op1!jo0!jm8!iu7!ji8!iq4!kn7!oqa!or4!r3!li3!lj1!nb!lje!jlf!lvc!mg8!mn8!ov3!mo5!ms7!mse!nh2!nlc!nq6!nuc!pk0!pkd!pq2!pqf!pr7!nv8!ok4!psd!pta!ii6!lg9&@3$7@1$1@1$0#k0^ib@2$5@1$0#k0^f\4fuel$h1>1RT>1k>0$4>0$2@1$d^3>4bail@1$d^2>1o$a>1s$8>1Q>0^5>0$8>0$9P>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h3@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$a>3st0$4>2st$4>2lo$2>2sc$2>3req$2>4errv@1$1@1$0#k0>0@5$i0^6^5^3^2^if>0@4$i4?5HCEIL?4HSEC^6^8>0@1$h4^7>0@3$h6^8^ie^a>0@2$h5^9^ie>0@4$i5?5HCEIL?4HSEC^c@2$6@1$0#k0^ic>0@4$ha$3^d^a@2$6@1$0#k0^id>0@2$e@1$h7?5HCEIL^b>0@2$e^c@2$i9@2$6@1$0#k0^if@1$i1^b>0@4$he$3^h0@2$i8@2$6@1$0#k0^ie-q4@3$h0$b@1$h8^a@1$h2$b>0@2$hc$3^h1>0@3$7@1$1@1$0#k0^j0@2$5@1$0#k0$i2>0~0>0~0>0>3st1$4>3idx$2>2s'$8>3ms'$9>0@he$hf^ja^j9^j8^j7^j3^j2^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hb^ha^jd^h9^h8^h7^jc^h6^h5^h4^4^3^2^1@7$c?5HCEIL^k1^je@2^k0^5^4^3^jc^2@7$c?5HCEIL^jd^ja@8$i6^jd$i7^je^h4^h2^h1^jc^jb^j9^j8@7$hb@hf$h9^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@2$5@1$0#k0$i3^h7@1$f@1$1@1$0#k0^h6@1$hd$3").

(* [comment removed for export] *)
Lemma ralloc_slot_stmtL : ltac2:(zQ "j21!ij8!ilb!h9!la!lkb!jsc!op1!jo0!jm8!iu7!kj2!ji8!iq4!kn7!oqa!or4!psd!pta!r3!li3!lia!lj1!nb!lje!lk4!jlf!qi7!qid!lvc!mg8!qj3!mn8!ov3!mo5!ms7!mse!nh2!nlc!nq6!nuc!qje!pk0!pkd!pq2!pqf!pr7!nv8!ok4!ii6!lg9&@3$8@1$1@1$0#k0^ib@2$6@1$0#k0^f>4fuel$h6>0@1$i8^1>1RT>1k>0$3>0$2@1$f^3>4bail@1$f^2>1o$c>1s$9>1Q>0^5>0$9>0$bP>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$c>3st0$3>2st$3>2lo$2>2sc$2>3req$2>4errv@1$1@1$0#k0>0@5$ia^6^5^3^2^j0>0@4$ie?5HCEIL?4HSEC^6^8>0@1$hc^7>0@3$hf^8^ie^a>0@2$hd^9^ie>0@4$if?5HCEIL?4HSEC^c@2$7@1$0#k0^ic>0@4$i3$5^d^a@2$7@1$0#k0^id>0@2$h2@1$i0?5HCEIL^b>0@2$h2^c@2$j1@2$7@1$0#k0^if@1$ib^b>0@4$i7$5^h0@2$j0@2$7@1$0#k0^ie-q4@3$h5$d@1$i1^a@1$h7$d>0@2$i5$5^h1>0@3$8@1$1@1$0#k0^j0@2$6@1$0#k0$ic>0~0>0~0>0>3st1$3>3idx$2>2s'$9>3ms'$b>0@he$i9^ja^j9^j8^j7^j3^j2^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hb^ha^jd^h9^h8^h7^jc^h6^h5^h4^4^3^2^1>0@4$he@1$a@2$4$3$2^je@8$h0@1$a@2$4$3$2$h1^k3^h8^h6^h5@2$hb$3$2@1$ha@2$4$3$2@2$h4@2$4$3$2@4$h8$3$2^5^4@7$e?5HCEIL^k2^jf@2^k1^6^5^4^jd^3@7$e?5HCEIL^jd^ja@8$h0^jd$h1^jf^h4^h2^h1^jc^jb^j9^j8@7$i4@hf$i2^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@2$6@1$0#k0$id^h7@1$h3@1$1@1$0#k0^h6@1$i6$5").
Proof. intros fuel. try hcb. try hsb.
  intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

(* [comment removed for export] *)
Lemma ralloc_meta_stmtL : ltac2:(zQ "ie0!ij8!ilb!la!om9!lkb!jsc!jo0!iu7!kj2!ji8!mg8!iq4!kn7!oqa!or4!ql4!r3!op1!li3!lia!lj1!lje!lk4!jm8!h9!jlf!qi7!qid!lvc!qj3!ov3!mo5!ms7!mse!nh2!nlc!nq6!nuc!qm1!nv8!qn7!qo4!qp9!ok4!ii6!lg9>6am_pre>0$2P>0@3$i9?5HCEIL?4HSEC^1>1RT>1k>0$2>0$3@1$e^3>4bail@1$e^2>1o$b>1s$7>1Q>0^5>0$7>0$9P>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$b>2st$2>2lo$h8>4errv@1$1@1$0#k0>0@1^id^3>0@4$i7?5HCEIL?4HSEC^4^5>0@1$hc^5>0@2$a^6^ia>0@4$ib?5HCEIL?4HSEC^8@2$6@1$0#k0^i8>0@4$i1$5^9^7@2$6@1$0#k0^i9>0@2$h0@1$he?5HCEIL^8>0@2$h0^9@2$id@2$6@1$0#k0^ib$i8>0@4$i5$5^c@2$ic@2$6@1$0#k0^ia-q4@3$h4$c@1$hf^9@1$h5$c>0@2$i3$5^d>0@3$h7@1$1@1$0#k0^ic@2$h1@1$0#k0+hgurv8>0>3st1$2>2mo$3>2s'$7>3ms'$9>0@hc$ia?5HCEIL?4HSEC^j4^j3^j2^j1^id^ic^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h5^h4^h2^j6^h1^h3^4^3^2^1>0@2$a^5^3>0@4$hd@1$8@2$4$2$3^j9@4$f@1$8@2$4$2$3^h4@2$hb$2$3@1$ha@2$4$2$3@2$h3@2$4$2$3@4$h6$2$3^6^5@7$d?5HCEIL^jd^ja@2^jc^7^6^5^j8^4@7$d?5HCEIL^j7^j4@4$f^j7^f^j6^j5^j3^j2@7$i2@hf$i0^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2@2$h1@1$0#k0$i6^h1@1$h2@1$1@1$0#k0^h0@1$i4$5").
Proof. intros am_pre. try hcb. try hsb.
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.

End HCW.

(* [comment removed for export] *)
