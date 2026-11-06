(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RBand.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~k15rsegshfbbv_unsigned46Stdlib6ZArith6BinInt1Zp33addhf7Z_to_bv37Corelib4Init9Datatypesrb4None37Corelib4Init5Logicta2ex3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsv3dmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hja3mkRhja3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ho42MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~hs77seg_romp32lerb4listrb6optionta3andta2eq01Z3h5LinuxProcessSemantics5Riscv7Preludeij45bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~im35hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~iq73evtho46ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iv37mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jj88rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref9RASlot_W2~~~~~~jnf9rta_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~jscaRSSP_GUARDjsc5rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ki46mstatep33sub" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma ras_ret0 : ltac2:(zQ "he0!h9!jc!nd!o5!qb!r1!t3!ue!hia!hn6!hnd!hs1!ig6!ih1!ih6!ihd!ii6!iic!ij1!ila!ipe!iu2!iu9!jid!jn3!jrf!kgd!khb!km2!kmc>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>2x1@1$1@1$0#k0>3s9v@1$1@1$0#k0>3s8v@1$1@1$0#k0>3s7v@1$1@1$0#k0>3s6v@1$1@1$0#k0>3s5v@1$1@1$0#k0>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0>1F@2$h3@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$f@1$1@1$0#8>4junk@1$e@1$1@1$0#8>3st'$hc>2lo$h2>0@4$hb?5HCEIL?4HSEC^2^4>0@2$h7$2^5>0@4$h8$2^6@2$4@2$3@1$0#k0^j1-p0@d$h9?4HSEC^5^h3^h2^h1^h0^f^e^d^c^b^a^9>0@4$a$2^7^4@2$4@2$3@1$0#k0^j2-p0>0@2$d@1$h4?5HCEIL^5>0@2$d^6@2$hd@2$3@1$0#k0^j4+p0@3$h5$2\3ms'$8@2$7@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$7@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$h0@3$h1$8^3@7$b@hf$9^h0^j8^j7^j6^j5^j4^j3^h1^h2^j0^2^1^id^ic^ib^ia^i9^h3^h4^h5^h6^h7^h8^h9^ha^i1^i0^hf^he^hd^hc^f@1$h6^h0^e@1$6@1$1@1$0#k0^d@1$c$2@4$a$2^d^a@2$3@1$0#k0^j8@7$b@hf$9^h8@2$5@1$0#k0@2$4@2$3@1$0#k0^j5-p0^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4@2$5@1$0#k0$ha^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^c@2$5@1$0#k0+ttvpc^b@1$6@1$1@1$0#k0^a@1$c$2").
Proof. try hcb. try hsb.
  intros until lo. intros MR' MI FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  npose MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling, RSSP_GUARD, rta_frame in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. neexists 2. split; [reflexivity| exact ST].
Qed.

End HCW.

