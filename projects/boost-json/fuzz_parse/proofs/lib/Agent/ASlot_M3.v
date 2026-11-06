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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv4.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "46Stdlib6ZArith6BinInt1Z02le37Corelib7Numbers7BinNumshc1Z37Corelib4Init9Datatypesj93nat37Corelib4Init5Logicl73and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~n19halve_big02lt03powhc4Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~sb3memn16mstate35stdpp9bitvectorbdefinitionshhd2bvj94listn14aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hke6PStatej94prodl72eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~hq05asegsn14optrhhdbbv_unsignedj96optionj94Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ih28rw_cells03add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ile4cellhke5ps_fahke4ps_mhke5ps_soj94Nonej94consj93nilj94pairj94unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~ite4ALLCite9ENTRY_REL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~jj36ta_rel79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W10~~~~~~jne8ag_frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~jsc3ISTjsc7ta_fail79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocNat~~~~~~ki52bSki52kS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~kn39meta_slotkn34mrepkn38ticks_oksb6am_relsb7auxv_oksbbbrk_link_pssb7leaf_ofsbbpres_except79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~lgf9malloc_fplgf9unk_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface~~~~~~lmb6MEDTABlmbcmedtab_cellsile2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lt03stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mh37mem_invn16activen1aalloc_metan1cget_meta_recn14metan15meta0hhd7Z_to_bvkn32wz03muln14UNITn1asize_classite7ag_mmap99OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_M33HCW5LEVEL~~~~~~ms16ag_ctxkn33CTXkn3cSIZE_CLASSESsb5implTlt03mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~njc2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nnf7seg_romn14concn15usageite7ag_nest" s.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma halve_big_pos : ltac2:(zQ "70!h8!j5!l1!mb!qf!rb!rf>1F$2>3cnt$1>2sz$1>0@2$0+1^2>0@2$3@2$0Z^2@2$5^2@2$6+2+h2@2$0+1@3$4^5^4^3").
Proof. intros F.
  induction F as [|F IH]; intros cnt sz Hc Hs; cbn [halve_big]; [lia|].
  destruct (Z.leb_spec (65536 * UNIT) (sz * cnt)) as [LE|GT]; [|lia].
  apply IH; [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. unfold UNIT in LE.
  assert (2 <= cnt) by nia. Z.div_mod_to_equations. lia.
Qed.

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

(* [comment removed for export] *)
Definition ag_ctx : ltac2:(zQ "70!s4!hge!hh4!hja!hk0!hk7!hoa>3st1$2>3st2$2>2mm$5>2m3$1>2s'$6>5errv'@1$3@1$0#k0>1j@1$4@1$3@1$0#8>2oo$1P") := ltac2:(zQ "j70!mb!hh4!s4!hk7!hp4!hpb!hu3!huc!hv3!ig2!igb!ikd!il9!j5!hge!ipa!iq2!iqb!ir3!hja!irc!is3!hk0!isa!it0!it7!jhe!ji6!jn4!js0!kh3!kha!km7!kmd!kr5!ks2!ksa!kt6!ktf!ku9!kv7!lg1!ll1!lle!lr0!lra!lsa!mgc!mkd!ml8!mm1!mme!mnd!mo4!hoa\3st1$1\3st2$1\2mm$3\2m3$e\2s'$j6\5errv'@1$h3@1$2#k0\1j@1$h6@1$h3@1$2#8\2oo$e@2$0@3$hf?2sc?2st^8@2$0@3$hc?2sc?2st^8@2$0@3$5$7@2$j1^8?2sc@1$h4$3@2$0@4$i8@1$9@2$4$1$7^1@4$j2@1$9@2$4$1$7^8@2$i1$1$7@1$i0@2$4$1$7@2$a@2$4$1@1$9$3@4$h8$1@1$9$3^7@2$a$3^6@2$0@2$he?3st0^7@2$0@2$hb?3st0^7@2$0@1$ha^7@2$0@3$i5^8^7@2$a$3^6@2$0@3$5$j4@2$j3^7^6$j5@2$0@2$i2^7^6@2$0@2$i3^7^5@2$0@1$i4^7@2$0@3$ib^7?1o^5@2$0@2$j0$6^5@2$0@4$if$6^5?2lo@2$c@2$8@1$2#k0?2sp-m0@2$0@4$b$6^5@2$c@2$8@1$2#k0?2sp-m0@8$hd?2sc^2?2s4?2s3?2s2?2s1?2s0?2ra@2$0@4$b$6^5@2$c@2$8@1$2#k0?2tp-q4@3$h5$f@1$ie^3@1$h7$f@2$0@2$i6^5@2$8@1$2#k0?2sp@2$0@4$b$6^5$ic$id@2$0@3$i9@4$ia?3st0^7?2lo@2$8@1$2#k0?2sp?1m^5@2$0@2$i7^7^4@2$0@3$5$1@1$h1^4@1$h1?1s@2$0@3$5@2$4$d$d@1$h0^4@1$h0?1s@3$5$h9@1$h2^4@1$h2?1s").

Definition HMM_stmt : ltac2:(zQ "00P") := ltac2:(zQ "he0!s4!moc!mp7!hja!mpd!mq2!mq9!il9!hge!hh4!h8!irc!hk0!mb!j5!mr6!ngc!hu3!nh6!nhd!nid!nj5!nn9!nre!hk7!ns9!nt0!hoa!rb!hv3>3st1$9>3st2$9>2mm$h8>2m3$8>2s'$hb>5errv'@1$3@1$0#k0>1j@1$c@1$3@1$0#8>2oo$8>4cnt1$e>3t0'@1$3@1$0#k0>3t2'@1$3@1$0#k0>3a3'@1$3@1$0#k0>3t4'@1$3@1$0#k0>3t6'@1$3@1$0#k0>0@8$h0^e^d^c^b^a^9^8^7>0@2$d@2$a+1^7@2$a^7+i0>0@2$hc+og0@2$7@2$4@2$4@1$6?2sc$5^8$5@7$h4?5HCEIL?1R?1o@8$f?1R?2sc?3req?1k?4bail^h0^f^9^d?1Q@7$h6@hf$h5@2$1@1$0#k0+hmjvc@2$1@1$0#k0@2$7@2$hd@1$0#k0?2sp-m0?2gp?2tp^8@1$2@2$4@1$6?2sc$5^7@2$1@1$0#k0?2sc@2$1@1$0#k0$h2@1$2+hgg0@1$2@2$4@2$4@1$6?2sc$5^9@1$2@2$ha^h0?2sc^6@2$1@1$0#k0$h3@1$2+og0@1$2^9@2$1@1$0#k0@2$h9^h0^f@2$1@1$0#k0@2$7?2sc+a@1$2@1$6?2sc?2a1?2s5?2s6?2s7?2s8?2s9?3s10?3s11@2$1@1$0#k0@2$7?2sc+ja^5@1$2@2$4+4^9^4?1F@2$1@1$0#k0+hmmk0?2fc@1$b@1$3@1$0#k0^e@1$h7$h1").

Definition HNEST_stmt : ltac2:(zQ "00P") := ltac2:(zQ "hd0!s4!moc!mp7!hja!mpd!mq2!mq9!il9!h8!hge!hh4!irc!hk0!mb!j5!nt8!ngc!hu3!nh6!nhd!nid!nj5!nn9!nre!hk7!ns9!nt0!hoa!hv3>3st1$a>3st2$a>2mm$h8>2m3$9>2s'$hb>5errv'@1$3@1$0#k0>1j@1$c@1$3@1$0#8>2oo$9>4cnt1$e>3t0'@1$3@1$0#k0>3t2'@1$3@1$0#k0>3a3'@1$3@1$0#k0>3t5'@1$3@1$0#k0>3t6'@1$3@1$0#k0>0@8$h0^e^d^c^b^a^9^8^7>0@2$d@2$8+1^7@2$8^7+i0>0@2$8@2$7@2$4@2$4@1$6?2sc$5^8$5+og0@7$h4?5HCEIL?1R?1o@8$f?1R?1f?2sc?1k?4bail^h0^f^9^d?1Q@7$h6@hf$h5@2$1@1$0#k0+hmjvc@2$1@1$0#k0@2$7@2$hc@1$0#k0?2sp-m0?2gp?2tp^8@1$2@2$4@1$6?2sc$5^7@2$1@1$0#k0?2sc@2$1@1$0#k0$h2@1$2+hgg0@1$2@2$4@2$4@1$6?2sc$5^9@1$2@2$ha^h0?2sc^6@2$1@1$0#k0$h3@1$2+og0@1$2^9@2$1@1$0#k0@2$h9^h0^f@2$1@1$0#k0@2$7?2sc+a@1$2@1$6?2sc?2a1?2s5?2s6?2s7?2s8?2s9?3s10?3s11@2$1@1$0#k0@2$7?2sc+ja@1$2^9^5^4?1F@2$1@1$0#k0+hmpl4?2fc@1$b@1$3@1$0#k0^e@1$h7$h1").

Hypothesis HMM : HMM_stmt.
Hypothesis HNEST : HNEST_stmt.
End LEVEL.

End HCW.

