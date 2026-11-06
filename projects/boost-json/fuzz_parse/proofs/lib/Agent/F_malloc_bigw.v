(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z25stdpp9countablehcbZ_countable35stdpp7numbers1Zjb6eq_dec37Corelib4Init9Datatypesl54list37Corelib4Init5Logicn42eq04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~p3aunmap_seqsp35zeros79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ua4mctxua6mstateuah1set_unmap_seq_mapua7upd_ctx25stdpp4basehl75empty35stdpp9bitvectorbdefinitionshmc2bv25stdpp4gmaphof4gmaphofagmap_empty46Stdlib6ZArith6BinInt1Zhr13addua2IBua4UNIThr13divhr14landhr13powhr13sub01Nua4metal54Noneua4aptrl54Somel54pairl54prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_bigw~~~~~~ii66big_mlua6mkMetaua8put_metaii68big_metaii69big_metaAua9hdr_havocua9put_groupuah0set_mmap_countern43andhr12lehr12ltua6shadowl53fstl53sndhcbN_countable35stdpp7numbers1Njg46eq_decl56optionn42exua7Unknownua9cell_readua7cellvaluaaget_shadowua8s_shadowhr16modulohl76lookuphofbgmap_lookupp39meta_word" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Lemma unmap_seqs_empty : ltac2:(zQ "h00!h9!id!kc!md!o8!od!t5!u2!hi8!hif!hj8!hkd!hm3!ho9!hpb!hq3>2st$9@3$4@1$3@1$d@1$5#8@1$6@2$b\1c$8@2$a@2$c@4$e$0$2$1$0@4$f$0$2$1$0^1^1@1$7Ni0").
Proof. intros st. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require StrFun.

Definition big_ml : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "80!hs9!h9!ht0!ht5!htc!hu3!hub!hv2\1n$1@2$5@2$4@2$0@2$0@2$0^1$2$3+vvf+hgg0@2$7@2$6+2+j4+1").
Definition big_meta : ltac2:(zQ "30!hv9!h9!hvc>3rid$0>1n$1$2") := ltac2:(zQ "90!hv9!h9!ig3!iga!ih1!ih8!ihf!imc!in6\3rid$0\1n$1@9$8@1$2$3@1$2$3@2$4@2$6$0$1@4$5$0$1^2ZZZZ+1+jf@1$7^1").
Definition big_metaA : ltac2:(zQ "20!hv9!hvc>3rid$0$1") := ltac2:(zQ "80!hv9!ig3!h9!iga!ih1!ih8!ihf!in6\3rid$0@9$7@1$1$3@1$1$3@2$4@2$6$0$2@4$5$0$2^1ZZZZZZZ").
(* [comment removed for export] *)
Definition big_st : ltac2:(zQ "40!h9!hif!hv9!iga>2st$1>1g$3>3rid$2>1n$0>1v$0$1") := ltac2:(zQ "d0!h9!hv9!ih8!iga!inf!ih1!ioa!ip6!iq3!hif!iqf!irb!hkd\2st$9\1g$3\3rid$1\1n$0\1v$0@2$c@1$b^1@3$4^4@2$6^3^2@4$a@4$2$1$0^3Z@2$5$3^4Z@2$8@4$2$1$0^3Z@3$4^4@1$7^3^5").

Lemma big_ml_eq : ltac2:(zQ "90!h9!isf!o8!imc!hs9!htc!it5!itb!hub>1n$0>0@2$1@2$6Z^1@2$7^1@2$8+2+i0@3$2$0@1$3^2@2$5@2$4^2+hgh3+hgg0").
Proof. intros n.
  intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_fresh : ltac2:(zQ "hb0!h9!hv9!iu1!o8!iua!iv0!iv6!jh5!ig3!jhf!ihf!isf!ji8!jid!jj7!jk3!jkd!iq3!hif!jla!hs9!it5!itb!jm5!jmf!hpb!jn9>2st$h2>1b@2$a$1$0>1o$0>0@3$3@1$9$2@6$h8$1$2@4$h9$1$7$6$2@4$ha$1$7$6$2@3$4$1$0^2@1$h3^3@1$8$2>0@3$3$0@2$h7@3$5$1$0^3+h0Z>0@2$b@2$h5Z^3@2$h6^3+c@2$c$0\1h$0@3$3$f@2$e@2$h0@2$h1^6^7@3$4$1$0^6@2$h4@3$5$1$0^6^5@1$d^1").
Proof.
  intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.

Lemma meta_word_big_range : ltac2:(zQ "80!isf!ioa!jo8!it5!itb!hub!hv9!h9>3rid$6>1n$7>0@2$0@2$3Z^1@2$4^1@2$5+2+i0@2$0@2$3Z@1$2@2$1^3^2@2$4@1$2@2$1^3^2@2$5+2+k0").
Proof. intros rid n.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  Z.div_mod_to_equations. lia.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.
End SUCC.
(* [comment removed for export] *)
