(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocKit_B.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Z04aptr03bit07m_freed0bm_set_freed04meta08upd_meta46Stdlib6ZArith6BinInt1Zp43lor0bm_set_availp44landp45ldiffk61N37Corelib4Init9Datatypest24prodt26option0cget_meta_rec05m_memt22idt24pairk62N00h0group_active_idx09mask_upto25stdpp6optionhjebfrom_option05lheadt24bool06m_nextt24Some06m_prev08optr_eqb08set_headt24Nonet24negb08get_head0am_set_next0am_set_prev37Corelib4Init5Logichs42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocModel_B~~~~~~hte9clr_linkshte7deq_mid07dequeuehte6act_ofhte6act_st06active09del_group09del_slots0aget_stride0am_last_idxp43add0bm_sizeclass09set_usage05usagep43ltbp43sub" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition aor_st : ltac2:(zQ "30!je!lf!m3>2st$0>1g$2>1i$1$0") := ltac2:(zQ "90!lf!m3!m9!me!n7!o4!je!oa!qc\2st$6\1g$1\1i$0@3$7^2\1r$5@2$4@2$8@1$3^1@1$2^2^1^3").

(* [comment removed for export] *)
Definition act_st : ltac2:(zQ "30!je!lf!m3>2st$0>1a$2>3act$1$0") := ltac2:(zQ "a0!me!lf!m3!r2!n7!o4!je!oa!rf!s6\2st$6\1a$2\3act$1@3$7^2\1r$5@2$3@2$8@1$0^1^2@2$4@2$9@1$0^1^2^1^3").
Definition act_of : ltac2:(zQ "30!lf!m3!je>2st$2>1a$1$0") := ltac2:(zQ "e0!lf!se!ua!m3!v1!va!hg8!hgf!hh4!hhb!hi0!hj3!je!hkc\2st$c\1a$3M4\1x@1$4$3$0@1$6@2$5^2^1\2a0$3@1$b@2$a^3@5$d@2$2$1$0@2$2$1$0@1$7@2$2$1$0@4$8$1$0$9-1@1$6@2$5^3^2Z").

(* [comment removed for export] *)
Definition deq_mid : ltac2:(zQ "30!je!m3!hlb>1h$2>1g$1>2st$0$0") := ltac2:(zQ "h20!m3!je!hm2!v1!hm9!hn1!hn8!ho0!hoa!oa!hp4!hpb!hq2!va!hlb!hqc!hr8!o4\1h$e\1g$0\2st$1=2mr$h1@2$d^1^2M2\0$2$1@1$b@2$7@1$4^1@2$5$0^3=3st1$1M3\1x@1$3$0$1@1$6^1\2pv$0@3$9^1@1$f@1$4^2^3^2=3st2$1M3\1x@1$3$0$1@1$4^2\2nx$0@3$9^1@1$h0@1$6^3^2^1M2\0$2$1@2$7@2$c^1^6@2$5$0^5@3$8^6@1$4^3^1^1@3$8^4@1$a$0^2").
Definition clr_links : ltac2:(zQ "10!o4>1r$0$0") := ltac2:(zQ "50!hp4!m3!hqc!hr8!o4\1r$4@2$3@1$0$1@2$2@1$0$1^1").
Lemma dequeue_mid : ltac2:(zQ "80!je!ht8!ii4!ij1!m3!ijc!hlb!oa>1h$6>1g$4>2st$0@3$1$0@3$5^3^2^1@3$7^2$2@3$3^3^2^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition pd_st : ltac2:(zQ "30!je!hm2!lf>2an$1>3st1$0>2sc$2$0") := ltac2:(zQ "80!hm2!je!v1!m3!lf!ik5!ikf!il9\2an$0\3st1$1\2sc$4M0\2an$0$1^3M2\1x@1$2$3$1@2$7^2^1\1a$3@3$6^3^1@2$5^3^1^2^2").

(* [comment removed for export] *)
Definition grp_del : ltac2:(zQ "20!m3!je>2st$1>1g$0>1p$0$1") := ltac2:(zQ "80!m3!va!im1!imc!in7!io3!je!iof\2st$6\1g$0\1p$0@4$3^1@1$4@2$1^3^2@2$7@1$5@2$1^3^2+1@2$2^1^3").
Definition fg_usage_st : ltac2:(zQ "20!je!m3>2st$0>1g$1$0") := ltac2:(zQ "c0!ip5!hm2!je!m3!va!io3!o4!iq2!iqd!iof!ir4!ira\2st$2\1g$3=2mr$6@2$4^2^1M1\0$1$2@2$a@1$0^1+j0@3$7@1$0^1@2$b@2$8^3@1$0^1@2$9@1$5^1+1^3^3").
