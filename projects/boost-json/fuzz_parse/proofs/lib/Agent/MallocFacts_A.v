(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocBlocks MallocHINV.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc4meta01N37Corelib4Init9Datatypesm44prod46Stdlib6ZArith6BinInt1Zo33addm42idm44pairm43snd02N0hc4UNIThcaget_stridehc5m_memo33mul25stdpp6optiont9bfrom_optionhc6mstate37Corelib4Init5Logicve3andhc3ctxo32leo32ltve2eqhc7bounceshcbc_init_donehcec_mmap_counterhc8c_secrethc5c_seqhc9unmap_seqo33powve2orhc4aptrhccget_meta_rechc4optrm44Nonem44Someve3nothc6activehcbm_sizeclasshc6regionhcam_last_idx35stdpp7numbers1Nhte6eq_dechc4ghdrhc7m_availhc8m_maplen25stdpp9countableih5bN_countable35stdpp7numbers1Zij56eq_decm44boolm46optionm44trueve2exhc7m_freedo36moduloo37testbit25stdpp4baseio96lookupih5bZ_countableih5eprod_countable25stdpp9decidableis0bprod_eq_dec25stdpp4gmapiu04gmapiu0bgmap_lookupm43fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_A~~~~~~jg99sstart_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~jlc9meta_slothc7RKGrouphcam_freeablehc6mkGhdrhc6r_kindhc5r_lenhc5rkindhcbround_up_pghc8s_groupshc9s_regionshcasize_classm44list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~khd5blockkhd8blk_addrhc2IBhc6r_baseo33subkhd8blk_sizekhd8blk_slot36Stdlib5Lists4Listkq32Inhc5usageo34landhc7s_slotshc6shadowhcas_next_rid79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~kub7ptrs_inhc8s_shadow46Stdlib6NArith6BinNat1Nlk42lelk42lthc7Unknownhc9cell_readhc7cellvalhcaget_shadowhc4cptrhc5Knownhc7r_cellshc6s_tick" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record block_ok (st : mstate) (b : block) : Prop := mkBO {
  (* [comment removed for export] *)
  bo_slot : exists g idx, (s_slots st) !! (blk_slot b) = Some (g, idx)
            /\ Z.testbit (m_avail (get_meta_rec st g)) idx = false
            /\ Z.testbit (m_freed (get_meta_rec st g)) idx = false
            /\ 0 <= idx <= m_last_idx (get_meta_rec st g)
            (* [comment removed for export] *)
            /\ (exists off, 0 <= off /\ blk_addr b = conc st (blk_slot b) + UNIT * off
                           /\ UNIT * off + blk_size b <= get_stride (get_meta_rec st g) - IB);
  (* [comment removed for export] *)
  bo_region : exists r, (s_regions st) !! (fst (blk_slot b)) = Some r /\ r_kind r = RKGroup;
  bo_size : 0 <= blk_size b
}.

(* [comment removed for export] *)

Definition sstart_of : ltac2:(zQ "20!h9!la>2mr$1>1i$0$0") := ltac2:(zQ "e0!h9!m1!nc!pb!q1!q6!qd!r3!r7!re!sb!la!t3!u7\2mr$b\1i$0@2$3@2$3@3$6$1$0@5$d@2$2$1$0@2$2$1$0@1$4@2$2$1$0@4$5$1$0$7Z@1$a^2$8@2$c@1$9^2^1").

Definition fact_ctx : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "f0!hh2!hh8!hhe!hi3!h9!hi8!hid!hj7!hk5!hl6!hm1!hm9!hn5!hnb!v5\2cs$e@2$0@2$0@2$2Z@1$8@1$1^1@2$3@1$8@1$1^1@2$c+2+i0@2$0@2$0@2$2Z@1$9@1$1^1@2$3@1$9@1$1^1@2$c+2+k0@2$0@2$d@3$5$4@1$7@1$1^1Z@3$5$4@1$7@1$1^1+1@2$0@2$0@2$2Z@1$a@1$1^1@2$3@1$a@1$1^1+hg0@2$0>1i$4@2$0@2$2Z@2$6^2^1@2$3@2$6^2^1+hg0>1i$4@2$0@2$2Z@2$b^2^1@2$3@2$b^2^1+hg0").

Definition fact_active : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "f0!hh2!hi8!ho0!h9!ho7!hp6!hpd!hq4!hqb!hr1!sb!hra!v5!hhe!hi3\2cs$c>2sc$3>1g$2>0@3$1$5@2$9^3^2@2$7$2^1@2$0@2$0@2$dZ^3@2$e^3+j0@2$0@3$1$3@1$b@2$4^4^2^3@1$8@3$1$5@1$a@2$4^4^2@1$6$2").

Definition fact_gmeta : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "j70!hh2!h9!hhe!hi8!m1!hi3!ho0!hra!hs8!ht1!huf!re!hv9!hn5!hq4!ig0!iga!ii6!ik6!r7!il0!il7!qd!im0!im7!ho7!imc!pb!in6!t3!inf!ip5!ipf!iqe!it1!iuc!iv4!jg3!hnb!jkf!jpe!jqb!jr5!sb!la!js2!v5!hp6!jsb!jt4!jtc!ju4!jv2!jvd!kg9\2cs$ie>1g$6>1b$6>0@3$3$if@1$ib@2$h9^3^2@2$e$6^1=2mr$ic@2$h9^4^3@2$0@2$i8^5^4@2$0@2$0@2$2Z@1$f^1@2$5@1$f^1@2$d+2+i0@2$0@2$0@2$2Z@1$ha^1@2$5@1$ha^1@2$d+2+i0@2$0@2$0@2$2Z@1$9^1@2$2@1$9^1+hf@2$0@3$3$1@1$ia^1+1@2$0@2$i6@2$0@2$0@2$2Z@1$7^1@2$5@1$7^1+j0@2$0@2$2Z@1$h0^1@2$5@1$h0^1@2$d+2+h3@2$0@3$3$1@1$7^1+jf@2$0@3$3$1@1$9^1Z@2$5Z@1$h0^1@2$0@2$2Z@1$h0^1@2$0@2$h8$1\2ai$1@2$0@3$3@1$h5$c@6$hf$6$c@4$i3$6@4$i2$4$a$1$h2@6$i1$4$a$h1$1$h2$i0$c@4$i4$6@4$i2$4$a$1$h2@6$i1$4$a$h1$1$h2$i0$c^4@1$j4^6@2$e$c@2$id@2$e$6^5^1@2$0@2$0@2$2Z^1@2$2^1@1$9^2>1i$1>0@2$2Z^1>0@3$3$h4@2$he@1$f^4^2$h7@2$2^3^4@2$0@2$h8$8\1r$8@2$0@3$3@1$h5$8@6$hf$4$8@4$i3$4$a$h1$8@4$i4$4$a$h1$8@3$i5$4$1^4@1$j5^6@2$e$8^1@2$0@3$3$j2@1$j0^1$i9@2$0@2$2Z@3$h6$4$1^4@2$0@3$3$1@2$hc@3$h6$4$1^4+h0Z@2$2@2$i7^2@2$hb@1$9^2+1@1$j3@1$j1^1@2$0@2$2$h3@1$b^1@2$0@3$3$1@2$hc@1$b^1$h3Z@2$0>0@2$5@1$7^1+j0@2$5@1$b^2@2$d+2+hf@2$0>0@2$5@1$7^1+j0>1i$1>0@2$2Z^1>0@3$3$h4@2$he@1$f^4^2$h7@2$2@2$hd$h3@1$j6@1$7^5@1$b^5>0@2$5@1$7^1+j0@2$5@2$hd@1$b^2@2$hb@1$9^2+1@2$d+2+h4").

Definition fact_avail_clear : ltac2:(zQ "30!kh6!km2!v5>2cs$2>2LB@1$0$1P") := ltac2:(zQ "if0!m1!h9!hs8!hi8!hv9!huf!jg3!ho0!pb!hhe!ii6!ik6!hq4!km2!ho7!il7!nc!qd!hh2!hnb!kmb!jkf!kn7!knc!ko5!ip5!ipf!iqe!it1!iuc!iv4!il0!kh6!im0!im7!kob!kp7!re!ig0!sb!la!v5!hp6!jv2!jvd!kr6!inf\2cs$i9\2LB@1$i0$d>1g$7>1b$7>1i$1>0@3$3$ia@1$i7@2$e^5^3@2$c$7^2>0@2$9Z^2>0@3$3$hf@2$ie@1$i6@2$e^7^5^3$i1=2mr$i8@2$e^8^6=2lo$1@2$h8@2$h5^1^5$h6=2hi$1@2$h8@2$8@2$h5^2^6@1$i5^2$h6@2$h2>2b'@2$h0$0$1>2gh$4>0@3$3@1$f$4@6$h9@2$h0$0$1$4@4$hd$7@4$hc$0$5$1$b@6$hb$0$5$a$1$b$ha$4@4$he$7@4$hc$0$5$1$b@6$hb$0$5$a$1$b$ha$4^2@1$ib^d@2$c$4^1>0@3$3$0@3$6$0$1^3@3$6$0$1^b@2$h3@2$9@2$8@3$h1$0$1^4+9^6@2$9^5@3$h1$0$1^4>3blk$d>0@3$id$d^1^b>0@3$3$0@3$6$0$1@1$i4^2@3$6$0$1^a@2$i2$2\1r$2@2$h2@3$3@1$f$2@6$h9$0$2@4$hd$0$5$a$2@4$he$0$5$a$2@3$6$0$1^c@1$ic^f@2$c$2^1@2$h3@2$9@2$8@1$h4^4@1$i3^4@2$8@1$h7^1^6@2$9@2$8@1$h7^1^5@1$h4^4").

(* [comment removed for export] *)
Definition fact_free_clear : ltac2:(zQ "30!kh6!km2!v5>2cs$2>2LB@1$0$1P") := ltac2:(zQ "j00!m1!h9!hi8!hs8!hv9!huf!jg3!ho0!pb!hhe!ho7!ii6!ik6!hq4!hnb!km2!il0!il7!nc!qd!im0!hh2!kmb!jkf!kn7!knc!ko5!inf!ip5!ipf!iqe!it1!iuc!iv4!kh6!im7!kob!kp7!re!ig0!imc!sb!la!v5!hp6!jv2!jvd!kr6\2cs$ib\2LB@1$i2$f>1g$7>1b$7>1i$1>0@3$2$ic@1$i9@2$a^5^3@2$d$7^2>0@2$9Z^2>0@2$e@3$2$h0@2$hb@1$i7@2$a^7^5^3$h4@3$2$h0@2$hb@1$i8@2$a^7^5^3$h4=2mr$ia@2$a^8^6=2lo$1@2$ha@2$h7^1^5$h8=2hi$1@2$ha@2$8@2$h7^2^6@1$i6^2$h8@2$h5>2b'@2$h2$0$1>2gh$4>0@3$2@1$h1$4@6$hc@2$h2$0$1$4@4$i0$7@4$hf$0$5$1$c@6$he$0$5$b$1$c$hd$4@4$i1$7@4$hf$0$5$1$c@6$he$0$5$b$1$c$hd$4^2@1$id^d@2$d$4^1>0@3$2$0@3$6$0$1^3@3$6$0$1^b@2$e@2$9@2$8@3$h3$0$1^4+9^6@2$9^5@3$h3$0$1^4>3blk$f>0@3$if$f^1^b>0@3$2$0@3$6$0$1@1$i5^2@3$6$0$1^a@2$i3$3\1r$3@2$h5@3$2@1$h1$3@6$hc$0$3@4$i0$0$5$b$3@4$i1$0$5$b$3@3$6$0$1^c@1$ie^f@2$d$3^1@2$e@2$9@2$8@1$h6^4@1$i4^4@2$8@1$h9^1^6@2$9@2$8@1$h9^1^5@1$h6^4").

(* [comment removed for export] *)
Definition fact_hdr_clear : ltac2:(zQ "30!kh6!km2!v5>2cs$2>2LB@1$0$1P") := ltac2:(zQ "i10!m1!h9!hv9!hs8!huf!pb!ii6!ik6!jg3!hi8!km2!hq4!il7!nc!qd!kmb!ho0!knc!hhe!ip5!ipf!iqe!it1!iuc!iv4!kh6!hnb!kob!kp7!v5!jv2!jvd!kr6\2cs$hd\2LB@1$h9$a>1b@2$d$0$1>2gh$2>3blk$a>1r$3>0@3$9@1$c$2@6$h3@2$d$0$1$2@4$h7$h0@4$h6$0$4$1$7@6$h5$0$4$6$1$7$h4$2@4$h8$h0@4$h6$0$4$1$7@6$h5$0$4$6$1$7$h4$2^4@1$he^6@2$b$2^3>0@3$i0$a^3^6>0@3$9$0@3$8$0$1@1$hc^4@3$8$0$1^6>0@3$9@1$c$3@6$h3$0$3@4$h7$0$4$6$3@4$h8$0$4$6$3@3$8$0$1^7@1$hf^9@2$b$3^4@2$ha@2$h2@2$5@1$f^6@1$hb^6@2$5@1$h1^5@3$e$0$1^8@2$h2@2$5@2$5@1$h1^5@3$e$0$1^8+h0@1$f^6").

(* [comment removed for export] *)
Definition fact_usage : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "70!krc!hh2!h9!v5!hhe!hi3!hn5\2cs$3>1i$2@2$1@2$4Z@2$0^2^1@2$5@2$0^2^1@2$6+2+jc").

(* [comment removed for export] *)
Definition fact_masks : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "h20!hi8!hhe!h9!ho0!il0!im0!hh2!ho7!ig0!imc!ht1!inf!hq4!sb!la!v5!hp6!ks4\2cs$f>1g$3>1b$3>0@3$0$h0@1$d@2$7^3^2@2$c$3^1=2mr$e@2$7^4^3@2$6>1i$2>0@2$1Z^1>0@3$0$4@2$b@1$8^3^2$5@2$1^3@1$a^4@2$6>1i$2>0@2$1Z^1>0@3$0$4@2$b@1$9^3^2$5@2$1^3@1$a^4@3$0$2@2$h1@1$8^1@1$9^1Z").

(* [comment removed for export] *)
Definition fact_maplen : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "a0!ho0!ho7!hq4!hi8!iga!sb!v5!hp6!hi3!hn5\2cs$6>1g$0>1b$0>0@3$3$7@1$5@2$1^3^2@2$2$0^1@2$8@1$4@2$1^4^3@2$9+2+i8").

(* [comment removed for export] *)
Definition fact_slots : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "hd0!h9!ho0!m1!nc!hh2!hi8!huf!ik6!ho7!hq4!jg3!hhe!ii6!ipf!iqe!it1!il7!q6!qd!im7!jkf!ht1!sb!v5!hp6!ksb!ip5!iuc!iv4\2cs$h7>1p@2$3$2$0>1g$1>3idx$0>0@3$5@1$h0@2$3$1$0@6$ha@2$3$2$0@2$3$1$0@4$hb$1@4$f$2$6$0$7@6$e$2$6$c$0$7$d@2$3$1$0@4$hc$1@4$f$2$6$0$7@6$e$2$6$c$0$7$d@2$3$1$0^3@1$h9^4@2$9@2$3$1$0@4$h1$1$0^2^1@2$h3$1\1b$1@2$4@3$5$h8@1$h6@2$8^6^4@2$9$1^1@2$4@3$5$2@3$a$2$0^5@3$a$2$0^1@2$4@3$5$0@3$h2$2$0^5@2$h4@2$8^6^4^3@2$4@2$bZ^3@2$b^3@1$h5@2$8^6^4").

(* [comment removed for export] *)
Definition fact_slots_complete : ltac2:(zQ "10!v5>2cs$0P") := ltac2:(zQ "hb0!h9!ho0!m1!nc!huf!ik6!ho7!hq4!q6!hi8!hhe!ii6!ipf!iqe!it1!jg3!il7!hh2!jkf!ht1!sb!v5!hp6!ksb!ip5!iuc!iv4\2cs$h5>1g$1>1b$1>1i$0>0@3$9$h6@1$h4@2$6^4^3@2$7$1^2>0@2$h1@2$aZ^2@2$a^2@1$h3@2$6^5^4@3$9@1$h0@2$3$1$0@6$h8@2$3$2$0@2$3$1$0@4$h9$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$3$1$0@4$ha$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$3$1$0@4$8$2$0@3$f$2$0^4@2$h2@2$6^6^5^3@1$h7^6@2$7@2$3$1$0@4$8$1$0^5^3").

(* [comment removed for export] *)
Definition fact_ptrs : ltac2:(zQ "10!v5>2st$0P") := ltac2:(zQ "h30!m1!hs8!kt5!ii6!huf!hpd!il7!hh2!hi8!kte!ip5!iuc!iv4!lie!v5!jvd!lj9!llc!lm2\2st$e@2$7@2$d\3rid$0@2$h2^1@1$9^2^1>3rid$0>0@2$h1@1$9^2^1@2$7@3$8@1$6$1@6$a$0$1@4$b$0$4$3$1@4$c$0$4$3$1^2@1$f^3@1$5$1@3$8@1$6$2@6$a$0$2@4$b$0$4$3$2@4$c$0$4$3$2^2@1$h0^3@1$5$2").

(* [comment removed for export] *)
Definition fact_blk_unknown : ltac2:(zQ "30!kh6!km2!v5>2st$2>2LB@1$0$1P") := ltac2:(zQ "hf0!hs8!m1!h9!km2!jg3!hi8!kmb!kp7!ii6!huf!hq4!kh6!il7!hh2!im7!kob!lm8!ln2!lne!lo8!v5!knc!jvd!kr6!pb!hhe!hi3!ko5!ip5!iuc!iv4\2st$h4\2LB@1$b$3>3blk$3>1r$0>0@3$h7$3^2^3>0@3$5@1$c$0@6$hc$1$0@4$hd$1$9$8$0@4$he$1$9$8$0@3$4$1$2@1$7^3@1$h6^5@2$a$0^2>1a$2>0@2$d@2$h9@1$6^5^1@2$ha^1@2$h8@1$6^5@1$f^5@2$e$2\1h$2@3$5$h2@2$h1@2$h3^9@3$4$1$2@1$7^7@2$hb^3@1$h5^6@1$h0^1").

(* [comment removed for export] *)
Definition fact_blocks_disjoint : ltac2:(zQ "30!kh6!km2!v5>2st$2>2LB@1$0$1P") := ltac2:(zQ "h00!km2!kmb!kp7!m1!jg3!hi8!h9!kob!kr6!pb!hhe!kh6!hqb!hnb!lp5!v5\2st$f\2LB@1$b$0>2b1$0>2b2$0>0@3$8$0^2^3>0@3$8$0^2^4>0@3$5$3@3$4$3$6@1$2^4@3$4$3$6@1$2^3>0@1$c@3$5$e@1$2^5@1$2^4@2$d@2$a@2$9@1$1^6@1$7^6@1$1^5@2$a@2$9@1$1^5@1$7^5@1$1^6").

(* [comment removed for export] *)
Definition fact_hdr0 : ltac2:(zQ "10!v5>2st$0P") := ltac2:(zQ "h50!ho0!ho7!hi8!h9!hhe!hq4!jg3!hh2!m1!jkf!kn7!lpc!ln2!lne!lo8!ht1!sb!v5!hp6!pb!ko5\2st$h1>1g$0>1b$0>1i$3>0@3$2$h2@1$h0@2$1^4^3@2$5$0^2>0@2$7@2$4Z^2@2$4^2@2$h3@1$f@2$1^5^4+1@3$2$d@2$c@2$e^6@3$6$8$3^4@2$h4@2$9@2$1^6^5^3$a@1$bZ").

(* [comment removed for export] *)
Definition fact_cell_ticks : ltac2:(zQ "10!v5>2st$0P") := ltac2:(zQ "h40!m1!h9!kt5!nc!hq4!il7!hi8!ip5!ii6!ipf!iuc!iv4!huf!ik6!q6!v5!lq4!lj9!lqe!llc\2st$f>3rid$0>2sh$2>1o$1>1v$1>1t$0>0@3$6@1$5$2@6$7$0$2@4$a$0$c$8$2@4$b$0$c$8$2^5@1$h1^6@2$4$2^4>0@3$6@1$5@2$3$1$0@6$7$1@2$3$1$0@4$a$1$d$9@2$3$1$0@4$b$1$d$9@2$3$1$0^4@1$h0^5@2$4@2$3$1$0@4$e$1$0^3^2@2$h3^3@1$h2^8").

(* [comment removed for export] *)
(* [comment removed for export] *)
Record MFACTS_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkMF {
  mf_blocks : Forall (block_ok st) LB;
  (* [comment removed for export] *)
  mf_nodup : List.NoDup (map blk_slot LB);
  (* [comment removed for export] *)
  mf_ticks : ticks_ok st;
  (* [comment removed for export] *)
  mf_reserved : s_reserved st = resv;
  mf_ctx : fact_ctx (strip st);
  mf_active : fact_active (strip st);
  mf_gmeta : fact_gmeta (strip st);
  mf_avail_clear : fact_avail_clear (strip st) LB;
  mf_hdr0 : fact_hdr0 st;
  (* [comment removed for export] *)
  mf_free_clear : fact_free_clear (strip st) LB;
  mf_hdr_clear : fact_hdr_clear (strip st) LB;
  mf_usage : fact_usage (strip st);
  mf_masks : fact_masks (strip st);
  mf_maplen : fact_maplen (strip st);
  mf_slots : fact_slots (strip st);
  mf_slots_complete : fact_slots_complete (strip st);
  (* [comment removed for export] *)
  mf_ptrs : fact_ptrs st;
  mf_blk_unknown : fact_blk_unknown st LB;
  mf_blocks_disjoint : fact_blocks_disjoint st LB;
  (* [comment removed for export] *)
  mf_cell_ticks : fact_cell_ticks st
}.

(* [comment removed for export] *)
Notation MFACTS := (@MFACTS_g agent_reserved).


(* [comment removed for export] *)
