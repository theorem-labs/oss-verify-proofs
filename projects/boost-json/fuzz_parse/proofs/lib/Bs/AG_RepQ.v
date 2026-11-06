(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hc6astatehcdclass_of_addr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocKit~~~~~~n66carvedhc5chunk37Corelib4Init5Logics52eq37Corelib4Init9Datatypeste4Somete6options53ands52exhcbCQuarantinehc9as_chunkshc8ch_statehc6cstatehcafind_chunkhch0kChunkHeaderSize46Stdlib6ZArith6BinInt1Zhm03addte4list36Stdlib5Lists4Listho62Inhc6qbatchhcachunk_listte3apphcdas_n_reservedhcbch_user_beghc7qc_listhm02lehc5as_gqhc6as_sechc5as_tqhc6schunkhc4zlenho65NoDupte6lengthte3nathccch_chunk_beghc6get_pchcaget_regionhch1kChunksBlockCounthc8pc_counthc9qb_chunkshcerg_mapped_user79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AllocWf~~~~~~ioc9qcache_ok46Stdlib5FSetscFMapPositivebPositiveMapit63keyhm02ltte4negbs52or37Corelib5Lists7ListDefjh63maphc8as_cachehc9as_qcachehc7as_qmaxhc7as_qminhcaas_regionshcach_primaryhc4ckeyhcdkMaxCacheSizehcbkNumClasseshch2kQuarantineMaxSizehch2kQuarantineMinSizehc6pclasshc6regionhcasc_map_beg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AG_RepQ~~~~~~ju95xb_okju95xc_okioc8cache_okioch0carved_addr_listioc8chunk_okioc9region_okit64findho66filterho68flat_maphm06modulohm03mulhc8qc_byteste3nils53iffju93WFQju97qboundsioc2WFioc8batch_ok36Stdlib7SortingbPermutationktcbPermutation79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~lg73ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~lkc3memlg74a_stlg7bbatches_replg79chunk_replg79flags_replg76ia_replg78inst_replg7apclass_replg7fregion_junk_replg7aregion_replg7h1region_shadow_replg77sec_replg7athread_rep89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AG_RepQ3HCW~~~~~~mj65ARmemlg74AREPlg79placed_okmj65AREPQlg72FAlg72RBlg74a_rihc9kPageSizehch1rg_allocated_userhch4rg_mapped_free_arraylg7bPCLASS_SIZElg77a_cachelg74a_palkc2shhm03divhcfcompact_to_addrhcaclass_sizehc9pc_chunkshcdrg_free_arrayhm03sublg7cachunk_range79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~nmc5asegslg75afootlg78agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ns55wmono04Npos35stdpp9bitvectorbdefinitionsoh02bvlg77awin_okns53ivlns55munch" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xb_ok : ltac2:(zQ "20!h9!ld>2st$1>1B$0P") := ltac2:(zQ "40!h9!ld!m6!r4\2st$1\1B$0@3$3^2@2$2^2^1^1").
(* [comment removed for export] *)
Definition xc_ok : ltac2:(zQ "20!h9!ld>2st$1>1m$0P") := ltac2:(zQ "f0!rd!t9!v6!vd!hg6!hgc!h9!hh1!hhf!ld!hib!hj6!hjf!hkc!hn8\2st$9\1m$6@2$5$0\2ch$0@2$4@3$1@1$3$0@2$c@1$8^3@2$e^2$d@2$2$0^1@3$1$b@1$a^1$7").

Definition WFQ : ltac2:(zQ "30!hnf!h9!ld>2st$2>2XC@1$0$1>2XB@1$0$1P") := ltac2:(zQ "k30!hg6!h9!t9!rd!hp9!hpf!hq8!hr5!hrb!hsb!ht9!hu3!hu9!hv1!hva!ig2!igb!ih2!ihb!hnf!ii4!iia!ij9!ik2!ikf!im4!imf!inb!is9!ivd!jg4!v6!jga!vd!hgc!jh1!jid!hh1!jj4!hhf!jjf!jkb!jl5!jlf!ld!jmc!hib!jn9!hj6!jo0!jp0!jpe!jr4!jsa!jt3!jtc!ki6!kif!kj8!kk4!kl9!km5!kn2!kna!ko4!kp0!kpa\2st$ic\2XC@1$h3$1\2XB@1$h3$1@2$0>1c$1>0@2$0@2$bZ^1@2$he^1$j2@2$0@2$jd^5^2@2$ja^5^2@2$0@2$h1$1@3$7$1@1$jb^3^1@2$0>2ch$3>0@3$4$3^1@1$6^4@2$jc^5^2@2$0>2ch$3>3ch'$3>0@3$4$3^2@1$6^5>0@3$4$3^2@1$6^6>0@3$2$1@1$9^4@1$9^3@3$2$3^5^4@2$0@3$2$1@2$h0$3@3$jf$3\2ch$3@1$i0@1$id^1@1$6^3@2$h0$f@1$d^3@2$0@2$h1$1@4$i4$f$1$j7@1$d^3@2$0@2$b@2$h0$f@1$d^3@1$8^3@2$0@2$0@3$2$1@2$k1@1$8^3$h8Z@2$0@2$bZ@1$8^3@2$b@1$8^3@2$k2+jf$h8@2$0@2$hc^3@1$e^3@2$0@2$hc^3@1$c^3@2$0@2$h1$1@3$7$1@4$k0$5$1$ha@3$7$5@1$a@1$e^3@1$a@1$c^3^2@2$0>2ch$3>0@3$4$3^1@1$6^4>0@3$2$j0@1$ie^2$i5@2$i3@2$i2$5\1b$5@2$0@3$4$5^1@3$7$5@1$a@1$e^7@1$a@1$c^7@3$4$1@1$h5^4@1$ha^1@3$4$1@1$h5^3^5@2$0@3$2$1@1$hb@2$h7^3ZZ@2$0@3$2$1@1$hb@2$h7^3+hfZ@2$0@3$2$1@1$h9@2$h6^3ZZ@2$0@3$2$1@1$h9@2$h6^3+hfZ@2$0@3$2$h4@2$h2$j6@1$ib^3Ni0@2$0@3$2$h4@2$h2$j5@1$i6^3Ni0@2$0@3$2$1@1$i9^3$j3@2$0@3$2$1@1$ia^3$j4@2$0@3$2$1@1$i8^3$j1@2$0>1k$hd>1x$3>0@3$2@1$i1$3@3$je$3^2@1$i7^5@2$hf$3^1@2$0@3$2$hd^3@1$if@1$9^2@2$heZ@1$9^2@2$0>1m$1>0@3$4$1^1^3@2$j9^5^2>1B$1>0@3$4$1^1^2@2$j8^5^2").

(* [comment removed for export] *)
Definition qbounds : ltac2:(zQ "10!ld>2st$0P") := ltac2:(zQ "80!kq1!hu3!hg6!hu9!jjf!jkb!hva!ld\2st$7@2$2@2$1@1$0@1$6^1@1$4^1@2$1@1$0@1$3^1@1$5^1").

Lemma WF_WFQ : ltac2:(zQ "80!kqc!h9!hg6!kr2!ld!kr8!krf!ksa>2st$4@2$3@1$7^1@2$2@3$5^1@1$0$1@1$0$1@1$6^1").
Proof.
  intros st. unfold WF, WFQ, qbounds. rewrite !app_nil_r. split.
  - (intros nd_i1; ndestruct nd_i1 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24)).
    split; [| exact (conj W11 W12)].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
    split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. split; [exact W13|].
    split; [intros ch Hin Hq; left; exact (W14 ch Hin Hq)|].
    split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|]. split; [exact W19|]. split; [exact W20|].
    split; [exact W21|]. split; [exact W22|]. split; [exact W23|]. split; [exact W24|]. split; [intros m []| intros B []].
  - (intros nd_i2; ndestruct nd_i2 as ((W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & _ & _) & B1 & B2)).
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
    split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. split; [exact B1|]. split; [exact B2|]. split; [exact W13|].
    split; [intros ch Hin Hq; destruct (W14 ch Hin Hq) as [E|[]]; exact E|].
    split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|]. split; [exact W19|]. split; [exact W20|].
    split; [exact W21|]. split; [exact W22|]. split; [exact W23| exact W24].
Qed.

(* [comment removed for export] *)
Lemma WFQ_region : ltac2:(zQ "90!h9!hnf!hg6!ld!jp0!kr8!km5!hu3!jg4>2st$3>2XC@1$1$0>2XB@1$1$0>1c$0>0@3$5^4^3^2>0@2$2@2$7Z^2@2$8^2$4@2$6^6^3").
Proof. intros st XC XB c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WFQ_cache : ltac2:(zQ "90!h9!hnf!hg6!ld!jp0!kr8!kj8!hu3!jg4>2st$3>2XC@1$1$0>2XB@1$1$0>1c$0>0@3$5^4^3^2>0@2$2@2$7Z^2@2$8^2$4@2$6^6^3").
Proof. intros st XC XB c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WFQ_chunk : ltac2:(zQ "80!hnf!h9!rd!ld!hq8!kr8!kl9!hp9>2st$3>2XC@1$0$1>2XB@1$0$1>2ch$2>0@3$5^4^3^2>0@3$7$2^2@1$4^5@2$6^6^3").
Proof. intros st XC XB ch W Hin. ndestruct W as (_ & _ & H & _). apply H, Hin. Qed.
Lemma WFQ_inj : ltac2:(zQ "90!rd!h9!hnf!t9!hsb!hq8!hp9!ld!kr8>2st$7>2XC@1$2$1>2XB@1$2$1>0@3$8^3^2^1>2ch$0>3ch'$0>0@3$6$0^2@1$5^6>0@3$6$0^2@1$5^7>0@3$3$1@1$4^4@1$4^3@3$3$0^5^4").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_carved : ltac2:(zQ "70!h9!hnf!hr5!ld!kr8!kk4!ih2>2st$3>2XC@1$1$0>2XB@1$1$0>0@3$4^3^2^1@2$6$0@3$2$0@1$5^4^2").
Proof. intros st XC XB W. ndestruct W as (_ & H & _). exact H. Qed.
Lemma WFQ_tq : ltac2:(zQ "60!hnf!h9!hva!ld!kr8!is9>2st$3>2XC@1$0$1>2XB@1$0$1>0@3$4^3^2^1@2$5^4@1$2^4").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_gq : ltac2:(zQ "60!hnf!h9!hu9!ld!kr8!is9>2st$3>2XC@1$0$1>2XB@1$0$1>0@3$4^3^2^1@2$5^4@1$2^4").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_batch : ltac2:(zQ "b0!hpf!hnf!h9!ht9!hr5!hu9!hva!ld!kr8!kt0!hp9>2st$7>2XC@1$1$2>2XB@1$1$2>1b$0>0@3$8^4^3^2>0@3$a$0^2@3$4$0@1$3@1$6^5@1$3@1$5^5@2$9^6^3").
Proof.
  intros st XC XB b W Hin. apply in_app_iff in Hin as [Hin|Hin]; [apply (proj1 (WFQ_tq st XC XB W)) | apply (proj1 (WFQ_gq st XC XB W))]; exact Hin.
Qed.
Lemma WFQ_qnodup : ltac2:(zQ "c0!h9!hr5!hnf!hpf!ht9!hu9!hva!ld!imf!kr8!ih2!ko4>2st$7>2XC@1$2$0>2XB@1$2$0>0@3$9^3^2^1@2$a$0@3$1$0@4$b$3$0$8@3$1$3@1$4@1$6^4@1$4@1$5^4^3").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_consts : ltac2:(zQ "c0!h9!t9!hnf!hg6!jjf!jkb!jl5!ld!jo0!jpe!jr4!kr8>2st$7>2XC@1$2$0>2XB@1$2$0>0@3$b^3^2^1@2$3@3$1$0@1$5^4$9@2$3@3$1$0@1$6^4$a@3$1$0@1$4^4$8").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). exact (conj H1 (conj H2 H3)). Qed.
Lemma WFQ_lens : ltac2:(zQ "c0!ihb!hnf!ii4!t9!h9!hg6!jj4!jlf!ld!jsa!jt3!kr8>2st$8>2XC@1$1$4>2XB@1$1$4>0@3$b^3^2^1@2$5@3$3$2@2$0$a@1$7^4Ni0@3$3$2@2$0$9@1$6^4Ni0").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma WFQ_keys : ltac2:(zQ "f0!rd!hnf!t9!h9!hsb!ivd!v6!vd!hg6!hhf!ld!jn9!kr8!kn2!jg4>2st$a>2XC@1$1$3>2XB@1$1$3>0@3$c^3^2^1>1k$5>1x$0>0@3$2@1$7$0@3$d$0^2@1$9^6@2$6$0^1@2$8@3$2$5^3@1$b@1$4^2@2$eZ@1$4^2").
Proof. intros st XC XB W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WFQ_xc : ltac2:(zQ "60!h9!hnf!ld!kr8!kif!hp9>2st$2>2XC@1$1$0>2XB@1$1$0>1m$0>0@3$3^4^3^2>0@3$5$0^2^4@2$4^6^3").
Proof. intros st XC XB m W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). apply H. Qed.
Lemma WFQ_xb : ltac2:(zQ "60!h9!hnf!ld!kr8!ki6!hp9>2st$2>2XC@1$1$0>2XB@1$1$0>1B$0>0@3$3^4^3^2>0@3$5$0^2^3@2$4^6^3").
Proof. intros st XC XB B W. ndestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). apply H. Qed.

(* [comment removed for export] *)
Lemma WFQ_perm : ltac2:(zQ "50!h9!hnf!kr8!kv8!ld>2st$4>2XC@1$1$0>3XC'@1$1$0>2XB@1$1$0>3XB'@1$1$0>0@3$3$0^4^3>0@3$3$0^3^2>0@3$2^7^6^4@3$2^8^6^4").
Proof.
  intros st XC XC' XB XB' PC PB W.
  ndestruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
  split; [exact W1|]. split; [eapply Permutation_NoDup; [| exact W2]; apply Permutation_app_head; exact PB|].
  split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|].
  split; [eapply Permutation_NoDup; [| exact W11]; apply Permutation_app_head; exact PC|].
  split; [intros ch Hin Hq; destruct (W12 ch Hin Hq) as [E|E]; [left; exact E| right; eapply Permutation_in; [exact PC| exact E]]|].
  split; [exact W13|]. split; [exact W14|]. split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|].
  split; [exact W19|]. split; [exact W20|]. split; [exact W21|]. split; [exact W22|].
  split; [intros m Hm; apply W23; eapply Permutation_in; [apply Permutation_sym; exact PC| exact Hm]|].
  intros B HB. apply W24. eapply Permutation_in; [apply Permutation_sym; exact PB| exact HB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition ARmem : ltac2:(zQ "20!lk5!loa>1s$0>1m$1P") := ltac2:(zQ "h90!hg6!lp1!rd!ht9!lp9!h9!hu9!hva!hq8!jp0!lk5!lq8!lr5!ls2!lsc!lt8!lu6!lv9!mg7!mhd!mi8!loa!hp9!hu3!jg4\1s$a\1m$h5@2$0@2$e^2^1@2$0@2$c^2^1@2$0@2$h4^2^1@2$0@2$h3^2^1@2$0@2$d^2^1@2$0>1c$5>0@2$0@2$h7Z^1@2$h8^1$9@2$0@3$h1^4^3^2@2$0@3$f^4^3^2@2$0@3$h2^4^3^2@3$h0^4^3^2@2$0>2ch$2>0@3$h6$2^1@1$8@1$1^3@2$b^3^2@2$0@2$4^1@1$3@1$7@1$1^2@2$4^1@1$3@1$6@1$1^2").

  Lemma AREP_split : ltac2:(zQ "90!hg6!kr2!mn7!mo0!lp1!lk5!mo8!ksa!loa>1s$5>1m$8@2$1@3$3?5HCEIL^2^1@2$0@2$0@2$6?5HCEIL^2@1$7@1$4^2@2$2^2^1").
  Proof. intros s m. unfold AREP, ast_ok, ARmem. tauto. Qed.

  Definition AREPQ : ltac2:(zQ "40!hnf!h9!lk5!loa>1s$2>2XC@1$0$1>2XB@1$0$1>1m$3P") := ltac2:(zQ "90!hnf!hg6!h9!mn7!kr8!lp1!lk5!mo8!loa\1s$6\2XC@1$0$2\2XB@1$0$2\1m$8@2$1@2$7?5HCEIL^4@2$1@3$4@1$5^4^3^2@2$3^4^1").

  Lemma AREP_AREPQ : ltac2:(zQ "a0!kqc!h9!hg6!kr2!mp5!krf!mo0!lp1!lk5!loa>1s$8>1m$9@2$3@3$6?5HCEIL^2^1@2$2@4$4^2@1$0$1@1$0$1^1@1$5@1$7^2").
  Proof.
    intros s m. rewrite AREP_split. unfold AREPQ. rewrite (WF_WFQ (a_st s)). tauto.
  Qed.
  Lemma AREP_of_AREPQ : ltac2:(zQ "80!kqc!h9!mp5!krf!mo0!lp1!lk5!loa>1s$6>1m$7>0@4$2^2@1$0$1@1$0$1^1>0@1$3@1$5^3@3$4?5HCEIL^4^3").
  Proof. intros s m H B. exact (proj2 (AREP_AREPQ s m) (conj H B)). Qed.

  Lemma AREPQ_placed : ltac2:(zQ "60!hnf!h9!mp5!lk5!mo8!loa>1s$3>2XC@1$0$1>2XB@1$0$1>1m$5>0@4$2^4^3^2^1@2$4?5HCEIL^5").
  Proof. intros s XC XB m H. exact (proj1 H). Qed.
  Lemma AREPQ_WFQ : ltac2:(zQ "70!hnf!h9!mp5!kr8!lp1!lk5!loa>1s$5>2XC@1$0$1>2XB@1$0$1>1m$6>0@4$2^4^3^2^1@3$3@1$4^5^4^3").
  Proof. intros s XC XB m H. exact (proj1 (proj2 H)). Qed.
  Lemma AREPQ_mem : ltac2:(zQ "60!hnf!h9!mp5!mn7!lk5!loa>1s$4>2XC@1$0$1>2XB@1$0$1>1m$5>0@4$2^4^3^2^1@2$3^5^2").
  Proof. intros s XC XB m H. exact (proj2 (proj2 H)). Qed.
  Lemma AREPQ_perm : ltac2:(zQ "60!h9!hnf!mp5!kv8!lk5!loa>1s$4>2XC@1$1$0>3XC'@1$1$0>2XB@1$1$0>3XB'@1$1$0>1m$5>0@3$3$0^5^4>0@3$3$0^4^3>0@4$2^8^7^5^3@4$2^9^7^5^4").
  Proof. (intros s XC XC' XB XB' m PC PB nd_i3; ndestruct nd_i3 as (P & W & M)). split; [exact P|]. split; [exact (WFQ_perm _ _ _ _ _ PC PB W)| exact M]. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section FrameQ.
    Variable s : ltac2:(zQ "10!lk5$0").
    Variables XC XB : list Z.
    Variables m m' : mem.
    Variable P : ltac2:(zQ "10!h9>0$0P").
    Hypothesis AG : ltac2:(zQ "10!nr9@3$0?1P?1m?2m'").
    Hypothesis WM : ltac2:(zQ "20!nq7!og1@3$1$0?1m?2m'").
    Hypothesis W : ltac2:(zQ "20!kr8!lp1@3$0@1$1?1s?2XC?2XB").

    Ltac tr_cells H := eapply (rw_cells_transport_pt P m m' AG WM); [exact H|];
                       cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat].
    Ltac tr_junk H := eapply (junk_transport_pt P m m' AG WM); [exact H|].
    Ltac tr_u32 H := eapply (u32arr_transport_pt P m m' AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
    Ltac tr_u64 H := eapply (u64arr_transport_pt P m m' AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev.
    Ltac tr_poi H := eapply (poisoned_transport_pt P m m' AG WM); [exact H|].
    Ltac af C := intros ? ?; eapply C; eauto; unfold OI_MISMATCH, OT_UNWINDING, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX,
                 OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER, OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, CACHE_STATS, PCLASS_SIZE, REGIONINFO_SIZE,
                 kNumClasses, kPageSize, kBatchSize, kSpaceSize, kPtrArrayReserve in *; try lia.

    Lemma region_rep_frameQ : ltac2:(zQ "h00!hg6!h9!hn8!hu3!jg4!ik2!lp1!mpe!mq4!mqa!lv9!jp0!mr2!mre!mt3!inb>1c$1>0@2$0@2$3Z^1@2$4^1$b>0>1a$1>0@2$0@2$3@1$9?1s^1@2$4^1@2$2@1$9?1s$c@1?1P^2>0>1a$1>0@2$0@2$3@2$7?1s^4^1@2$4^1@2$2@2$7?1s^4@1$e@2$5@1$6?1s^4@1?1P^2>0>1a$1>0@2$0@2$3@2$2@2$8?1s^5@1$d@2$5@1$6?1s^5^1@2$4^1@2$2@2$8?1s^5@1$f@2$5@1$6?1s^5@1?1P^2>0@3$a?1s?1m^5@3$a?1s?2m'^6").
    Proof.
      intros c Hc HP1 HP2 HP3 H. pose proof (WFQ_region _ _ _ c W Hc) as RO.
      ndestruct H as (R1 & J1 & R2 & J2 & U & J3 & J4). unfold region_rep.
      pose proof (ro_numfreed _ _ RO) as N1. pose proof (ro_fa_le _ _ RO) as N2. pose proof (ro_alloc_nonneg _ _ RO) as N3.
      pose proof (ro_alloc_le _ _ RO) as N4. unfold zlen in N1.
      split; [tr_cells R1; af HP1|].
      split; [tr_junk J1; af HP1|].
      split; [tr_cells R2; af HP1|].
      split; [tr_junk J2; af HP1|].
      split; [tr_u32 U; af HP2|].
      split; [tr_junk J3; af HP2|].
      tr_junk J4; af HP3.
    Qed.

    Lemma pclass_rep_frameQ : ltac2:(zQ "a0!mub!hn8!hg6!h9!mva!lt8!hu3!jg4!kpa!jp0>1c$3>0@2$2@2$6Z^1@2$7^1$9>0>1a$3>0@2$2@2$6@2$1@1$4?1s@2$8$0^3^1@2$7^1@2$1@2$1@1$4?1s@2$8$0^3$0@1?1P^2>0@3$5?1s?1m^3@3$5?1s?2m'^4").
    Proof.
      intros c Hc HP H. pose proof (WFQ_cache _ _ _ c W Hc) as CO.
      ndestruct H as (P1 & P2 & U & J). unfold pclass_rep.
      pose proof (co_count _ _ CO) as N1. unfold zlen in N1.
      assert (N2 : 0 <= pc_count (get_pc (a_st s) c) <= 16).
      { pose proof (co_bound _ _ CO) as B. pose proof (class_size_table_facts c Hc) as T.
        destruct (as_cache_inited (a_st s)); lia. }
      split; [tr_cells P1; af HP|].
      split; [tr_cells P2; af HP|].
      split; [tr_u32 U; af HP|].
      tr_junk J; af HP.
    Qed.

    Lemma sec_rep_frameQ : ltac2:(zQ "f0!hg6!h9!jtc!ig2!ng5!lp1!mhd!hn8!hu3!jg4!hrb!hv1!mr2!hp9!kpa>0>1a$1>0@2$0@2$8@1$4?1s^1@2$9^1@2$7@1$4?1s@2$e+8@1$a@1$5?1s@1?1P^2>0>1h$3>1a$1>0@3$d$3^2@1$b@1$5?1s>0@2$0@2$8@1$2^3^2@2$9^2@2$7@1$2^3$c@1?1P^3>0@2$6?1s?1m@2$6?1s?2m'").
    Proof.
      (intros HP1 HP2 nd_i4; ndestruct nd_i4 as (U & J & H)). unfold sec_rep.
      ndestruct W as (_ & _ & _ & _ & Wn & _ & Wres & _).
      assert (N0 : 0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia).
      split; [tr_u64 U; unfold zlen in *; af HP1|].
      split; [tr_junk J; unfold zlen in *; af HP1|].
      intros i h Hi. destruct (H i h Hi) as [C1 J1]. pose proof (nth_error_In _ _ Hi) as IN.
      split; [tr_cells C1; af HP2| tr_junk J1; af HP2].
    Qed.

    Lemma region_shadow_rep_frameQ : ltac2:(zQ "h82!lp1!h9!ik2!ngd!hn8!hg6!hu3!jg4!mre!nh3!nha!mpe!mq4!mg7!hp9!jh1!nic!ij9!jp0!nj9!nk5!mt3!inb!nl5&@2$4@2$c?1s^4@1$8@2$2@1$0?1s^4&@1$3~0>1c$1>0@2$5@2$6Z^1@2$7^1$h2>0>2cp$1>1a$1>0@2$f@3$e$1^2@1$h4@2$2@1$0?1s^4@3$e$1^2@1$h3@2$h1@1$0?1s^4>0@2$5@2$6@1$3@3$a@1$0?1s^5^3^2@2$7^2@2$4@1$3@3$a@1$0?1s^5^3@2$9@1$h0^5+8@1?1P^3>0>1a$1>0@2$5@2$6~1^1@2$7^1@2$4~1@2$9@2$h7@1$h6@2$2@1$0?1s^4@1$8@2$2@1$0?1s^4+8@1?1P^2>0>1a$1>0@2$5@2$6@1$3@2$b?1s^5^1@2$7^1@2$4@1$3@2$b?1s^5@2$9@1$h5@2$2@1$0?1s^5+8@1?1P^2>0@3$d?1s?1m^5@3$d?1s?2m'^6").
    Proof.
      (intros c Hc HP1 HP2 HP3 nd_i5; ndestruct nd_i5 as (H1 & H2 & H3 & H4)). pose proof (WFQ_region _ _ _ c W Hc) as RO. pose proof (class_size_table_facts c Hc) as CS.
      pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO). pose proof (ro_fa_le _ _ RO). pose proof (ro_numfreed _ _ RO).
      unfold zlen in *. unfold region_shadow_rep.
      split; [| split; [| split]].
      - intros cp Hin. specialize (H1 cp Hin). tr_poi H1. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af (HP1 cp).
      - intros cp Hin. specialize (H2 cp Hin). tr_poi H2. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af (HP1 cp).
      - tr_poi H3. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af HP2.
      - tr_poi H4. rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). af HP3.
    Qed.

    Lemma chunk_rep_frameQ : ltac2:(zQ "70!rd!lq8!h9!hq8!lp1!nlc!hp9>2ch$0>0@3$6$0^1@1$3@1$4?1s>0>1a$2>0@2$5^3^1@1?1P^2>0@2$1?1m^3@2$1?2m'^4").
    Proof.
      intros ch Hin HP H. pose proof (WFQ_chunk _ _ _ ch W Hin) as CO. unfold achunk_range in HP.
      ndestruct CO as (U1 & U2 & U3 & U4 & _).
      pose proof (rz_size_facts (ch_used ch)) as RZ. rewrite <- (eq_refl : rq_rz (compute_req (ch_used ch)) = rz_size (ch_used ch)) in RZ.
      rewrite <- U3 in RZ. ndestruct RZ as (RZ1 & RZ2 & _).
      ndestruct H as ((b1 & actx & HD & Hb1 & Hb1') & LC & ST & JR & PL & PR & PH). unfold chunk_rep.
      assert (NS : 0 <= nsh (ch_used ch) /\ 8 * nsh (ch_used ch) = round_up (ch_used ch) 8 /\ ch_used ch <= round_up (ch_used ch) 8 < ch_used ch + 8).
      { unfold nsh, round_up. Z.div_mod_to_equations. lia. }
      split.
      { exists b1, actx. split; [|split; [exact Hb1| exact Hb1']]. tr_cells HD. unfold kChunkHeaderSize. intros ? ?; eapply HP; left; lia. }
      split.
      { destruct LC as [LC|[LC1 LC2]]; [left; exact LC| right]. split; [tr_cells LC1; intros ? ?; eapply HP; left; lia| tr_junk LC2; intros ? ?; eapply HP; left; lia]. }
      split.
      { destruct (ch_state ch) eqn:E.
        - destruct ST as [ST1 ST2]. split; eapply wr_at_transport; eauto.
        - destruct ST as [ST1 ST2]. split; [tr_junk ST1; intros ? ?; eapply HP; do 2 right; left; split; [first [exact E | reflexivity]| lia]
                                            | tr_poi ST2; rewrite Z2Nat.id by lia; intros ? ?; eapply HP; do 5 right; left; split; [first [exact E | reflexivity]| lia]]. }
      split; [tr_junk JR; intros ? ?; eapply HP; right; left; lia|].
      split; [tr_poi PL; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); intros ? ?; eapply HP; do 3 right; left; lia|].
      split.
      { tr_poi PR. destruct (Z.le_gt_cases 0 ((ch_end ch - (ch_user_beg ch + round_up (ch_used ch) 8)) / 8)).
        - rewrite Z2Nat.id by lia. intros ? ?; eapply HP; do 4 right; left; lia.
        - rewrite (Z2Nat.nonpos _) by lia. intros a Ha. cbn in Ha. lia. }
      destruct (ch_primary ch) eqn:E; [exact I|]. tr_poi PH. intros ? ?; eapply HP. do 6 right. split; [reflexivity| lia].
    Qed.
  End FrameQ.

  (* [comment removed for export] *)
  Theorem AREPQ_frame_pt : ltac2:(zQ "90!hnf!h9!mp5!loa!nq7!nr0!nr9!lk5!og1>1s$7>2XC@1$0$1>2XB@1$0$1>1m$3>2m'$3>0@4$2^5^4^3^2>0@3$6@1$5^6^3^2>0@3$8$4^4^3@4$2^8^7^6^4").
  Proof.
    intros s XC XB m m' H AG WM.
    ndestruct H as (PL & W & I & F & T & SC & IA & RC & CH & BT & BG).
    split; [exact PL|]. split; [exact W|].
    split; [apply (inst_rep_frame s m m' _ AG WM (af_inst s) I)|].
    split; [apply (flags_rep_frame s m m' _ AG WM (af_flags s) F)|].
    split; [apply (thread_rep_frame s m m' _ AG WM (af_thread s) T)|].
    split; [apply (sec_rep_frameQ s XC XB m m' _ AG WM W (af_ptrarr s) (fun h a Hh Ha => af_sechdr s a h Hh Ha) SC)|].
    split; [apply (ia_rep_frame s m m' _ AG WM); [intros a Ha; eapply af_flags; do 13 right; left; exact Ha| exact IA]|].
    split.
    { intros c Hc. ndestruct (RC c Hc) as (R1 & R2 & R3 & R4).
      split; [apply (region_rep_frameQ s XC XB m m' _ AG WM W c Hc (af_rinfo s) (fun a Ha => af_farray s a c Hc Ha) (fun a Ha => af_tail s a c Hc Ha) R1)|].
      split.
      { apply (pclass_rep_frameQ s XC XB m m' _ AG WM W c Hc); [| exact R2]. intros a Ha. apply af_thread. left.
        unfold a_cache, OT_CACHE, PCLASS_SIZE, OT_UNWINDING, kNumClasses in *. lia. }
      split; [apply (region_shadow_rep_frameQ s XC XB m m' _ AG WM W c Hc (fun cp a Hin Ha => af_sh_freech s a c cp Hc Hin Ha) (fun a Ha => af_sh_tail s a c Hc Ha) (fun a Ha => af_sh_farray s a c Hc Ha) R3)
            | apply (region_junk_rep_frame s m m' _ AG WM c Hc (fun cp a Hin Ha => af_freech s a c cp Hc Hin Ha) R4)]. }
    split.
    { intros ch Hin. apply (chunk_rep_frameQ s XC XB m m' _ AG WM W ch Hin); [| exact (CH ch Hin)].
      intros a Ha. destruct Ha as [Ha|[Ha|[[Q Ha]|[Ha|[Ha|[[Q Ha]|[NP Ha]]]]]]].
      - eapply af_chleft; eauto. - eapply af_chright; eauto. - eapply af_chquar; eauto. - eapply af_sh_chleft; eauto.
      - eapply af_sh_chright; eauto. - eapply af_sh_chquar; eauto. - eapply af_sh_sechdr; eauto. }
    assert (BOK : forall b, In b (qc_list (as_tq (a_st s)) ++ qc_list (as_gq (a_st s))) ->
              0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
    { intros b Hb. pose proof (WFQ_batch _ _ _ b W Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. lia. }
    split.
    - eapply (batches_rep_transport (afoot s) m m'); [exact AG| exact WM| | | exact BT].
      + intros b a Hb Hr. destruct Hr as [Hr|Hr]; [eapply af_batch| eapply af_sh_batch]; eauto; apply in_app_iff; left; exact Hb.
      + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
    - eapply (batches_rep_transport (afoot s) m m'); [exact AG| exact WM| | | exact BG].
      + intros b a Hb Hr. destruct Hr as [Hr|Hr]; [eapply af_batch| eapply af_sh_batch]; eauto; apply in_app_iff; right; exact Hb.
      + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
  Qed.

  Theorem AREPQ_frame : ltac2:(zQ "d0!hnf!oga!h9!mp5!oid!vd!nq7!lk5!oj3!loa!oje!ok5!og1>1s$7>2XC@1$0$2>2XB@1$0$2>1W@1$0$a>1m$9>2m'>0@1$4@1$1#k0@1$5@1$4@1$1#8>0@4$3^6^5^4^2>0@3$b^4^3^2>0@3$c$6^4^3>0@2$8^9^6@4$3^a^9^8^5").
  Proof. intros s XC XB W m m' H MU WM AW. eapply AREPQ_frame_pt; [exact H| eapply awin_agree; eauto| exact WM]. Qed.

End HCW.
(* [comment removed for export] *)
