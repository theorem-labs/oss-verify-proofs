(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree MallocBlocks.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc4meta01N37Corelib4Init9Datatypesm44prod46Stdlib6ZArith6BinInt1Zo33addm42idm44pairm43snd02N0hc4UNIThcaget_stridehc5m_memo33mul25stdpp6optiont9bfrom_optionhc4aptrhc6mstatehc4ghdr35stdpp7numbers1Nhgc6eq_dec35stdpp7numbers1Zhi76eq_decm44Some25stdpp9countablehk9bN_countablehk9bZ_countablehk9eprod_countable25stdpp9decidablehoabprod_eq_decm46option37Corelib4Init5Logichr32eqhr32exhc6mkGhdrhc8s_groups25stdpp4basehu76lookup25stdpp4gmaphvd4gmaphvdbgmap_lookup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_B~~~~~~ii05hostsm44boolm44trueo37testbithr32orhc7m_availhc7m_freedii05is_gmhccget_meta_rechcbm_sizeclasshr33andhr33iffhc6m_nexthc4optro33subm43fsthc5Knownhc9cell_readhc7cellvalhcaget_shadowo34landii08gmeta_okhccg_active_idxo32lehc6g_metahcam_last_idxhc7s_slotshcbslot_start'hc7Unknowno32ltii09sstart_ofhc2IBhc3ctxhc7bounceshc8c_secrethc5c_seqhc9unmap_seqhc5usageo33powhc6regionhc7BrkLivehc5RKBrkhc8brkstatehc5c_brkhc6r_kindhc5rkindhc9s_regionshr34Truehr33nothc7RKGrouphc4areaii06ng_ptrhc6a_nexthccc_avail_metahch2c_avail_meta_areashch0c_meta_area_headhch0c_meta_area_tailhc7s_areas" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sstart_of : ltac2:(zQ "20!h9!la>2mr$1>1i$0$0") := ltac2:(zQ "e0!h9!m1!nc!pb!q1!q6!qd!r3!r7!re!sb!la!t3!u7\2mr$b\1i$0@2$3@2$3@3$6$1$0@5$d@2$2$1$0@2$2$1$0@1$4@2$2$1$0@4$5$1$0$7Z@1$a^2$8@2$c@1$9^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)

Notation rec st m := (get_meta_rec st m) (only parsing).

(* [comment removed for export] *)
Definition hosts : ltac2:(zQ "20!v5!vc>2st$1>1b$0>1g$0P") := ltac2:(zQ "h40!h9!v5!hg5!m1!hhd!hj8!hk2!hla!hm9!hn8!hpb!hqa!hs7!hsd!ht3!vc!htc!hv3!ig9!ih1\2st$f\1b$1\1g$1@2$d$0\2ai$0@3$c@1$b$2@6$h1$1$2@4$h2$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2@4$h3$1@4$a$3$4$0$5@6$9$3$4$7$0$5$8$2^3@1$h0^4@2$6$2@2$e@2$6$1^2^1").
Definition is_gm : ltac2:(zQ "20!v5!vc>2st$1>1g$0P") := ltac2:(zQ "40!v5!hsd!im6!vc\2st$3\1g$0@2$1$0\1b$0@3$2^3^1^2").

Definition slot_free : ltac2:(zQ "20!h9!la>2mr$1>1i$0P") := ltac2:(zQ "90!imf!in6!hs7!ind!io7!h9!iod!ip7!la\2mr$8\1i$5@2$4@3$2$0@2$3@1$7^2^1$1@3$2$0@2$3@1$6^2^1$1").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ci_links_t (st : mstate) : Prop := mkCL {
  cl_next : forall m nx, m_next (get_meta_rec st m) = Some nx ->
              m_prev (get_meta_rec st nx) = Some m /\ meta_slot st nx;
  cl_prev : forall m pv, m_prev (get_meta_rec st m) = Some pv ->
              m_next (get_meta_rec st pv) = Some m /\ meta_slot st pv;
  cl_none : forall m, m_next (get_meta_rec st m) = None <-> m_prev (get_meta_rec st m) = None;
  (* [comment removed for export] *)
  cl_self : forall m, m_next (get_meta_rec st m) <> None -> meta_slot st m
}.

(* [comment removed for export] *)
Record ci_heads_t (st : mstate) : Prop := mkCH {
  ch_free : forall h, c_free_meta_head (ctx st) = Some h ->
              m_next (get_meta_rec st h) <> None /\ m_mem (get_meta_rec st h) = None;
  ch_active : forall sc a, active st sc = Some a ->
              0 <= sc < 48 /\ m_next (get_meta_rec st a) <> None /\ is_gm st a /\ m_sizeclass (get_meta_rec st a) = sc
}.

(* [comment removed for export] *)
Definition ci_homog : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "c0!iq1!v5!iqa!hs7!ir9!hk2!is7!ise!h9!it5!vc!ite\2st$a>1m$1>2nx$1>0@3$3$b@1$9@2$2^3^2@2$5$1^1@2$6@2$7@2$0^4^3@2$0^4^2>0@2$0^4^3@3$3$8@1$4@2$2^5^3@1$4@2$2^5^4").

(* [comment removed for export] *)
Definition hdr_known : ltac2:(zQ "30!v5!h9!vc>2st$2>1p$0>2b1$0>2i1$1P") := ltac2:(zQ "h10!h9!m1!qd!hs7!iu5!is7!iub!hsd!iv1!iv9!jg5!jgf!v5!t3!vc!pb!jhc\2st$e\1p$c\2b1$c\2i1$0@2$7$0\2v3$0@2$7$0\2lo$0@2$7$0\2hi$0@2$5@3$3$a@2$9@2$b^7@3$6$1$0^6@2$4@3$2$1$0^6+3@1$8^3@2$5@3$3$0@2$h0^3+hf^4@2$5@3$3$a@2$9@2$b^7@3$6$1$0^6@2$4@3$2$1$0^6+2@1$8^2@2$5@3$3$a@2$9@2$b^7@3$6$1$0^6@2$4@3$2$1$0^6+1@1$8^1@3$3$0@2$d+h0@2$f^2@2$d+hg0^1@2$4@2$4@3$2$1$0^6@3$2$1$0^5+h0").

(* [comment removed for export] *)
Record gmeta_ok (st : mstate) (g b : aptr) : Prop := mkGO {
  go_slot : meta_slot st g;
  go_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  go_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  go_li : 0 <= m_last_idx (get_meta_rec st g) <= 31;
  go_freeable : m_freeable (get_meta_rec st g) = 1;
  go_sc : (0 <= m_sizeclass (get_meta_rec st g) < 48)
          \/ (m_sizeclass (get_meta_rec st g) = 63 /\ m_last_idx (get_meta_rec st g) = 0 /\ 0 < m_maplen (get_meta_rec st g));
  go_maplen : 0 <= m_maplen (get_meta_rec st g) < 2^35;
  (* [comment removed for export] *)
  go_bits : forall i, 0 <= i ->
      (Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g))
      /\ (Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g));
  go_mem : m_mem (get_meta_rec st g) = Some b;
  go_region : exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup
      /\ 0 <= snd b /\ snd b mod 16 = 0
      /\ sstart_of (get_meta_rec st g) (m_last_idx (get_meta_rec st g) + 1) <= round_up_pg (r_len r)   (* [comment removed for export] *)
      /\ (m_maplen (get_meta_rec st g) <> 0 -> snd b = 0 /\ m_maplen (get_meta_rec st g) * 4096 = round_up_pg (r_len r));
  go_stride : UNIT <= get_stride (get_meta_rec st g) /\ get_stride (get_meta_rec st g) mod UNIT = 0;
  (* [comment removed for export] *)
  go_nest : m_maplen (get_meta_rec st g) = 0 ->
      exists g1 i1 b1, (s_slots st) !! b = Some (g1, i1) /\ hosts st b1 g1 /\ fst b1 = fst b
        /\ b = slot_start' (get_meta_rec st g1) i1 /\ 0 <= i1 <= m_last_idx (get_meta_rec st g1)
        /\ ~ slot_free (get_meta_rec st g1) i1
        /\ m_sizeclass (get_meta_rec st g) < m_sizeclass (get_meta_rec st g1)
        (* [comment removed for export] *)
        /\ hdr_known st b b1 i1
}.

Definition ci_gmeta : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "40!v5!ji3!im6!vc\2st$3>1b$0>1g$0>0@3$2^3^2^1@3$1^4^2^3").

(* [comment removed for export] *)
Definition ci_groups : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "ha0!v5!hg5!m1!h9!hhd!hj8!hk2!is7!hs7!jif!jje!hla!hm9!hn8!hpb!hqa!hsd!jk3!iqa!jkc!vc!ite!htc!hv3!ig9!ih1\2st$h4>1b$0>2gh$1>0@3$8@1$f$1@6$h7$0$1@4$h8$0@4$e$2$4$3$5@6$d$2$4$b$3$5$c$1@4$h9$0@4$e$2$4$3$5@6$d$2$4$b$3$5$c$1^2@1$h6^3@2$6$1^1@2$h0$0\1g$0@2$7@3$8$h5@1$h1^3@2$6$0^1@2$7@2$aZ@1$9^3@2$a@1$9^3@1$h3@2$h2^5^1").

(* [comment removed for export] *)
Definition ci_group_inj : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "40!v5!im6!hs7!vc\2st$3>2b1$0>2b2$0>1g$0>0@3$1^4^3^1>0@3$1^5^3^2@3$2$0^5^4").

(* [comment removed for export] *)
Definition ci_slots : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "h90!v5!h9!nc!m1!hhd!hj8!is7!hs7!iqa!jje!hla!hm9!hn8!hpb!hk2!hqa!q6!iq1!jkc!vc!jl9!jm3!hv3!ig9!ih1\2st$h3>1s$0>1g$0>1i$1>0@3$7@1$f@2$2$0$1@6$h6$0@2$2$0$1@4$h7$0@4$d$3$4$1$5@6$c$3$4$a$1$5$b@2$2$0$1@4$h8$0@4$d$3$4$1$5@6$c$3$4$a$1$5$b@2$2$0$1^3@1$h4^4@2$e@2$2$0$1@4$h0$0$1^2^1@2$6@2$h1^5^3@2$6@3$7$0^4@2$h5@2$8^5^3^2@2$6@2$9Z^2@2$9^2@1$h2@2$8^5^3").
Definition ci_slots_total : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "h90!h9!v5!nc!m1!hhd!hj8!iqa!jje!hla!hm9!hn8!hpb!hk2!hqa!q6!is7!hs7!im6!jkc!vc!jl9!jm3!hv3!ig9!ih1\2st$h3>1b$1>1g$1>1i$0>0@3$h1^4^3^2>0@2$f@2$7Z^2@2$7^2@1$h2@2$6^5^3@3$h0@1$d@2$2$1$0@6$h6$1@2$2$1$0@4$h7$1@4$b$3$4$0$5@6$a$3$4$8$0$5$9@2$2$1$0@4$h8$1@4$b$3$4$0$5@6$a$3$4$8$0$5$9@2$2$1$0@2$h5@2$6^6^4^3@1$h4^6@2$c@2$2$1$0@4$e$1$0^4^3").

(* [comment removed for export] *)
Definition ci_ghdr_unk : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "he0!h9!m1!hg5!hhd!hj8!nc!hs7!v5!hla!hm9!hn8!hpb!hk2!iub!hqa!qd!is7!hsd!jn1!iv9!jg5!jgf!vc!htc!pb!jje!jnb!hv3!ig9!ih1\2st$h6>1b@2$5$1$0>2gh$2>1o$0>0@3$6@1$e$2@6$hb@2$5$1$0$2@4$hc$7@4$b$1$3$0$4@6$a$1$3$8$0$4$9$2@4$hd$7@4$b$1$3$0$4@6$a$1$3$8$0$4$9$2^3@1$h7^4@2$c$2^2>0@2$h0@2$h9Z^2@2$ha^2+c@2$h1$0\1h$0@3$6$h4@2$h3@2$h5^7@3$d$1$0^6@2$h8@3$f$1$0^6^4@1$h2^1").

(* [comment removed for export] *)
Definition ci_hdr0 : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "h20!h9!v5!iqa!jje!iub!is7!hs7!m1!im6!jo0!jod!iv1!iv9!jg5!jgf!jkc!vc!iu5\2st$h0>1g$1>1b$1>1i$0>0@3$8^4^2^3>0@2$5@2$3Z^2@2$3^2@1$f@2$2^5^4@3$6$d@2$c@2$e^6@3$4$7$0^4@2$h1@2$9@2$2^6^5^3$a@1$bZ").

(* [comment removed for export] *)
Record blk_ok (st : mstate) (blk : block) : Prop := mkBK {
  bk_slot : exists g i b, (s_slots st) !! (blk_slot blk) = Some (g, i) /\ hosts st b g /\ fst b = fst (blk_slot blk)
            /\ 0 <= i <= m_last_idx (get_meta_rec st g)
            /\ ~ slot_free (get_meta_rec st g) i
            /\ (exists off, 0 <= off /\ blk_addr blk = conc st (blk_slot blk) + UNIT * off
                           /\ UNIT * off + blk_size blk <= get_stride (get_meta_rec st g) - IB
                           /\ cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - IB) = Known 0
                           /\ hdr_known st (aadd (blk_slot blk) (UNIT * off)) b i);
  (* [comment removed for export] *)
  bk_nogroup : (s_groups st) !! (blk_slot blk) = None;
  bk_size : 0 <= blk_size blk
}.

Definition ci_ctx : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "c0!is7!jje!jnb!jp2!h9!jp8!jq2!jqd!jr5!js1!js9!vc\2st$b@2$0@2$0@2$1Z@1$7@1$3^1@2$2@1$7@1$3^1+hg0@2$0>1i$4@2$0@2$1Z@2$5^2^1@2$2@2$5^2^1+hg0@2$0>1i$4@2$0@2$1Z@2$8^2^1@2$2@2$8^2^1+hg0@2$0>2sc$4@2$0@2$1Z@2$9^2^1@2$2@2$9^2^1@2$a+2+k0@2$0@2$1Z@1$6@1$3^1@2$2@1$6@1$3^1@2$a+2+k0").

Definition ci_brk : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "h60!jsf!m1!hs7!hla!hhd!hk2!hqa!is7!hsd!h9!jt8!ju2!jua!jv5!jp2!vc!jvd!kg6!kge!hv3!ig9!ih1\2st$f>3rid$1>3off$9>0@3$2$c@1$d@1$e^3@2$a^2^1@2$8$0\1r$0@2$7@3$2@1$6$0@6$h3$1$0@4$h4$1$4$3$0@4$h5$1$4$3$0^4@1$h2^5@2$5$0^1@3$2$h1@1$h0^1$b").


(* [comment removed for export] *)
Definition ci_mem_hosts : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "80!v5!hk2!hs7!im6!iqa!sb!vc!ite\2st$6>1q$0>1b$0>0@3$2$7@1$5@2$4^3^2@2$1$0^1@3$3^4^2^3").

(* [comment removed for export] *)
Definition ng_ptr : ltac2:(zQ "20!vc!ite>2st$0>1p$1P") := ltac2:(zQ "h70!jsf!m1!hqa!hs7!v5!hla!hhd!hk2!iub!kha!is7!hsd!ki2!h9!ki9!vc!ite!jvd!kg6!kge!hv3!ig9!ih1\2st$f\1p$h0M2\1p@1$2$4P^1\1q$4@2$b$0\1r$0@2$a@3$3@1$2$0@6$h4$1$0@4$h5$1$6$5$0@4$h6$1$6$5$0@3$8$1$d^2@1$h3^4@2$7$0^1@1$c@3$3$h2@1$h1^1$e$9").
(* [comment removed for export] *)
Definition ci_mptrs : ltac2:(zQ "10!vc>2st$0P") := ltac2:(zQ "ha0!kj3!kja!is7!m1!h9!v5!jp2!hhd!hj8!hla!hm9!hn8!hpb!hk2!hqa!hs7!kk4!kkd!klc!kn2!ko6!vc!kpa!hv3!ig9!ih1\2st$h5@2$2@2$1^1@1$h1@1$6^1@2$2@2$1^1@1$h3@1$6^1@2$2@2$1^1@1$h4@1$6^1@2$2@2$1^1@1$h2@1$6^1>1a$5>2ar$0>0@3$f@1$e$0@6$h7$5$0@4$h8$5@4$c$3$7$4$8@6$b$3$7$9$4$8$a$0@4$h9$5@4$c$3$7$4$8@6$b$3$7$9$4$8$a$0^2@1$h6^3@2$d$0^1@2$1^4@1$h0^2").

(* [comment removed for export] *)
Record blk_clear (st : mstate) (LB : list block) (blk : block) : Prop := mkBC {
  bc_region : exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
     /\ r_base r + 16 <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
     /\ blk_addr blk mod 16 = 0
     /\ (forall a, blk_addr blk <= a < blk_addr blk + blk_size blk ->
           exists h, cell_read (get_shadow st (fst (blk_slot blk))) (a - r_base r) = Unknown h);
  bc_hdrs : forall b gh, (s_groups st) !! b = Some gh -> fst b = fst (blk_slot blk) ->
     blk_addr blk + blk_size blk <= conc st b - IB \/ conc st b + 16 <= blk_addr blk;
  bc_blocks : forall blk', In blk' LB -> blk_slot blk' <> blk_slot blk -> fst (blk_slot blk') = fst (blk_slot blk) ->
     blk_addr blk' + blk_size blk' <= blk_addr blk - 4 \/ blk_addr blk + blk_size blk <= blk_addr blk' - 4
}.

Record CINV (st : mstate) (LB : list block) : Prop := mkCI {
  ci_links : ci_links_t st;
  ci_heads : ci_heads_t st;
  ci_hom : ci_homog st;
  ci_gmetas : ci_gmeta st;
  ci_grps : ci_groups st;
  ci_ginj : ci_group_inj st;
  ci_slts : ci_slots st;
  ci_sltt : ci_slots_total st;
  ci_unk : ci_ghdr_unk st;
  ci_h0 : ci_hdr0 st;
  ci_blks : Forall (blk_ok st) LB;
  ci_nodup : List.NoDup (map blk_slot LB);
  ci_cx : ci_ctx st;
  ci_bk : ci_brk st;
  ci_ticks : ticks_ok st;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ci_memh : ci_mem_hosts st;
  ci_mp : ci_mptrs st;
  ci_bclr : Forall (blk_clear st LB) LB
}.
