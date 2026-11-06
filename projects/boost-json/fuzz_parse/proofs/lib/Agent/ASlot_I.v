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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS ASlot_W1.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Nk61Z06shadow37Corelib4Init9Datatypesmf4prodmf4Somemf6option37Corelib4Init5Logicpe2eq25stdpp4baser76lookup25stdpp9countablescbN_countablescbZ_countable25stdpp4gmapv94gmapv9bgmap_lookup35stdpp7numbers1Nhha6eq_dec35stdpp7numbers1Zhj56eq_decmf4pair07r_cells08s_shadow06s_tick46Stdlib6NArith6BinNat1Nhn22lt04aptrpe3and0cget_meta_recpe2ex0aget_stride04optr46Stdlib6ZArith6BinInt1Zhs13addmf3fstmf3snd06active05m_memhs13mulhs13submf3naths12lemf4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~ihc5blockhs12lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I3HCW~~~~~~in04ALLCin09ENTRY_RELihcbAREACH_from79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~it83IST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~ji6eagent_reserved0asize_classhs13powk64Npos35stdpp9bitvectorbdefinitionsjp42bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~jr73mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~kg16PState3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskk7dmachine_state3h5LinuxProcessSemantics5Riscv7Preludekof5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~kre5asegs06regionjp4bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~li19malloc_fp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ln04cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lr48rw_cells0ec_mmap_counter03ctx06r_basekg15ps_fakg14ps_mkg15ps_somf4Nonemf4consmf3nilmf4unitpe2orin07as_inv279OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~mld3rdvji64mrepji68ticks_okjr77auxv_okjr7bbrk_link_psjr78pans_memjr7bpres_exceptli14mrelli17slot_okli19unk_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMalloc_iface~~~~~~nh76MEDTABnh7cmedtab_cellsln02C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~nnc3mkRnnc3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ns62MSns66ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~oh37mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ol87seg_rom09s_regionsr75emptyjp47Z_to_bvv9agmap_emptyjr75implT01Min08as_post2in07as_pre279OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentfAllocSlot_iface~~~~~~ov08AS_STACKji6h0alloc_slot_entrynh73AGP0dalloc_ceiling0aalloc_slot08full_lay07LActive07m_avail0bm_set_avail04meta05queue08upd_metamf4bool04UNITmf4andb04PGSZ09halve_big0ahalve_even07med_cnt0esmall_cnt_pick05usagehs13divhs13eqbhs14landhs13lebhs13ltb99OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I3HCW3AGB~~~~~~qj05as_kq02IB06EUndef07UBadPtr07ag_tail02ev09free_meta07lh_nest0cm_set_maplen0dsize_to_class07slot_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~qtd4SVisqj07ag_cnt1qj07ag_bodyqj07ag_mmapqj07ag_nest79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W1~~~~~~rke6as_grp0aalloc_meta" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Record ENTRY_REL (st0 st : mstate) : Prop := mkER {
  er_shadow : s_shadow st = s_shadow st0;
  er_groups : forall b, is_Some ((s_groups st) !! b) <-> is_Some ((s_groups st0) !! b);
  er_gregions : forall rid r, r_kind r = RKGroup -> ((s_regions st) !! rid = Some r <-> (s_regions st0) !! rid = Some r);
  er_mrel : mrel st0 st;
  er_mem : forall q, m_mem (get_meta_rec st q) = m_mem (get_meta_rec st0 q);
  er_geom : forall q, m_mem (get_meta_rec st0 q) <> None ->
      get_stride (get_meta_rec st q) = get_stride (get_meta_rec st0 q)
      /\ m_last_idx (get_meta_rec st q) = m_last_idx (get_meta_rec st0 q)
      /\ m_sizeclass (get_meta_rec st q) = m_sizeclass (get_meta_rec st0 q);
  er_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st0 q)) i || Z.testbit (m_freed (get_meta_rec st0 q)) i = true;
  er_areas : forall a, is_Some ((s_areas st0) !! a) -> is_Some ((s_areas st) !! a)
}.

(* [comment removed for export] *)
Definition ALLC : ltac2:(zQ "10!je>2st$0P") := ltac2:(zQ "h40!lf!m3!m7!o7!oe!p5!r2!s3!td!ub!hg5!hgc!hib!hk6!hl0!je!hl7!hm0!hma!hoa\2st$f>3rid$0>2sh$2>1o$1>1v$1>1t$0>0@3$6@1$5$2@6$7$0$2@4$a$0$c$8$2@4$b$0$c$8$2^5@1$h1^6@2$4$2^4>0@3$6@1$5@2$3$1$0@6$7$1@2$3$1$0@4$a$1$d$9@2$3$1$0@4$b$1$d$9@2$3$1$0^4@1$h0^5@2$4@2$3$1$0@4$e$1$0^3^2@2$h3^3@1$h2^8").

(* [comment removed for export] *)
Definition ret_span : ltac2:(zQ "30!m3!lf!je>3st1$2>2sc$0>3idx$0>3rid$1>1S$0>3len$0P") := ltac2:(zQ "h20!m3!hp0!r2!hp6!lf!hpc!oe!hqa!hqf!hrb!ht9!hu0!hu6!huc!hv4!je!hvb!ig2\3st1$f\2sc$0\3idx$0\3rid$4\1S$0\3len$0@2$7$1\1g$1@2$7$1\1b$1@2$3@3$2$9@2$d^8^7@2$6$1^2@2$3@3$2$9@1$e@2$5^8^2@2$6$1^1@2$3@3$2$4^5@3$b$4$0^1@2$3@3$2$0^4@2$a@2$a@3$c$4$0^1+h0@2$h0@1$8@2$5^8^2^6@3$2$0^3@2$h1@1$8@2$5^8^2+4").

Record as_inv2 (st0 st st1 : mstate) (sc idx : Z) : Prop := mkAI {
  ai_act : forall c, 0 <= c < sc -> active st1 c = active st c;
  ai_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  ai_tick : s_tick st1 = s_tick st;
  (* [comment removed for export] *)
  ai_fresh : 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o v t, S <= o < S + len -> (r_cells (get_shadow st1 rid)) !! o = Some (v, t) -> (t < s_tick st1)%N;
  (* [comment removed for export] *)
  ai_virgin : s_regions st0 = ∅ -> 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o, S <= o < S + len ->
        (r_cells (get_shadow st1 rid)) !! o = None /\ (r_hav (get_shadow st1 rid)) !! (o / 16) = None
        /\ (r_havp (get_shadow st1 rid)) !! (o / 4096) = None
}.

Definition as_pre2 : ltac2:(zQ "30!m3!je!ig9>3st0$1>2st$1>2sc$0>3req$0>4fuel$2P") := ltac2:(zQ "h20!hp6!igf!ih5!m3!im1!je!ima!ig9!hqa!ir4!irc!is9!jhf!jm8!jna!ht9!hvb!jo6\3st0$5\2st$5\2sc$3\3req$3\4fuel$7@2$0@2$8@1$2$4\2LB@1$2$4@2$0@4$b?4HSEC$d^6^1@2$c^6^5@2$0@2$a^5^4@2$0@1$9^4@2$0@2$0@2$1Z^3@2$6^3+j0@2$0@2$0@2$1Z^2@2$6^2@2$h1+2+i0@2$1@2$f^2+4@2$h0+h0@1$e^3").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition as_post2 : ltac2:(zQ "80!jod!jr1!m3!je!jva!kjd!kne!kr5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1o$4>1m$4>3st0$3>2st$3>1s$5>2lo$2>2sc$2>3req$2>3st1$3>3idx$2>2s'$5>0$6P") := ltac2:(zQ "k93!jod!jr1!hp6!hqa!m3!ht9!r2!lf!lg1!hp0!lga!lh2!hpc!hqf!je!hu6!jva!igf!hvb!td!hib!p5!kne!lm3!lqc!luf!lvb!mgb!mh0!kjd!mh8!mi1!mi9!ima!ig2!hg5!mj2!oe!mj9!hu0!mk0!hl0!o7!mk6!mkd!kr5!ml2!mq7!mqe!mr6!ms2!msd!mtc!mu8!mv7!mvf!nga!nlc!nm6!nn6!nr8!nrf!og3!og9!okd!op7!huc!hrb!oq2!jo6!oqd!or5!os0&>0@1$1@1$0#k0@1$h5@1$1@1$0#8&@2$5@2$5@1$hc^2@3$f$7$4^3+h0&@2$5~1@2$h2@1$d@2$c^h8^4^h7\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$id@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1o$h0\1m$h0\3st0$e\2st$e\1s$hd\2lo$4\2sc$4\3req$4\3st1$e\3idx$4\2s'$hd\3ms'$h6@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$3@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2@3$6$h6^h1@7$je@hf$jc^ie^id^ic^ib^h0^f^e^ia^i9@2$k7@1$0#k0^h3^d^c^b^a^9^8^7^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^6^5^4^3^he@1$jf^ie^hd@1$i4@1$1@1$0#k0^2@1$k1$8@2$2@2$k0$8^2@2$2@4$jd$8^2^h7@2$b@1$0#k0^id@2$2@4$h9$8^2@2$5@2$b@1$0#k0^ib-q4@3$i6$h8@1$jb^1@1$i8$h8@2$2@2$j2^2@2$b@1$0#k0^id@2$2@4$h9$8^2$j9$ja@2$2@2$j0^h4^2@2$2@1$j1^h4@2$2@3$j8^h4^hc^2@2$2@3$j5@4$h7^ha^h4^h7@2$b@1$0#k0^id^hb^2@2$2@2$j6^h9^h4@2$2@2$j3^h4^h2@2$2@3$6$e@1$hf^h2@1$hf^h8@2$2@3$6@2$ia$4$4@1$he^h2@1$he^h8@2$2@3$6$ib@1$i0^h2@1$i0^h8@2$2@5$ie^ha^h9^h4^h6^h3@2$2@2$2@2$h1Z@1$ha@1$hb^h4@2$i1@1$ha@1$hb^h4@2$k5+2+i0@2$ic@3$6$4^h3-1@2$2@2$h1Z^h3@2$3$9\1g$9@2$3$9\1b$9@2$3$a\1r$a@2$2@3$6$k3@2$k2^h7^h9@2$i5$9^3@2$2@6$j7^h7^3^2^1^h6^h8@2$2>1a$4>0@2$2@2$h1@2$i2~2+4^1@2$i1^1@2$i2@2$5~2@1$d@2$c^h8^4+4@5$h7^hf^h9^hc@2$b@1$0#k0^j2^2>0@3$6@4$i3$7$h4$h3$a@1$k4^hd@2$k6@4$i3$7$h4$h3$a@4$k8$7$h4$h3$a@3$6$4@5$if$h0$j4^i0^h8@4$i9$7$4@3$i7$7$4^3@2$5@2$5@3$f$7$4^3@2$5+h0@2$h2@1$d@2$c^h8^4^h7-3Z").

Definition alloc_slot_stmt2 : ltac2:(zQ "10!ig9>4fuel$0P") := ltac2:(zQ "ic1!jod!jr1!m3!lg1!or5!r2!je!lh2!kjd!kne!osd!jva!lqc!luf!ot6!igf!mj2!mj9!ig9!mk0!kr5!ot9!ou5!pj8!pk4!mqe!mr6!ms2!msd!nga!pl9!nlc!nm6!nn6!nr8!nrf!og3!okd!op7!pm0!pmf!pnb!ht9!ig2&@3$5@1$1@1$0#k0^id@2$4@1$0#k0^h1\4fuel$h2>1RT>1k>0$6>0$2@1$e^3>4bail@1$e^2>1o$b>1s$8>1Q>0^5>0$8>0$9P>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$b>3st0$6>2st$6>2lo$2>2sc$2>3req$2>4errv@1$1@1$0#k0>0@5$h6^6^5^3^2^if>0@2$h9^6^8>0@1$ha^7>0@3$hd^8^ie^a>0@2$hc^9^ie>0@2$hb^c@2$7@1$0#k0^ic>0@4$i3$3^d^a@2$7@1$0#k0^id>0@2$f$i7^b>0@2$f^c@2$ib@2$7@1$0#k0^if@1$h7^j7>0@4$d$3^h0@2$ia@2$7@1$0#k0^ie-q4@3$h1$c@1$i1^a@1$h3$c>0@2$i5$3^h1>0@4$d$3^h2$hf$i0>0@3$5@1$1@1$0#k0^j2@2$4@1$0#k0$he>0@3$5@1$1@1$0#k0^j2@2$4@1$0#k0+hqmi0>0~0>0~0>0>3st1$6>3idx$2>2s'$8>3ms'$9>0@he$h5^jc^jb^ja^j9^j5^j4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^hd^hc^jf^hb^ha^h9^je^h8^h7^h6^4^3^2^1@7$a?5HCEIL^k3^k0@2^k2^5^4^3^je^2@7$a?5HCEIL^jf^jc@8$i8^jf$i9^k0^h6^h4^h3^je^jd^jb^ja@7$i4@hf$i2^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha@2$4@1$0#k0$h8^h9@1$h0@1$1@1$0#k0^h8@1$i6$3").


(* [comment removed for export] *)
(* [comment removed for export] *)
Section AGB.
Context {R : Type}.
Variables (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_kq : ltac2:(zQ "30!ot6!je!hrb>3st2$1>2go$2@1$0?1R") := ltac2:(zQ "c0!je!p5!hp0!po5!ot6!poe!pp7!pq4!hrb!pqa!pr1!ig2\3st2$0\2go$8M1\2go@1$1$2@1$4?1R^1\1g$2=3st3$0@3$a^1\1r$7@2$6@2$b@1$5^1+1^1^3@6$9?1R@1$3?2sc^2^1\3st4$0@2?1k^1Z?4bail@2?1k^2-1").

(* [comment removed for export] *)
Definition ag_body (st : mstate) (m : aptr) : Malloc.M R :=
  let size := UNIT * size_class sc in
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : Malloc.M R := ag_tail full_lay st sc m p cnt active_idx as_kq in
    if PGSZ / 2 <? size * cnt + UNIT then
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest full_lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail.

(* [comment removed for export] *)
Definition ag_cnt1 : ltac2:(zQ "20!m3!je>2st$1$0") := ltac2:(zQ "h30!m3!prb!ps2!hvb!ps8!psf!pt5!pu0!puc!je!jna!pv5!qg5!ht9!qgc!qh3!qha!qi2!qi9\2st$9=4size$0@2$3$2@1$a?2sc=6usage0$0@2$c^2?2sc=3cnt$0M1\0$1$0@2$h2?2sc+9@2$b?2sc^1@3$6N8@3$7N8@1$8@2$h0?2sc+3^1^2M1\0$1$0@2$4@2$f^1+1@2$h1@2$d@2$3^3^1$2@2$e$5+2+2^1").

Definition ag_mmap (st : mstate) (m : aptr) (cnt : Z) : Malloc.M R :=
  let size := UNIT * size_class sc in
  let usage0 := usage st sc in
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) cnt ai as_kq).

Definition ag_nest : ltac2:(zQ "40!m3!ot6!hp0!je>2st$3>1m$2>3cnt$0@1$1?1R") := ltac2:(zQ "hd0!m3!hp0!je!ps2!pnb!hvb!ig2!prb!p5!qn8!qo1!ot6!ht9!mj2!qo5!qod!huc!qp6!pmf!qpf!qq3!qqe!qr7!jna!qs5!qt4!pr1!rha!qi9\2st$2\1m$1\3cnt$0=4size$0@2$5$3@1$h7?2sc=1j$0@1$h8@2$6@2$c$3@2$5^2^1$a@8$h2?1R$4?1f^5^1@2$6@2$c$3@2$5^3^2$a\3st1$2\3idx$0M7\0$7@1$b?1R@2$hc^1Z@5$h4?1R^6^2\3st2$2@2$9^1@1$d$1?4bailM8\1x@1$8$1@1$b?1R@2$h0^2^3\1g$1=1p$1@3$h9^3^1^2=3st2$2@7$h5$4^4^2^3^5^6^7=3st3$2@3$ha^9@1$h6Z^1@9$h1?1R$4^1?2sc^a^3^9@2$6^9+1$9@5$hb$h3$0?1R@1$e$f\0$0?4bail?4bail").

Lemma ag_body_eq : ltac2:(zQ "h00!ri2!prb!ot6!ps2!hvb!r2!rid!rj8!rk3!psf!hp0!je!jna!ht9!qgc!qi9>2st$b>1m$a@3$5@1$2?1R@2$6^2^1M1\0$1@1$2?1R@2$f@2$e$9+2@2$d@2$4@2$4$3@1$c?2sc@1$0^2$3@3$7^2^1@1$0^2@3$8^2^1@1$0^2").
Proof. intros st m. reflexivity. Qed.

Lemma as_grp_eq : ltac2:(zQ "a0!p5!ot6!hp0!je!r2!rid!rof!rp9!pnb!hrb>3st1$3@3$4@1$1?1R@8$6?1R$8?1f?2sc?3req?1k?4bail^1@4$7?1R^1\2st$3\2mo$9M0\2mo@1$0$2@1$1?1R^1\1m$2@2$5^3^1@2?1k^2-1?4bail").
Proof. intros st1.
  unfold as_grp, alloc_group, ag_body, as_kq. f_equal.
Qed.
End AGB.

End HCW.

