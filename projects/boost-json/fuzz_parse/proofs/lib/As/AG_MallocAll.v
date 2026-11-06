(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX SecLazy
     AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AG_MallocModel AG_Malloc2 AG_LargeModel AG_MallocLarge3
     AG_Frame AG_MallocCold AG_MallocTop AG_MallocLarge AG_WriteSet.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hc8round_uphc7rz_size46Stdlib6ZArith6BinInt1Zn23addn23max37Corelib4Init9Datatypesp64bool89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAG_MallocAll3HCW~~~~~~r57mneededhc8kMaxSizen23lebhc9kPageSizehcbcompute_reqhc9rq_neededr58mprimaryr56msz_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAG_MallocLarge3~~~~~~hl07lg_costn22lep64true37Corelib4Init5Logichqc2eqhqc3iff3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshsddmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateih55Model04Npos35stdpp9bitvectorbdefinitionsil22bvhqc3andhqc2exp64listp64prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ip05asegshc6astatehc6effectp64pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~iud4a_Zril2bbv_unsignedp64consiud4a_ALiud3a_Liud3a_Siud5a_botiud5a_ctxiud5a_fsbiud5a_thriud5a_topiud3ast79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~jp33mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jt84cellp64Nonep64Somep63nilp66option3h5LinuxProcessSemanticsfLinuxProcessSem3Runkj95mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_Frame~~~~~~kme7amframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~kr7cdepot_placedr5bmalloc_cost79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~lh5fsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_WriteSet~~~~~~lmc6acompllmc4avmxiud6ARHEAPiud4a_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~lt17AMODELXlt18awin_vislt19depot_covlt1aflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~mk25DEPOTjp3baddressable79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7SecLazy~~~~~~mpaanonvm_samehcbam_malloc_k69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~mv38restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~nje4lzokjt82CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~no53mkRno53stkno55wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~nt82MSnt86ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~oi57mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~oma7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~or48rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ovb2wzn23subn26to_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~pkb6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~poedhunspell_scfg99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAG_MallocAll3HCWdMallocAllGlue~~~~~~pt6cmalloc_gpost79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAW_MallocBase~~~~~~qjaaicpt_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsUnwind~~~~~~qob6utracep66lengthn26of_natmk25depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsDepotHash~~~~~~queadepot_hashmk25d_putiud8AFS_SIZEiud4disjn23mulmk24d_nbmk24d_sbjp35aceiln26modulon23pown22ltiud3ATPmk28d_framesmk25d_idsqob9goodframeqobbframe_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAG_MallocCold~~~~~~rs59COLD_COST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~sh56B_PRIMsh56pusageil27Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition mneeded : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "50!h9!ld!m8!oa!p0\4size$0@2$3@2$1@2$4^1+8+8@1$2^1").
Definition mprimary : ltac2:(zQ "20!qe!h9>4size$1$0") := ltac2:(zQ "40!h9!vb!hg5!hh0\4size$0@2$3@1$1^1$2").
Definition msz_of : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "60!hh6!h9!hi2!ld!hj0!oa\4size$1@2$5@2$3@1$4@1$2^1$0$0").
(* [comment removed for export] *)
Definition malloc_cost : ltac2:(zQ "10!h9>4size$0$0") := ltac2:(zQ "50!qe!h9!hjc!hk7!hp5\4size$1M0\0$0$1@1$2^1Z@1$4@1$3^1").

Lemma mprimary_iff : ltac2:(zQ "70!hq0!qe!hq5!hs0!hs6!h9!hjc>4size$5>0@2$0+1^1@2$4@3$3$1@1$6^2$2@2$0^2+vsg0").
Proof.
  intros size Hs. unfold mprimary, mneeded, kMaxSize, rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog, round_up. rewrite Z.leb_le.
  repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end.
  all: match goal with |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v end.
  all: Z.div_mod_to_equations; lia.
Qed.

Section MallocAllGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  Let st : ltac2:(zQ "10!it4$0") := ltac2:(zQ "10!ls9@1$0?1s").
  Let c := class_id (mneeded size).
  Let CHI : ltac2:(zQ "30!h9!io2!io9@1$1@2$2$0$0") := ltac2:(zQ "40!ikc!jj3!qnd!jo3@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!io2!h9@1$0$1") := ltac2:(zQ "50!ikc!jlf!jo3!qs9!jj3@6$3+pgug0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!qt3!h9!qtc@1$2@2$0$1?1T").
  Let d' : ltac2:(zQ "10!qu5$0") := ltac2:(zQ "20!rif!rjd@3$1?1d@1$0?1T?2nT").

  Hypothesis HR : ltac2:(zQ "10!lrf@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis AX : ltac2:(zQ "30!in5!mhb!mj4@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!mh0@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!isb!mo2@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!kv7@3$0?5HCEIL?1s?1d").
  Hypothesis DFS : ltac2:(zQ "70!rk6!jn1!rl2!rla!in5!rm0!rm8@2$4@4$2@1$1?1s$0@1$5?1d@2$3+h0+hggg0@4$2@1$1?1s$0@1$6?1d@2$3+8+ogg0").
  Hypothesis DCOV : ltac2:(zQ "10!mi7@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!isb!olf@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!ikc!isb!ns8!jj3@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!rn0!hq0@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!ikc!oa!hq0!jj3@2$2@2$1?2lo+rr0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!hs0!ikc!h9!rn9!jj3@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!ikc!oa!hq0!ro2!jj3@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SZ : ltac2:(zQ "40!in5!hq0!ro8!ro2@2$0@2$1+1?4size@2$2?4size@2$3+2+i0").
  Hypothesis TP : ltac2:(zQ "50!hs0!ikc!rod!pj6!imf@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis DCAP : ltac2:(zQ "60!oa!in5!rp4!rq0!hq0!ro8@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis FCH : ltac2:(zQ "d0!ikc!jj3!jo3!qe!hq5!hs0!rq9!in5!isb!jlf!rr6!oa!hq0>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!hs0!ikc!pj6!imf@3$0@1$3@1$1#k0?2a0@1$2?4size").
  (* [comment removed for export] *)
  Hypothesis ALLOW : ltac2:(zQ "30!lg7!jk9!hq0@2$2@1$0?4size@1$1?1s").
  Hypothesis PROOM : ltac2:(zQ "50!sg8!sl6!sm0!oa!hq0@2$4@2$3@1$2?2st$0$1").
  Hypothesis XTRA : if mprimary size then rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset
                    else AGAP (msz_of size) mo /\ zlen (as_sec st) < 63 * kChunksBlockCount.   (* [comment removed for export] *)
  Hypothesis OK : ltac2:(zQ "60!km5!isb!jl1!jl8!jib!nn7@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "d0!ikc!khc!hs0!ig4!isb!jl1!jl8!nj2!ns1!oh5!oq9!sma!imf@3$2$3@3$7@1$5?1s@1$6?1s?3msF@7$9@hf$8?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$b@1$0#k0+pgtj8?2fc@1$1@1$c@1$0#k0?1m@1$a$4").

  Definition malloc_gpost : ltac2:(zQ "20!ig4!ik3>4msF'$0>3mo'$1P") := ltac2:(zQ "k00!ikc!imf!in5!inc!h9!io2!hs0!io9!isb!it4!itd!iu6!jib!jj3!jk2!ig4!jk9!jl1!jl8!jlf!jm8!jn1!jna!jo3!joc!jt1!kh4!khc!ki3!kia!kj0!km5!ik3!kqc!kv7!lg7!ll9!lqd!lr7!lrf!ls9!mh0!mhb!mi7!mj4!mo2!mob!mt7!mu5!nj2!nn7!nnf!ns1!ns8!nsf!oh5!ohb!olf!oq9!ouf!pj6!hq0!pjc!pk2\4msF'$f\3mo'$i0@2$3$h8\2s'$h8@2$3$4\1U$4@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3$h9\2m'$h9@2$2@3$6$4@1$h6^h1@1$h6?1s@2$2@3$6$4@1$h4^h1@1$h4?1s@2$2@3$6$4@1$h5^h1@1$h5?1s@2$2@3$6@1$5@2$7@1$1@1$0#k0@1$1@1$0#k0@1$c^h1@1$c?1s@2$2@3$6$4@1$h7^h1@1$h7?1s@2$2@3$6$4@1$h3^h1@1$h3?1s@2$2@2$jd@2$je@1$h0?1s@1$i3?4size@1$h0^h1@2$2@5$j2$8@1$h1^h1@1$h2^h1@1$c^h1@2$hf^h3^h2@2$2@3$6$f@3$j1@1$h1^h1@1$h2^h1^h3@7$j7@hf$j4?2ra?2sp?2gp?2tp^f^e^d?2s0?2s1@1$jc^h0^c^b^a^9^8^7^6?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^5^4^3^2?1F@1$j8?2ra?2fc@1$hb@1$1@1$0#k0^1@1$ja$8@2$2@4$i7?5HCEIL^h1@3$e@2$7$4$4@4$b$4$4^h0?4size?2LB^1@2$2@2$ia^h1^1@2$2@1$ic^1@2$2@3$i9?5HCEIL^h1^h2@2$2@2$if?2mo^h2@2$2@3$id$8?2d'^1@2$2@3$i2?5HCEIL^h1?2d'@2$2@2$ib?2d'^h2@2$2@2$j9$8^1@2$2@4$j5$8^1?2lo@2$d@1$0#k0?2sp@2$2@6$i1?5HCEIL?1s?2LB@2$d@1$0#k0?2sp?1m^1@2$2@3$j6$8?1m^1@2$2@7$i5?1s^h1?1d?2lo@2$d@1$0#k0?2sp?1m^1@2$2@4$i6?1s^h1?2mo^h2@2$2@2$3@1$5@1$1@1$0#8\4junk@1$5@1$1@1$0#8@4$jb$8^2^h1@3$e$ha@2$j3@1$jf?4size^1@1$hd$ha@2$2@3$ie^1^h0?4size@2$3$4\5kaddr$4@2$3$9\4st''$9@2$3@1$5$a\2ev@1$5$a@2$2@3$6@1$he@2$7@2$7$4$9@1$5$a@3$j0?2st?4size^3@2$hc@2$7@2$7$4$9@1$5$a@4$b@2$7$4$9@1$5$a@4$b$4$9^h3^2^1@2$i4^2@1$i8^h4").

  Theorem malloc_arep : ltac2:(zQ "70!km5!isb!po4!ps5!ig4!ik3!qia>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
  Proof.
    intros K. unfold malloc_cost in ALLOW.
    destruct (mprimary size) eqn:PR.
    - (* [comment removed for export] *)
      assert (SZ' : 1 <= size /\ round_up (Z.max size 8) 8 + rz_size size <= kMaxSize).
      { split; [clear - SZ; try acb; lia|]. unfold mprimary, mneeded in PR. apply Z.leb_le in PR. exact PR. }
      eapply (malloc_arep_prim ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH
                HR AX AMX DEP DPL DFS DCOV MI ST LO HI SPA SPT SZ' TP DCAP FCH Ha0 PROOM XTRA OK VISE).
      intros msF' mo' PO.
      ndestruct PO as (s' & U & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & AL
                      & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & FR' & WM' & CP' & AVX' & BLK & ADDR & MODEL).
      apply K. nexists s', U, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. unfold malloc_cost. rewrite PR.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      { clear - AL. lia. }
      ndestruct (MODEL 0) as (st'' & ev & M1 & M2). nexists 0, st'', ev. split; assumption.
    - (* [comment removed for export] *)
      assert (SZ' : 64512 < size < 2^32).
      { split; [| clear - SZ; try acb; lia]. destruct (Z.le_gt_cases size 64512) as [LE|GT]; [| exact GT].
        exfalso. apply (proj2 (mprimary_iff size ltac:(hci; clear - SZ; try acb; lia))) in LE. rewrite LE in PR. discriminate PR. }
      destruct XTRA as (AGP & NSEC).
      eapply (malloc_arep_large ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s LB d lo size CH
                HR AX AMX DEP DPL DCOV MI ST LO ltac:(hci; clear - HI; try acb; lia) SPA SPT SZ' TP DCAP FCH Ha0 ALLOW ltac:(hci; pose proof PROOM as PR'; unfold COLD_COST in PR'; change st with (a_st s) in PR'; clear - PR'; lia) AGP NSEC DFS OK VISE).
      intros msF' mo' PO.
      ndestruct PO as (a & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & A1 & A2 & A3
                      & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & MU' & WM' & FR' & CP' & AVX' & BLK & ADDR & MODEL).
      apply K. nexists (mkAst (large_state st a size) (a_thr s) (a_ctx s) (a_fsb s) (lg_L (a_L s) (a_pa s) (as_n_reserved st) (zlen (as_sec st)))
                             ((wz (sh a), wz (msz_of size / 8)) :: a_S s) (a_Zr s) (a_AL s - lg_cost (msz_of size)) (a_top s) (a_bot s)),
                      (a + kPageSize + 2048), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [a_AL]; unfold malloc_cost; rewrite PR; clear; lia|].
      repeat match goal with |- _ /\ _ => split end; try assumption.
      ndestruct MODEL as (st'' & ev & M1 & M2). nexists a, st'', ev. split; assumption.
  Qed.
End MallocAllGlue.

End HCW.

