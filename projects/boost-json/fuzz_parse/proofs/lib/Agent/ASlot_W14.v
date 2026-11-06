(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc2lehc3pow37Corelib4Init5Logicjf3andjf2eqhc4landhc2lthc3mulhc3addhc3lor04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_free~~~~~~o23sxv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~se2wzhc6modulohc6shiftl35stdpp9bitvectorbdefinitionshi77Z_to_bvhi72bvhi78bv_swrap01N37Corelib4Init9Datatypeshm44prodhm43sndhm43fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hp2aget_shadow25stdpp9countablehtebZ_countable35stdpp7numbers1Zhve6eq_dechm44Somehm46optionhm44pairjf2exhp27Unknownhp29cell_readhp27cellvalhp29hdr_havochp26mstatehp27r_cellshp26s_tick46Stdlib6NArith6BinNat1Nio72lt25stdpp4baseiq56lookup25stdpp4gmapirb4gmapirbbgmap_lookup89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9ASlot_W144TAIL~~~~~~ite3stAhp29set_usagehp25usagehp24metahp24aptrhm44Nonehp26mkMetaite4recAite3stBhp28put_metaite3stChp29put_grouphc3subite4recFite3stDite3stEhp2aset_activehp28upd_metahp2bm_set_availhp29mask_uptohp29add_slotshp2cget_meta_rechp2aget_stridehp27m_availhp2em_set_freeablehp2bm_set_freedhp2em_set_last_idxhp29m_set_memhp2am_set_nexthp2am_set_prevhp2fm_set_sizeclass35stdpp7numbers1Nkoa6eq_dechp29set_slotshtebN_countablehteeprod_countable25stdpp9decidablekt3bprod_eq_dechp24optrite5stFinite8st_model" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_high_low : ltac2:(zQ "80!h9!j4!j9!l3!l9!le!m5!ma>1x$0>1k$0>1y$0>0@2$1Z^3>0@2$1Z^3>0@2$3@2$1Z^3@2$6^3@2$2+2^4@3$4$0@2$5@2$7^6@2$2+2^5^4Z").
Proof. intros x k y.
  intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [LT|GE].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_shl_small : ltac2:(zQ "90!h9!j4!j9!ma!l3!l9!n0!n6!m5>1x$0>1k$0>1y$0>0@2$1Z^3>0@2$1Z^3>0@2$4@2$1Z^3@2$8^3@2$2+2^4@3$5$0@2$7@2$3^6@2$2+2^5^4@2$6@2$3^6@2$2+2^5^4").
Proof. intros x k y. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.

Lemma lor_small_shl : ltac2:(zQ "90!h9!j4!j9!ma!l3!l9!n0!n6!m5>1x$0>1k$0>1y$0>0@2$1Z^3>0@2$1Z^3>0@2$4@2$1Z^3@2$8^3@2$2+2^4@3$5$0@2$7^4@2$3^6@2$2+2^5@2$6@2$3^6@2$2+2^5^4").
Proof. intros x k y. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.

Lemma land_pg_mask : ltac2:(zQ "80!h9!ma!l3!l9!le!j4!m5!j9>1q$0>0@2$2@2$5Z^1@2$6^1@2$7+2+j4@3$3$0@2$4@2$1+hgg0^2+vvvvvvvvvvvvvgg0@2$1+hgg0^2").
Proof. intros q.
  intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hdr_byte_facts : ltac2:(zQ "71!l3!le!h9!j4!n6!m5!l9&@2$4@2$1^4+vvvvvvvvvvvvvvu0^3>1x$2>2ai$2>0@2$0@2$3Z^2@2$5^2+hg0>0@2$0@2$3Z^2@2$5^2+i0@2$0@2$0@2$3Z~0@2$5~0+hg0@3$6$2@2$1~0+hf^3").
Proof. intros x ai.
  intros Hx Hai.
  assert (E : Z.land x 18446744073709551584 = Z.land x 224).
  { replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    rewrite <- !Z.land_assoc. reflexivity. }
  rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
  split.
  - change 256 with (2^8). apply lor_lt_pow2; lia.
  - rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
    change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sllw2_word : ltac2:(zQ "f0!nc!l3!l9!h9!s8!hh0!n0!j4!m5!hh5!j9!hhe!hk4!hkf!hl5>1i$3>0@2$1@2$7Z^1@2$8^1+i0@3$2@1$d@1$0#k0@2$c@1$0#k0@2$e@1$0#i0@2$b+2@2$9^2+i0@1$5@1$4@2$a+2@2$6^2+1").
Proof. intros i.
  intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
  replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_old : ltac2:(zQ "hd0!h9!hm1!hnc!ho4!l9!hob!ht0!n0!huf!igf!ih9!ii1!iib!l3!ij3!ij8!ik3!il0!ilb!im8!in2!ind!ipf!j4!m5!hh5!ir1!is7!isf>2st$h3>1b@2$2$1$0>1o$0>0@3$4$0@2$h9@3$3$1$0^2+h0Z>0@2$d@2$h7Z^2@2$h8^2+c>0>1v$0>1t$1>0@3$4@1$b@2$2$0$1@6$ha$0@2$2$0$1@4$hb$0$9$8@2$2$0$1@4$hc$0$9$8@2$2$0$1@2$7@3$3$1$0^6^5@1$h4@2$6^7@3$5$1$0^6@2$a@2$2$0$1@4$c$0$1^2^1@2$h6^2@1$h5^8@2$e$0\1h$0@3$4$h1@2$h0@2$6@2$h2^6^7@3$5$1$0^6@2$7@3$3$1$0^6^5@1$f^1").
Proof.
  intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id].
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  unfold hav_add. unfold stale. cbn [existsb fst snd].
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
  - specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
    cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
  - cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!jt8@1$0?2ai").
Let FR : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!jt8!jp3@2$1@1$0@2$1?3cnt+1@1$0?2ai").
Hypothesis SC : ltac2:(zQ "30!l3!j4!m5@2$0@2$1Z?2sc@2$2?2sc+j0").
Hypothesis CNT : ltac2:(zQ "20!j4!l3@2$1@2$0+1?3cnt@2$0?3cnt+i0").
Hypothesis AI : ltac2:(zQ "30!j4!l3!jp3@2$1@2$0Z?2ai@2$0?2ai@2$2?3cnt+1").
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : ltac2:(zQ "60!jl2!jka!l9!jv2!jk2!jla@3$2$4@2$3?3stT?2mt@9$5@1$0$1@1$0$1@1$0$1ZZZZZ?2ml").
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : ltac2:(zQ "40!ho4!hm1!h9!j4@2$3Z@3$0$1$2?1p").
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition stA : ltac2:(zQ "10!im8$0") := ltac2:(zQ "10!ilb@2$0?1p?3stT").
Definition stB : ltac2:(zQ "10!im8$0") := ltac2:(zQ "40!ji5!jic!jj9!n0@3$1?2sc@2$3@2$2?3stT?2sc?3cnt$0").
Definition recA : ltac2:(zQ "10!jk2$0") := ltac2:(zQ "40!jka!jl2!ih9!jla@9$3@1$1$0@1$1$0@2$2$0?1p?2AV?2FRZZZ?2ml").
Definition stC : ltac2:(zQ "10!im8$0") := ltac2:(zQ "30!jm4!jmc!jn3@3$2?2mt$0$1").
Definition stD : ltac2:(zQ "10!im8$0") := ltac2:(zQ "40!ih9!jnf!jka!jo6@4$3?1p@2$0$2?2mt?2ai$1").
Definition recF : ltac2:(zQ "10!jk2$0") := ltac2:(zQ "40!ih9!jka!jp3!jla@9$3@2$0$1?2mt@2$0$1?2mt@2$0$1?1p@2$2?2AV+1?2FR@2$2?3cnt+1+1?2sc?2ml").
Definition stE : ltac2:(zQ "10!im8$0") := ltac2:(zQ "30!jp9!jq1!jn3@3$2?2mt$0$1").
Definition stFin : ltac2:(zQ "10!im8$0") := ltac2:(zQ "40!ih9!jq8!jka!jqf@3$3?2sc@2$0$2?2mt$1").

(* [comment removed for export] *)
Definition st_model : ltac2:(zQ "10!im8$0") := ltac2:(zQ "ha0!im8!ih9!jka!jp3!jk2!jrd!h9!js9!jt8!ju5!jv2!kg2!ilb!kh0!khb!kid!kjc!kke!klb!km9!kn7!jo6!jqf!jic!jj9!n0=2st$0@2$c?1p?3stT=3st1$0@3$h7?2sc@2$h9@2$h8^1?2sc?3cnt^1=5avail$6@1$8?2ai=5freed$6@2$3@1$8@2$3?3cnt+1^1=3st2$0@3$5?2mt\1r$4@2$h4?2sc@2$e+1@2$h0@2$3?3cnt+1@2$h1@2$1$2?1p@2$f^2@2$7^3^1^3=3st3$0@4$h5?1p@2$1$2?2mt?2ai^1=3st4$0@5$9?2mt?1p@1$b@2$a^1?2mt?3cnt^1=3st5$0@3$5?2mt\1r$4@2$7@2$3@1$d^1+1^1^1=3st6$0@3$5?2mt\1r$4@2$h3@2$1$2?2mt@2$h2@2$1$2?2mt^1^1@3$h6?2sc@2$1$2?2mt^1").

Lemma mask_upto_range : ltac2:(zQ "60!j4!l3!jt8!j9!h9!m5>1k$4>0@2$1@2$0Z^1@2$0^1+hf@2$1@2$1@2$0+1@1$2^2@2$5@1$2^2@2$3+2+i0@2$0@2$3+2^2@1$2^2").
Proof. intros k.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

Lemma AV_FR_range : ltac2:(zQ "60!jp3!l3!j4!m5!j9!jt8@2$1@2$1@2$2+1?2AV@2$3?2AV@2$4+2+i0@2$1@2$1@2$2Z@2$0@1$5@2$0?3cnt+1?2AV@2$3@2$0@1$5@2$0?3cnt+1?2AV@2$4+2+i0@2$1@2$2Z@2$0?2AV+1@2$3@2$0?2AV+1@2$4+2+i0").
Proof.
  pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (mask_upto ai <= mask_upto (cnt - 1)).
  { unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  unfold AV, FR. lia.
Qed.

Lemma rec_set_slots : ltac2:(zQ "h00!h9!jka!hm1!jv2!kpb!igf!hnc!l9!jk2!im8!kq5!kr2!huf!ks1!ku4!is7>2st$9>1v@4$f$1@4$e$2$4$0$5@6$d$2$4$b$0$5$c@2$6$1$0>1q$1@3$7$8@2$3@2$a^2^3^1@2$3^3^1"). Proof. intros st v q. reflexivity. Qed.
Lemma rec_put_group : ltac2:(zQ "80!jka!jv2!l9!h9!jk2!im8!kv3!jo6>2st$5>1b$0>1g$6>1a$3>1q$0@3$2$4@2$1@4$7^4^3^2^5^1@2$1^5^1"). Proof. intros st b g a q. reflexivity. Qed.
Lemma rec_hdr_havoc : ltac2:(zQ "60!jka!jv2!l9!ilb!jk2!im8>2st$5>1b$0>1q$0@3$2$4@2$1@2$3^2^3^1@2$1^3^1"). Proof. intros st b q. reflexivity. Qed.

Lemma st_model_eq_rec : ltac2:(zQ "60!jv2!l9!kvb!lg4!jka!jk2>1q$4@3$1$5@2$0$3^1@2$0$2^1").
Proof. intros q.
  unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
  rewrite !rec_set_active.
  destruct (decide (q = mt)) as [->|NE].
  - rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
    unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
    replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    change (Z.land 1 1) with 1. reflexivity.
  - rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
End TAIL.
(* [comment removed for export] *)
