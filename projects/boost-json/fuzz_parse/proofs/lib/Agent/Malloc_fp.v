(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes06length03nat37Corelib4Init5Logici52eq37Corelib7Numbers7BinNumsje4Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~le7actives79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~qa6mstate35stdpp9bitvectorbdefinitionsv12bv04Some06optioni53andje1Zle2pwqa6active36Stdlib5Lists4Listhj99nth_error46Stdlib6ZArith6BinInt1Zhl92lehl92lthl96to_nat04bool04trueqa6lowbithl93powhl97testbitje1Nqa4ghdr35stdpp7numbers1Nhr96eq_dec35stdpp7numbers1Zht46eq_dec04prod03sndi52exqa4aptr25stdpp9countableig6bN_countableig6bZ_countableig6eprod_countable25stdpp9decidableik7bprod_eq_dec03fstqa8s_groupshl93add25stdpp4baseine6lookup25stdpp4gmapip44gmapip4bgmap_lookup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~ir73memqa6region79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jga2waqa6r_basei53not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~jl9bgrp_hdr_covqa7RKGroupqa7Unknownqa9cell_readqa7cellvalqaaget_shadowqa6r_kindqa5r_lenqa5rkindqabround_up_pgqa9s_regionsjl99unk_agreei52orqaeMMAP_THRESHOLDine5emptyip4agmap_emptyqacget_meta_rec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_A~~~~~~kld9sstart_ofqa2IBhl93subqaaget_strideqa7m_availqa7m_freedqa5m_memqa4optr04Nonele5lr_loir78alloc_fpir7afresh_addrjl9efree_slot_addrjl9cgrp_hdr_addrjl9cnew_reg_addrjl94mrelhl96modulohl93opp" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : mrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma actives_length : ltac2:(zQ "70!h8!i0!j9!l7!q0!u8!hge>2st$5@3$2$1@2$0@1$6@1$3#k0@1$4^1Nj0").
Proof. intros. unfold actives. rewrite length_map, length_seq. reflexivity. Qed.

Lemma actives_nth : ltac2:(zQ "f0!l7!hge!hh3!hh9!hi1!j9!hi7!q0!hib!hj0!u8!hkc!hn1!hn7!hnd>2st$a>2sc$6>0@2$4@2$cZ^1@2$d^1+j0@3$5@1$3@1$1@1$0#k0@3$b@1$1@1$0#k0@1$7^3@1$e^2@2$2@1$1@1$0#k0@2$8^3@2$9^3^2").
Proof.
  intros st sc Hsc. unfold actives. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lowbit_testbit : ltac2:(zQ "80!hi7!j9!ho7!hod!hp3!hn1!hpc!hq3>1v$0>1k$0>0@2$5Z^1>0@3$1$0@1$4^3@2$6+2^2@3$1$2@2$7^4^3$3").
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grp_hdr_cov : ltac2:(zQ "30!hqe!hi7!u8>2st$2>3rid$0>3off$1P") := ltac2:(zQ "ha0!hqe!hi7!hr2!hsa!hu5!huf!hi1!hv5!j9!hva!hvf!ih7!ii6!ij5!il8!hh3!im7!hh9!u8!imc!in7!hn1!hn7!ioa!iq0!iq8\2st$h2\3rid$0\3off$1@2$9@2$5$0$1\1b@2$5$0$1@2$9$2\2gh$2@2$6@3$8@1$h1$2@6$h7@2$5$0$1$2@4$h8$a@4$e$0$3$1$4@6$d$0$3$b$1$4$c$2@4$h9$a@4$e$0$3$1$4@6$d$0$3$b$1$4$c$2^2@1$h3^5@2$f$2^1@2$6@3$8$0@3$h0$0$1^2^4@2$6@2$h5@3$7$0$1^2^3@2$h6^3@2$h4@3$7$0$1^2+c").

(* [comment removed for export] *)
Definition unk_agree : ltac2:(zQ "20!iva!u8>2st$1>1o$0>2m1$0P") := ltac2:(zQ "i10!jg1!j9!hqe!hh9!hi7!iva!jk4!jka!in7!ih7!hsa!hh3!hi1!jl3!l7!jpb!jqa!jr4!jre!jsa!jt4!u8!ju1!jua!jv2!jva!kg8!hn1!hn7!ioa!hge!iq0!iq8\2st$h5\1o$5\2m1$5>3rid$2>1r$0>3off$4>1h$4>0@3$1@1$3$0@6$hd$2$0@4$hf$2$a$9$0@4$i0$2$a$9$0^4@1$ha^7@2$b$0^3>0@3$1$h8@1$h6^4$h0>0@2$c@2$hbZ^4@2$hc^4@1$h9@1$h7^5>0@3$1$h3@2$h2@2$h4^a^7^5@1$h1^4>0@1$d@3$f^b^8^6@3$1@1$3@1$he@1$e#8@1^a@1$6@2$8@1$7^8^7@1^b@1$6@2$8@1$7^8^7").

Lemma unk_agree_refl : ltac2:(zQ "30!iva!kh4!u8>2st$2>1m$0@3$1^2^1^1").
Proof. intros st m rid r off h _ _ _ _ _. reflexivity. Qed.

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : mrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.
End SLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition expo_cond : ltac2:(zQ "20!hi7!u8>2st$1>1n$0P") := ltac2:(zQ "e0!hqe!jg1!ih7!hsa!iq0!j9!ki1!hi7!ki6!u8!kg8!hn1!kj7!kk0\2st$9\1n$7@2$6@2$b$8^1@3$5@4$4$0$3$2$1@1$a^2@2$c@4$4$0$3$2$1@4$d$0$3$2$1").

Record slot_ok (st1 : mstate) (g b : aptr) (r : region) (idx n : Z) : Prop := mkSO {
  so_mem : m_mem (get_meta_rec st1 g) = Some b;
  so_reg : (s_regions st1) !! (fst b) = Some r;
  so_kind : r_kind r = RKGroup;
  so_b0 : 0 <= snd b;
  so_b16 : snd b mod 16 = 0;
  so_idx : 0 <= idx <= m_last_idx (get_meta_rec st1 g);
  so_li : m_last_idx (get_meta_rec st1 g) < 32;
  so_span : snd b + 16 + get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1) <= round_up_pg (r_len r);
  so_s16 : 16 <= get_stride (get_meta_rec st1 g);
  so_smod : get_stride (get_meta_rec st1 g) mod 16 = 0;
  so_s31 : get_stride (get_meta_rec st1 g) - 4 - n < 2^31;
  so_n : 0 <= n;
  so_fit : n + 4 <= get_stride (get_meta_rec st1 g);
  (* [comment removed for export] *)
  so_nogrp : forall b' gh, (s_groups st1) !! b' = Some gh -> fst b' = fst b ->
     snd b' + 9 <= snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4
     \/ snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 <= snd b';
  (* [comment removed for export] *)
  so_hdr0 : cell_read (get_shadow st1 (fst b)) (snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4) = Known 0;
  (* [comment removed for export] *)
  so_q16 : forall off, 0 <= off -> 16 * off + n + 4 <= get_stride (get_meta_rec st1 g) ->
     (get_stride (get_meta_rec st1 g) * idx + 16 * off) / 16 < 65536;
  (* [comment removed for export] *)
  so_slot : (s_slots st1) !! (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx) = Some (g, idx);
  so_mslot : meta_slot st1 g;
  so_avail : 0 <= m_avail (get_meta_rec st1 g) < 2^32;
  so_freed : 0 <= m_freed (get_meta_rec st1 g) < 2^32;
  so_freeable : 0 <= m_freeable (get_meta_rec st1 g) < 2;
  so_maplen : 0 <= m_maplen (get_meta_rec st1 g) < 2^40;
  so_sc : 0 <= m_sizeclass (get_meta_rec st1 g) < 48
          \/ (m_sizeclass (get_meta_rec st1 g) = 63 /\ m_last_idx (get_meta_rec st1 g) = 0 /\ 0 < m_maplen (get_meta_rec st1 g))
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_slot_addr : ltac2:(zQ "20!hi7!u8>2st$1>1a$0P") := ltac2:(zQ "i71!hi1!jg1!kke!j9!hvf!hva!hqe!hi7!jka!in7!hn1!hh3!ho7!hod!kq3!kr0!hn7!kr5!hq3!ih7!hsa!im7!hh9!ki1!jqa!krc!ks9!kt3!ktd!u8!ku5!ju1!jua!jv2!jva!kg8!ioa!iq0!iq8&@2$9@1$8^2@2$e@2$2^6^4^1\2st$hd\1a$7@2$5$4\1g$4@2$5$4\1b$4@2$5$1\1r$1@2$5$7\1i$7@2$0@3$3$he@1$hc@2$2^6^4@2$b$4^3@2$0@3$3@1$h6$1@6$i4$6$1@4$i5$6$h4$h3$1@4$i6$6$h4$h3$1@3$h5$6$7^3@1$i3^6@2$b$1^2@2$0@3$3$i1@1$hf^2$h8@2$0@2$aZ^1@2$0@2$h7@3$3$c@2$h2@1$ha@2$2^6^4^1$d@3$3$c@2$h2@1$hb@2$2^6^4^1$d@2$0@2$0@2$a@1$8^2^5@2$h0^5@2$9@1$8^2@1$i2@1$i0^2@2$0@2$a@2$h1~0$f^5@2$h0^5@2$h1@2$9~0@1$h9@2$2^6^4$f").

(* [comment removed for export] *)
Definition grp_hdr_addr : ltac2:(zQ "20!hi7!u8>2st$1>1a$0P") := ltac2:(zQ "i20!hqe!hi7!hr2!jg1!hi1!hsa!jka!in7!ih7!hu5!huf!j9!hva!hh3!hh9!hv5!hvf!hn1!hn7!ioa!ii6!ij5!il8!iq0!iq8!im7!jqa!u8!ju1!jua!jv2!jva!imc!kg8\2st$hb\1a$1@2$c@2$a$0$1\1b@2$a$0$1@2$c$2\2gh$2@2$c$3\1r$3@2$4@3$b@1$e$2@6$h3@2$a$0$1$2@4$h7$h0@4$h6$0$5$1$9@6$h5$0$5$8$1$9$h4$2@4$h8$h0@4$h6$0$5$1$9@6$h5$0$5$8$1$9$h4$2^3@1$i0^5@2$d$2^2@2$4@3$b@1$e$3@6$h3$0$3@4$h7$0$5$8$3@4$h8$0$5$8$3@3$h9$0$1^3@1$i1^5@2$d$3^1@2$4@3$b$he@1$hc^1$ha@2$4@2$4@2$h1@1$6^1^4@2$h2^4@2$7@1$6^1@1$hf@1$hd^1@2$4@2$h1@2$7@1$6^1@3$f$0$1^3^4@2$h2^4@2$7@2$7@1$6^1@3$f$0$1^3+h0").

(* [comment removed for export] *)
Definition new_reg_addr : ltac2:(zQ "20!u8!hi7>2st$0>3st'$0>1a$1P") := ltac2:(zQ "h70!jg1!hqe!ih7!hsa!hi1!hh9!j9!hva!u8!kg8!ioa!iq0!iq8!kuc!hh3!hi7!kv2!jka!jua!jva!in7!hn1!hn7\2st$8\3st'$8\1a$f@2$7$1\3rid$1@2$7$0\1r$0@2$4@3$6@1$5$0@6$a$1$0@4$b$1$3$2$0@4$c$1$3$2$0^2@1$9^4@2$e$0^1@2$4@3$6@1$5$0@6$a$1$0@4$b$1$3$2$0@4$c$1$3$2$0^2@1$9^5@1$d$0@2$4@2$h5@1$h0^1^3@2$h6^3@2$h4@1$h1^1@1$h3@1$h2^1").

(* [comment removed for export] *)
Definition malloc_fp : ltac2:(zQ "20!hi7!u8>2st$1>3st'$1>2lo$0>2sp$0>1a$0P") := ltac2:(zQ "c0!ki1!hi7!u8!jv2!j9!jl3!kva!lg6!lh4!li6!lj6!jqa\2st$2\3st'$2\2lo$1\2sp$1\1a$1@2$0@5$6\1k$3@1$5@3$4$3^1$b^4^3^2^1@2$0@3$a^5^4^1@2$0@2$8^5^1@2$0@2$9^5^1@2$7^5^1").

Record mrel (st st' : mstate) : Prop := mkMREL {
  mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
  mrel_next : (s_next_rid st <= s_next_rid st')%N;
  mrel_reserved : s_reserved st' = s_reserved st
}.

Lemma mrel_trans : ltac2:(zQ "20!lk6!u8>3st1$1>3st2$1>3st3$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. intros st1 st2 st3.
  intros [R1 N1 S1] [R2 N2 S2]. split; [| lia | congruence].
  intros rid r H. ndestruct (R1 rid r H) as (r' & H' & K' & B' & L'). ndestruct (R2 rid r' H') as (r'' & H'' & K'' & B'' & L'').
  exists r''. repeat split; auto; try congruence. lia.
Qed.

Lemma round_up_pg_eq : ltac2:(zQ "60!hi7!j9!jva!in7!lke!ll8>1x$0@3$1$0@1$2^1@2$3^1@2$4@1$5^1+hgg0").
Proof. intros x. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_mono : ltac2:(zQ "30!hi7!jva!hn1>1x$0>1y$0>0@2$2^2^1@2$2@1$1^3@1$1^2").
Proof. intros x y. intros H. rewrite !round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : MFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.
End FASTFACTS.
