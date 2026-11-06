(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc6mstatehc4aptrhc4ghdr37Corelib4Init5Logicn13and01Nhc4conc46Stdlib6ZArith6BinInt1Zp52lep52lt35stdpp7numbers1Nr76eq_dec35stdpp7numbers1Zt16eq_decn12exn12orp53add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~vb3CTX25stdpp9countablehk3bN_countablehk3bZ_countablehk3eprod_countable25stdpp9decidableho4bprod_eq_dec37Corelib4Init9Datatypeshq44Somehq46optionn12eqvb9meta_slothc8s_groups25stdpp4basehua6lookup25stdpp4gmapig04gmapig0bgmap_lookuphccget_meta_rechc7m_availhcam_freeablehc7m_freedhcam_last_idxhc5m_memhcbm_sizeclassp53pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W0~~~~~~inc6ta_rel89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W93HCW~~~~~~is73gmf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgenteMallocFacts_AS~~~~~~jh35mw_okhc4optrhcddecay_bounceshcaset_bouncep53subhc6activehc4metahc8upd_meta" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ta_fp : ltac2:(zQ "20!h9!la>2st$1>2lo$0>2sp$0>1a$0P") := ltac2:(zQ "hb0!h9!m3!ma!o5!ob!oe!qd!r2!s8!u2!ub!v0!v5!hjd!hl4!hm3!hn2!hp5!hrc!hs4!hse!ht3!la!htf!hv6!igc!ih4\2st$h6\2lo$0\2sp$0\1a$0@2$b@2$3@2$6^3^1@2$7^1^2@2$b@2$3@2$6$d^1@2$7^1@2$c$d+jq0@2$b@2$a$1\1q$1@2$3@2$h5^5^1@2$3@2$6@2$5^5^1^2@2$7^2@2$c@2$5^5^1+i8@2$a$1\1b$1@2$a$2\2gh$2@2$3@3$h4@1$h3$2@6$h8$1$2@4$h9$1@4$h1$4$8$0$9@6$h0$4$8$e$0$9$f$2@4$ha$1@4$h1$4$8$0$9@6$h0$4$8$e$0$9$f$2^2@1$h7^6@2$h2$2^1@2$3@2$6@2$5^6^2^3@2$7^3@2$c@2$5^6^2+9").

(* [comment removed for export] *)
Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
  gmf_slot : meta_slot st g;
  gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  gmf_mw : mw_ok (get_meta_rec st g);
  gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
  gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
  gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
             /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
             /\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
             /\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
  gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.

(* [comment removed for export] *)
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmf_geom : ltac2:(zQ "h50!ii3!o5!hse!h9!oe!ij2!ijc!ik9!il3!im0!im8!la!qd!r2!in6!ird!jgc!jla!ht3!m3!jm3>2st$b>3st1$b>2sc$3>1g$h3>0@3$f^2^4^3>0@3$h0^5^3^2@2$1@2$h2^5^3@2$1@2$1@2$cZ@1$5@2$0^5^3@2$d@1$5@2$0^5^3@2$e+2+i0@2$1@2$1@2$cZ@1$7@2$0^5^3@2$d@1$7@2$0^5^3@2$e+2+i0@2$1@1$h1@2$0^5^3@2$1@3$2$h4@1$9@2$0^5^3@1$9@2$0^6^3@2$1@3$2$3@1$8@2$0^5^3@1$8@2$0^6^3@2$1@3$2$3@1$a@2$0^5^3@1$a@2$0^6^3@2$1@3$2$3@1$6@2$0^5^3@1$6@2$0^6^3@3$2$3@2$4^5^3@2$4^6^3").
Proof. intros st st1 sc g.
  intros TR GM. destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
  destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
  pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
  split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
  repeat (split; [first [assumption| lia| reflexivity]|]).
  unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma decay_cases : ltac2:(zQ "80!h9!la!hse!jma!ub!v0!jna!jo7>1c$0>2st$1@2$5@3$2$1@2$3^2^1^1@2$4$0\1v$0@3$2$1@2$3^3^2@3$6@2$7^3+7^1^2").
Proof. intros c st. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
Lemma active_decay : ltac2:(zQ "60!h9!jod!hse!jma!la!jm3>1c$0>2st$4>1i$0@3$2$5@2$1@2$3^3^2^1@2$1^2^1").
Proof. intros c st i. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma rec_decay : ltac2:(zQ "70!ii3!hse!h9!m3!jma!jp6!la>1c$2>2st$6>1q$3@3$1$5@2$0@2$4^3^2^1@2$0^2^1").
Proof. intros c st q. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma active_upd_meta : ltac2:(zQ "80!jod!jp6!hse!h9!m3!la!jm3!jpd>1g$4>1f>0$1$1>2st$5>1i$3@3$2$6@2$0@3$7^4^3^2^1@2$0^2^1").
Proof. intros g f st i. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

(* [comment removed for export] *)
Hypothesis HK1 : forall stX g3 msk k m' (t1' t3' t4' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  mrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv asegs m' -> stk asegs m' lo spv ->
  pres_except (ta_fp st lo spv) m m' ->
  implT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (wz k) a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
        F (ret_pc ra) fc None m' (seg_rom asegs)).

(* [comment removed for export] *)
End PHASE.

End HCW.

(* [comment removed for export] *)
