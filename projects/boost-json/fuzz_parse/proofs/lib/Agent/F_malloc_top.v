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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface F_malloc_join F_malloc_small F_malloc_entry F_malloc_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr37Corelib7Numbers7BinNumsk41Z06mstate46Stdlib6ZArith6BinInt1Zm93addk41N37Corelib4Init9Datatypesob6optionob4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~r33memob4pairob3sndob3fstm93mulob4Some79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~hhc3rdvr38pans_mem0aenframe_atob4bool37Corelib4Init5Logichob2eq0cget_meta_rec05havocm94landm93subr34mrun02IB01M04UNIT0cenframe_full02ev08fold_off0aget_stride05m_mem04optr03ret79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~ih54SRetm93divm93eqb35stdpp7numbers1Nim66eq_dec35stdpp7numbers1Zio16eq_dechob3and25stdpp9countableiq3bN_countable25stdpp4gmapis34gmapiq3bZ_countableiq3eprod_countable25stdpp9decidableiv8bprod_eq_dec07s_areas05s_ctx08s_groups07s_metas0as_next_rid09s_regions0as_reserved07s_slots05stripob4list04area04ghdr04mctx04meta06regionm96modulom92le" s.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma follow_steq {R} (t1 t2 : Malloc.M R) : steq t1 t2 -> forall ans, follow t1 ans = follow t2 ans.
Proof.
  induction 1 as [r | e k1 k2 Hk IH]; intros ans; [reflexivity|].
  cbn. destruct e; try reflexivity; destruct ans; try reflexivity; apply IH.
Qed.

Lemma follow_sbind {R S} (t : Malloc.M R) (f : R -> Malloc.M S) :
  forall ans x y, follow t ans = Some x ->
  (forall ans', follow (f x) ans' = Some y) ->
  follow (sbind t f) ans = Some y.
Proof.
  induction t as [r | e k IH]; intros ans x y H Hf.
  - cbn in H. inversion H; subst. rewrite sbind_ret_l. apply Hf.
  - rewrite sbind_vis. cbn in H |- *. destruct e; try discriminate; destruct ans as [|a ans]; try discriminate; eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma mrun_enframe_full : ltac2:(zQ "i42!je!ld!m1!o1!o7!q3!qc!v6!vc!hg3!hg9!hgf!hh5!hm6!hmd!hn8!ho4!hpf!hq5!hr3!hra!hs1!hs7!hse!ht2!ht5!htb!hu9!hud!hv7!ig3!iga!ih0!il2!ila!im0&@2$3@3$9$4$1^6@2$3+h0@2$b^1^5&@2$3~0-2>1o$7>2st$2>1g$0>1b$0>3idx$1>1n$1>3ctr$1>0@3$h1$hf@1$he@2$h2^6^5@2$c$0^4=6stride$1@1$hd@2$h2^7^6=3off$1@2$hcMh0\0$h0$1@2$i3@5$d$7$e^9^8@4$8$4$1@3$a$4$1^6@2$3~0-3Z@2$h4^3+vf@2$h4@2$3@2$3@5$d$7$e^9^8@4$8$4$1@3$a$4$1^6~1@2$b+hg0@5$d$7$e^9^8@4$8$4$1@3$a$4$1^6@2$3~1+1+1+vf@2$i2@2$h5@2$h5^1$h7^4$h9@3$h1@1$h8@2$6$7@2$6$2@1$5$0@3$h6@2$6$2@1$5$0^a@7$ha@2$6$2@1$5$0^9^8^6^5^4\3st2$2\1p$0@2$i0@2$6$2@1$5$0@4$8$2@1$5$0@3$h3^1^7^2@2$c$0^1@4$i1$hb$1@2$6$7@2$6$2@1$5$0@4$8$7@2$6$2@1$5$0^a@4$8$2@1$5$0@3$h3@3$9$2$0@5$f^9^8^6^5^1^5@3$a$2$0@5$f^9^8^6^5^1@2$c$0@3$9$2$0@5$f^9^8^6^5^1").
Proof. intros o st g b idx n ctr.
  intros Hmem stride off. unfold mrun, enframe_full, enframe_read_off.
  assert (Hp0 : slot_start' (get_meta_rec st g) idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd]. fold stride.
  rewrite (rd8_oracle pans_mem pans_mem_range).
  assert (OFFa : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = 0 -> fold_off (Z.land ctr 255) ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
  assert (OFFb : rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) <> 0 ->
     fold_off (Z.land (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) + 256 * rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) + 1) 255)
              ((stride - IB - n) / UNIT) = off).
  { intros E0. subst off. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
  clearbody off.
  destruct (Z.eqb_spec (rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3)) 0) as [E|NE]; cbn [negb].
  - rewrite (OFFa E). rewrite surj_pair_let. reflexivity.
  - rewrite (rd16_oracle pans_mem pans_mem_range). unfold aadd. cbn [fst snd].
    rewrite (OFFb NE). rewrite surj_pair_let. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strip_eq_proj : ltac2:(zQ "hd0!ld!o7!hpf!in7!ip2!ipc!je!ir4!isf!it7!iu6!jg9!m1!qc!jh8!ji1!ji8!jj2!jjb!jk7!jl2!jle!jm7!jme!jn5!jnb!jo1!jo7!jod>1a$c>1b$c>0@3$2$c@1$h6^2@1$h6^1@2$5@3$2$ha@1$f^3@1$f^2@2$5@3$2@4$8$1$3$7$hc@1$h3^3@1$h3^2@2$5@3$2$1@1$h2^3@1$h2^2@2$5@3$2@4$8$6@4$b$1$3$0$4@6$a$1$3$7$0$4$9$hb@1$h1^3@1$h1^2@2$5@3$2@4$8$6@4$b$1$3$0$4@6$a$1$3$7$0$4$9$h8@1$e^3@1$e^2@2$5@3$2@4$8$6@4$b$1$3$0$4@6$a$1$3$7$0$4$9$h9@1$h0^3@1$h0^2@2$5@3$2@4$8$6@4$b$1$3$0$4@6$a$1$3$7$0$4$9@2$d$6$0@1$h5^3@1$h5^2@3$2@1$h7@2$d$0$0@1$h4^3@1$h4^2").
Proof. intros a b.
  intros E.
  pose proof (f_equal s_ctx E) as E1. pose proof (f_equal s_regions E) as E2. pose proof (f_equal s_next_rid E) as E3.
  pose proof (f_equal s_metas E) as E4. pose proof (f_equal s_areas E) as E5. pose proof (f_equal s_groups E) as E6.
  pose proof (f_equal s_slots E) as E7. pose proof (f_equal s_reserved E) as E8.
  cbn in E1, E2, E3, E4, E5, E6, E7, E8. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma mrun_fst {R} (t : Malloc.M R) : forall o ans o1 x, follow (mrun o t) ans = Some (o1, x) -> o1 = o.
Proof.
  unfold mrun, prun. induction t as [r | e k IH]; intros o ans o1 x H.
  - cbn in H. inversion H. reflexivity.
  - cbn [eruns] in H. destruct (psel pans_mem o e) as [a|] eqn:P.
    + unfold pupd_mem in H. eapply IH. exact H.
    + cbn in H. destruct e; try discriminate; destruct ans; try discriminate; unfold pupd_mem in H; eapply IH; exact H.
Qed.

Lemma mod16_slot : ltac2:(zQ "60!ld!hpf!o1!jp5!hgf!jpe>1B$0>1s$0>2st$0>1k$0>3off$0>0@3$1$0@2$3^5+hgg0Z>0@3$1$0@2$3^5+h0Z>0@3$1$0@2$3^5+h0Z>0@2$5Z^5@3$1$0@2$3@2$2@2$2@2$2@2$2^9^8+h0@2$4^7^6@2$4+h0^5+h0Z").
Proof. intros B s st k off.
  intros HB HS HT HK.
  destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
  assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
  set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis BIG : big_stmt.

(* [comment removed for export] *)
End TOPLEVEL.

End HCW.

(* [comment removed for export] *)
