(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N37Corelib4Init5Logichc2eq35stdpp7numbers1Nj56eq_dec01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~l23mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~pb9unk_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~u9aget_shadowu96mstateu98s_groupsu99s_regions25stdpp9countablehl4bN_countable25stdpp4gmaphn44gmap35stdpp7numbers1Zho86eq_decu94aptru94ghdru96regionu96shadowhl4bZ_countablehl4eprod_countable25stdpp9decidablehu4bprod_eq_dec37Corelib4Init9Datatypesig46optionu96r_baseig44Some04Nposu95r_lenu9bround_up_pg46Stdlib6ZArith6BinInt1Zil32le25stdpp4basein16lookup35stdpp9bitvectorbdefinitionsio72bvhn4bgmap_lookupig44listhc3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~is7ddisjoint_fromis73ivlis75munchu97RKGroupu96r_kindu95rkindil33addil33powu9as_next_ridu9as_reservedig44prodpb4mrel" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unk_agree_ext : ltac2:(zQ "h40!h9!j0!k6!kf!p5!td!hi7!hj4!hjd!hk8!hm5!ho0!hp9!hq3!hqa!hr1!hra!hs3!ht2!hv5>2st$7>3st'$7>1o$4>1m$4>0@3$5^4^2^1>0@3$1@4$b$0$2$a$f@1$9^4@1$9^5>0>3rid$0@3$1$h0@2$6^6^1@2$6^7^1>0@3$1@4$b$d@4$h3$0$2$3$c@6$h2$0$2$a$3$c$h1$e@1$8^6@1$8^7@3$5^7^6^5").
Proof. intros st st' o m.
  intros UA ER ES EG rid r off h Hr Hk Ho Hc NG. rewrite ER in Hr. rewrite ES in Hc.
  apply (UA rid r off h Hr Hk Ho Hc). (intros nd_i1; ndestruct nd_i1 as (b & gh & Hb & Hf & Hx)). apply NG. exists b, gh. rewrite EG. auto.
Qed.

Lemma unk_agree_munch : ltac2:(zQ "he0!hr1!h9!hm5!k6!ihc!j0!ii6!iif!ij7!p5!td!ijd!ik5!hk8!imb!ind!iq4!ho0!iqa!ir9!is1!jg3!jh4!jhb!ji4!hj4!jie!jj7!jjf!jk6>2st$h9>1o$9>1m$9>2m'>0@1$h0@1$8#k0@1$4@1$h0@1$8#8>1W@1$h3$h6>0@3$a^5^4^3>0@3$h7^2^4^3>0>3rid$1>1r$0>0@3$5@1$4$0@6$f$1$0@4$h1$1$3$2$0@4$h2$1$3$2$0^2@1$d^9@2$7$0^1>0@3$5$hb@1$ha^2$h8@3$h5^7@1$6^3@1$c@1$b^3>0>3rid$1>1r$0>0@3$5@1$4$0@6$f$1$0@4$h1$1$3$2$0@4$h2$1$3$2$0^2@1$d^a@2$7$0^1@2$h4@2$eZ@1$6^2@2$e@2$hc@1$6^2@1$c@1$b^2@2$hd+2+k0@3$a^9^8^6").
Proof. intros st o m m' W.
  intros UA MU HD HB rid r off h Hr Hk Ho Hc NG.
  rewrite <- (UA rid r off h Hr Hk Ho Hc NG). apply MU.
  destruct (HB rid r Hr) as [B0 B1]. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [apply (HD rid r Hr Hk)| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (junk : list byte) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a3 a5 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -64) ->
    rw_cells asegs m1 (bv_unsigned sp + -64)
       [C8 (wz idx); C8 (pw st2 (Some g)); C8 (wz (sxv (c_mmap_counter (ctx st2)))); C8 (wz idx); CB 16 junk; C8 s0v; C8 ra] ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       malloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1
                   a0 a1 (wz idx) a3 (wz (sxv (c_mmap_counter (ctx st2)))) a5 (pw st2 (Some g)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17014) fc None m1 (seg_rom asegs)).

Lemma mrel_same : ltac2:(zQ "e0!j0!h9!kf!hj4!jkd!hk8!jla!ir9!jm7!jmf!hr1!hm5!ho0!k6>2st$3>3st'$3>0@3$0@4$c$1$d$b$a@1$5^1@1$5^2>0@3$0$1@1$4^2@1$4^3>0@3$0@1$7@2$8$2$2@1$6^3@1$6^4@2$9^5^4").
Proof. intros st st'.
  intros ER EN ES. split; [| rewrite EN; lia | exact ES].
  intros rid r H. exists r. rewrite ER. repeat split; auto. lia.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End FASTCORE.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mrep st2 m1 -> ticks_ok st2 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
    pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    implT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)).

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis HENF : enf_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo.
Hypothesis HFAIL : fail_hyp K o m0 st s Q ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc lo.
Hypothesis MF : MFACTS st LB.
Hypothesis MR0 : mrep st m0.
Hypothesis MED0 : rw_cells asegs m0 MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End ASCALL.

End HCW.

(* [comment removed for export] *)
