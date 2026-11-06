(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp F_malloc_enf F_malloc_join.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk46option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~m55rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~qf6mstate46Stdlib6ZArith6BinInt1Zv62lt37Corelib4Init5Logichh33andhh32or69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~hj45hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMalloc_fp~~~~~~hn8armalloc_fpv62le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hsd3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ih78rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ile5rsegsk44list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~iqb4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~iufcrpres_except79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~jk24mrelm54RCTXv63addiuf8rauxv_ok" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
  forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
    rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                 < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
       rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
    0 <= c_mmap_counter (ctx st2) < 2^32 ->
    slot_ok st2 g b r idx n ->
    (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 (Some (g, idx))) s' Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xe0b98) fc None m1 (seg_rom rsegs)).

(* [comment removed for export] *)
Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
    (Q : R -> PState -> machine_state -> Prop)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
  forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
    rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
    mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
    rimplT o (K st2 None) s' Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmalloc_fp_cases : ltac2:(zQ "c1!h9!jc!k1!lc!q7!ud!hge!hi7!hie!hmf!hra!hs8&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2st$5>3st2$5>2lo$2>2sp$2>2m0~0>2m2~0>1a$2>0@4$4?5HCEIL?4HSEC^7^3>0@4$4?5HCEIL?4HSEC^7^3>0@5$a^9^8^7^6^3@2$8@2$7@2$b^8^4@2$6^4^7@2$6^4@1$9?5HCEIL").
Proof. intros st st2 lo sp m0 m2 a. try hcb. try hsb.
  intros (WF & _) (WF2 & _) H. npose WF as (RS1 & WR & _). npose WF2 as (_ & WR2 & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  all: try pose proof (rfresh_below st a (conj FC FR) RS1) as FC'.
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. ndestruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. ndestruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. ndestruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. ndestruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - right. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in FC. lia.
Qed.

Lemma rframe_after_call : ltac2:(zQ "f1!h9!jc!k1!lc!ih0!il2!q7!ipb!ud!hs8!iq4!hmf!iu7!jj2!hra&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2st$8>3st2$8>2lo$2>3sp'$2>2m0~0>1m$4>2m'$4>2m2~0>1A$2>2cs@1$a$c>0@4$6?5HCEIL?4HSEC^a^6>0@4$6?5HCEIL?4HSEC^a^4>0@3$d@4$e^c^b^a^9^7^6>0@4$5$7^8^5^4>0@2$9^b^6>0@2$9@1$b?5HCEIL^7@4$5$7^a^8^7").
Proof. intros st st2 lo sp' m0 m m' m2 A cs. try hcb. try hsb.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono : ltac2:(zQ "40!k1!hra!ud!hs8>2st$2>3st2$2>2lo$0>3sp1$0>3sp2$0>1a$0>0@2$3^3^2>0@5$1^7^6^5^4^2@5$1^8^7^6^4^3").
Proof. intros st st2 lo sp1 sp2 a. try hcb. try hsb.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono : ltac2:(zQ "40!k1!ud!hra!jo4>2st$1>3sta$1>3stb$1>2lo$0>2sp$0>1a$0>0@2$3^5^4>0@5$2^7^6^4^3^2@5$2^8^6^5^4^3").
Proof. intros st sta stb lo sp a. try hcb. try hsb. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image : ltac2:(zQ "e1!h9!hs8!jc!hi7!k1!hge!lc!joc!q7!ud!hie!hmf!hra!jp3&>0@1$2@1$0#k0@1$6@1$2@1$0#8>2st$9>3st2$9>2lo$4>2sp$4>2m0~0>2m2~0>1a$4>0@4$8?5HCEIL?4HSEC^7^3>0@4$8?5HCEIL?4HSEC^7^3>0@5$c^9^8^7^6^3>0@2$1@1$b?5HCEIL^8>0@2$3@2$1+vkgg0^5@2$5^5+hjhgg0@2$a@2$3@2$1$7^6@2$5^6@2$d$7+jq0@2$3@2$1+hgurl4^6@2$5^6+hgurl8").
Proof. intros st st2 lo sp m0 m2 a. try hcb. try hsb.
  intros (WF & _) (WF2 & _) H CLO HA. npose WF as (_ & WR & _). npose WF2 as (_ & WR2 & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - ndestruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - ndestruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - (* [comment removed for export] *)
    exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

Lemma rauxv_ok_malloc_fp : ltac2:(zQ "c1!h9!jc!k1!lc!ih0!q7!jp9!ud!hs8!hmf!jj2!hra&>0@1$1@1$0#k0@1$3@1$1@1$0#8>2st$7>3st2$7>2lo$2>2sp$2>2m0~0>2m2~0>1m$4>2m'$4>1B$2>0@4$5?5HCEIL?4HSEC^9^5>0@4$5?5HCEIL?4HSEC^9^5>0@4$6?5HCEIL?4HSEC^5^3>0@3$a@4$b^c^b^a^9^6^5>0@2$8@1$9?5HCEIL^b>0@2$8^b^6@4$6?5HCEIL?4HSEC^8^7").
Proof. intros st st2 lo sp m0 m2 m m' B. try hcb. try hsb.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    ndestruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

End HCW.

