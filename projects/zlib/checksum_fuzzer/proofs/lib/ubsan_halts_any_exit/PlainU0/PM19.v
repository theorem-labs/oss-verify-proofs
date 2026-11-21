(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM07.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM06.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM10.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM05.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM04.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM22.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM21.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM20.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM10.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM16.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require RF_free_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require PM17.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RF_ntf.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM07. Import MM07. Import MM07.MallocKit_B2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM06. Import MM06. Import MM06.F_ntf_A. Import MM07.F_ntf_B. Import MM06.F_ntf_C.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM10. Import MM10. Import MM10.F_ntf_D. Import MM10.F_ntf_E. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM05. Import MM05. Import MM05.F_ntf_F. Import MM05.F_ntf_G. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_ntf_H. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM04. Import MM04. Import MM04.F_ntf.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3.
Import PM21. Import PM21.RF_get_meta. Import PM20. Import PM20.RF_ntf_A. Import PM20.RF_ntf_C. Import PM08. Import PM08.RF_ntf_D. Import PM10. Import PM10.RF_ntf_E. Import PM16. Import PM16.RF_ntf_F. Import PM09. Import PM09.RF_ntf_G. Import PM12. Import PM12.RF_ntf_H.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp) /\ rmrep st' m'
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.


Lemma rpres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m1 -> lo <= bv_unsigned sp - 96 ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof.
  intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> rmrep st mw -> ATOP <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof.
  intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
  rewrite (OK rid r q h Hr Hk Hq M8 Hc).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  atop_facts.
  symmetry. apply (PE (r_base r + q)); [lia|].
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid' & r' & Hr' & Hk' & Hin).
    destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
    pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
  - destruct A as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
    destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
    assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
    Z.div_mod_to_equations. lia.
  - destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
    destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma rfree_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> ATOP <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof.
  intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
  atop_facts.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). atop_facts. lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). atop_facts. lia.
Qed.

Lemma rknown_byte st m (q : aptr) r v :
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof.
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

Lemma rimplT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
  rimplT o (queue h g st0 k bail) s Q ms.
Proof.
  intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
  assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
  assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
  specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : ATOP <= lo.

Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof.
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
  unfold rntf_q. do 16 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> Malloc.M R) (bail : Malloc.M R)
    (s : PState) (Q : R -> PState -> machine_state -> Prop)
    (ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
  KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> oracle_ok o m st ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
  (forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
  rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1642c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
  { cbn [nontrivial_free]. apply rimplT_undef. }
  rewrite ntf_unfold. cbv zeta.
  pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
  pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
  pose proof (go_slot _ _ _ GO) as MSL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
  set (ms0 := MS _ _ _ _ _ _ _).
  assert (ENTRY : entry_hyps st g i ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
  { intros EH. subst ms0. eapply rntf_entry; eauto. }
  assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
                       (G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
                       (G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
                             m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
             entry_hyps st g i).
  { intros. constructor; auto.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - pose proof (go_sc _ _ _ GO). lia.
    - intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
    - intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
    - split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
  destruct (ntf_cond st g i) eqn:HC.
  -
    assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
      rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
              (m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
      (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
      wmono (run_segments psegs rc_inp rc_sp rc_mb) m m2 -> oracle_ok o m2 stX ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
    { intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
      pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
      unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
      set (stU := fg_usage_st stX g) in *.
      assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
      assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
      rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
      rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).
      assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
      { destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
        unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
        unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
        pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
        apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
          try lia; try exact HALL.
        - exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
        - destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
        - destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
      assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
      assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
      assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
      rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
          [ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
          | pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
            rewrite RU in FC; exact FC ])).
      fold stG in GD. destruct GD as (KIG & NGM & NSL).
      assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
      assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
      assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).
      pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
      pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
      replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
      change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
      destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
      -
        assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
        rewrite free_meta_eq.
        eapply rimplT_evt.
        { eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
            first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
                  | apply munch_refl | apply wmono_refl | idtac].
          - pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
          - intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
        + destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
            (eapply rpres_except_mono; [exact PE3| exact FPX]).
        + intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
          unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
        + eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
          * unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros [b Hb]. apply NGM. exists b. unfold hosts in *.
            replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
        + apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        +
          pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
          set (stS := record_seq _ (step_seq stG)) in *.
          assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
          unfold fm_st. apply frame_queue.
          * apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
          * apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
          * cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
            intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
            rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
          * right; exact (hosts_is_gm _ _ _ HOSTS).
        +
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
          destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
          change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
          pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
          unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
          * unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
          * exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
          * intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
            apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
            apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
        + eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
        + exact MRG.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
      -
        assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).
        pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
        destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
        clear NEST.
        pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
        destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
        destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
        rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
        assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
        assert (B1LT : snd b1 + 16 <= snd p).
        { rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
          pose proof (go_stride _ _ _ GO1) as [S16 _].
          assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
        assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
        assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
        assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).
        pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
        assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
        { split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
          rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
          unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
          rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
          assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
          unfold UNIT, IB in *. lia. }
        destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].
        unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
        apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
        assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
        { intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
          unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
        rewrite !ESH.
        rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
        rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
        rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
        rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
        cbn [Z.eqb negb].
        set (off16 := lo8 + 256 * hi8).
        assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
        { unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
        rewrite EB. unfold get_group.
        replace (s_groups stG !! b1) with (s_groups stX !! b1).
        2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
        destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
        apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
        apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
        assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
        change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
        rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
        destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
        apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
        apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
        assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
        assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
        assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
                   bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
        { intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
                   ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
          cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
          rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
          replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
        destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
        destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
        assert (HDR : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
        { change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
          apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
          apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
          cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }
        destruct HOSTSX as [aig Hghp].
        eapply rimplT_evt.
        { eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
          all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
                     | exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
          all: try reflexivity.
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
          all: rewrite ?EU1.
          all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
               try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
          all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
          all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
          all: try (symmetry; exact EB).
          all: try (change (c_init_done (ctx stU)) with (c_init_done (ctx stG));
                    refine (ZINV_ainit stG (g :: Zs) _ _ _ AR1);
                    unfold stG; apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)]).
          all: match goal with
               | |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
               | |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
                                   apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
               | |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
                                   fold off16 in G17; unfold UNIT in G17;
                                   replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
                                   rewrite Z.div_mul in G17 by lia; lia
               | |- ?G => idtac "NCGOAL" G; fail
               end. }
        intros ms3 NC. unfold rnest_call_post in NC.
        destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
        fold stG in MR4.
        pose proof (bv_unsigned_in_range _ sp) as SPR'.
        assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (atop_facts; rewrite unsigned_lit; lia).
        rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
        eapply (IH R _ bail s Q (Z_to_bv 64 0x166b4) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
        + exact KIG.
        + constructor.
          * exact HB1G.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
            apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
            pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
            pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
        + unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + exact MR4.
        + exact MI4.
        + apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
          eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
          intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
        + rewrite SPU. exact ST4.
        + rewrite SPU. lia.
        +
          intros st3 mi ms5 NQ. rewrite free_meta_eq.
          unfold rntf_q in NQ. rewrite SPU in NQ.
          destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
          replace (ret_pc (Z_to_bv 64 0x166b4)) with (Z_to_bv 64 0x166b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
          { apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
          assert (NGM3 : ~ is_gm st3 g).
          { intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
          eapply rimplT_evt.
          { eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
              first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
            - unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
            - intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
            - unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
            - eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
              intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
            - exact ST5. }
          intros ms6 RP. apply KH.
          pose proof (frame_trans _ _ _ FRG FR35) as FR03.
          pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
          eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
          * destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
              (eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
          * intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
          * exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
            intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
          * apply ZINV_fm. exact ZI3.
          * unfold fm_st. apply frame_queue.
            -- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
            -- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
            -- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
               intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
               rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
            -- right; exact (hosts_is_gm _ _ _ HOSTS).
          * destruct mi as [[bb len]|]; [| exact RES5].
            destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
            unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
            split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
            intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
          * exact OOK5.
          * exact MR5.
          * exact FS1.
          * exact FS2. }
    assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
      s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
      (m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
      rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m4 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m4 ->
      stk (run_segments psegs rc_inp rc_sp rc_mb) m4 lo (bv_unsigned sp + -96) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
      ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
               F (Z_to_bv 64 0x16654) fc None m4 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
    { intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
      assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
      eapply rimplT_evt.
      { eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
          first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
      intros ms5 FGP.
      eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
      - intros a Ha. eapply (rfree_fp_same st stX); eauto.
      - apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
        eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
    destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
    +
      apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
      set (sc := m_sizeclass (get_meta_rec st g)) in *.
      set (an := optr_eqb (active st sc) (Some g)).
      set (stm := deq_mid (LActive sc) g st).
      set (st1 := dequeue (LActive sc) g st).
      assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
      pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
      pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
      assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
      assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
      assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
      assert (FR1' : ntf_frame st st1).
      { unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
      destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
      pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
      destruct DS as (DSdata & GN1 & GP1 & _).
      assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m2 ->
        rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
                   (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (match an, active st1 sc with
                 | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
                 | _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
                 end) s Q ms2).
      { intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
        unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
        assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
        { destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }
        assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
        { pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). atop_facts.
          rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
          - destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
            pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). atop_facts.
            unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
          - unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
        assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
          evt (run_segments psegs rc_inp rc_sp rc_mb) (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x165f0) fc None m3 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
        { intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
          eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
            first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBLm| exact MSL].
          - pose proof (go_sc _ _ _ GO). subst sc. lia.
          - rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
            destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
            destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
            destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
            split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
            exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
        assert (AVK : forall a, an = true -> active st1 sc = Some a ->
                 rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x165f0) fc None m3 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
        { intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
          change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
          set (stA := act_st st1 a (act_of st1 a)).
          destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
          assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
          eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
          - unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
          - unfold stA. apply ZINV_act. exact ZI1.
          - unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
          - unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
          - unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
          - unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
          - unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
          - unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
          - unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
          - unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
            change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
            apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        assert (NOACT : (an = false \/ active st1 sc = None) ->
                 rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x165f0) fc None m3 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
        { intros NA.
          eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
          rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
          - apply DSdata.
          - apply (sbl_regions _ _ SBL1).
          - apply (sbl_shadow _ _ SBL1).
          - apply (sbl_groups _ _ SBL1).
          - intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); congruence).
      *
        destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx = g) by congruence.
        eapply rimplT_evt.
        { eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - rewrite NX, Enx. reflexivity. }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
      *
        destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx' = nx) by congruence. subst nx'.
        eapply rimplT_evt.
        { eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - apply NEpv. exact NE.
          - destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
            exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
    +
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
      eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
                               | | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
      intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
    +
      apply Z.eqb_eq in HM.
      apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.
      assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m1 ->
        stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
        (active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
        forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                      x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (k (aor_st stq g i) None) s Q ms2).
      { intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
        assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
        assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
        assert (KIq : KINV stq LB c).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
          apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
        assert (FRq : ntf_frame st stq).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
          apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
          cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
        unfold rqpath_post in QP. cbv beta in QP.
        destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
        pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
        rewrite <- (conc_sbl st stq g SBL).
        eapply rimplT_evt.
        { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
            first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBL| exact MSL].
          - pose proof (go_li _ _ _ GO). lia.
          - destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
        * eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
        * exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
        * apply ZINV_aor. exact ZIq.
        * apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
        * exact eq_refl.
        * apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
          eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
          eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * exact MR2.
        * reflexivity.
        * reflexivity. }
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
      *
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
        { destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | exact HAct]|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - right. exists g. split; [exact HAct| exact MSL].
          - intros NE. exfalso. exact (NE HAct).
          - intros hd Hhd NE. exfalso. apply NE. congruence. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
      *
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
        { intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
        apply rimplT_queue. intros GN GPV.
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
            exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
          - intros _. split; assumption.
          - intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
            split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
    +
      apply Z.eqb_neq in HM.
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
      eapply rimplT_evt.
      { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
          first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
        - pose proof (go_li _ _ _ GO). lia.
        - exact (go_freed _ _ _ GO). }
      intros ms2 RP. apply KH.
      eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
      * eapply rpres_except_entry; eauto.
      * auto.
      * exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
      * apply ZINV_aor. exact ZI.
      * apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
      * exact eq_refl.
      * eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
      * exact MR1.
      * reflexivity.
      * reflexivity.
Qed.
End NTF.
End CANSEC1.
End RF_ntf.

Module RF_free.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_B. Import MM12.MallocFacts_B_reach.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM07. Import MM07. Import MM07.MallocKit_B2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocFacts_Bpres. Import MM12.F_mm_syscalls. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM04. Import MM04. Import MM04.F_ntf. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM03. Import MM03. Import MM03.F_free_C. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM09. Import MM09. Import MM09.F_free_K. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM01. Import MM01. Import MM01.F_free.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM21. Import PM21.RF_get_meta. Import PM21.RF_mm_syscalls.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PlainU0 Require Import RF_free_A. Import PM20. Import PM20.RF_free_B. Import PM17. Import PM17.RF_free_C. Import RF_ntf. Import PM08. Import PM08.RF_free_K.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop :=
  fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (errno_addr tp) [C4 errv]
    /\ rmrep st' m'
    /\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 195804 <= a < 195808) m m'
    /\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
    /\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
    /\ c_brk (ctx st') = c_brk (ctx st)
    /\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> ATOP <= lo -> 195804 <= a < 195808 -> ~ rfree_fp st lo sp a.
Proof.
  intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.

Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
  rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
  (s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
  munch [(slo, shi); (195804, 195808); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
  ATOP <= slo ->
  rmrep (drop_region rid st2) m5.
Proof.
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
  pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). atop_facts.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < ATOP /\ ~ (195804 <= a < 195808) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold PImg.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). atop_facts. lia.
        * destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). atop_facts. lia.
        * destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). atop_facts. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold PImg.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
          assert (NE : fst b <> rid).
          { intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). atop_facts.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Lemma bytes4_range (x0 x1 x2 x3 : byte) :
  0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
  le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.

Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : ATOP <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof using LO TP.
  intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = 195804) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof LO as LOv. atop_facts.
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (atop_facts; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x51000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at (run_segments psegs rc_inp rc_sp rc_mb) m (r_base r + snd q) 1).
    { destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); atop_facts; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (ci_ainit _ _ C _ _ AR1).
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - clear - GSC; lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [clear - OFF SZ AEND TOP HAp Hml; lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    -
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32. 
      destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0. 
      destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1. 
      destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
      destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    -
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; clear - SR5 V3R ERNG; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
  destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  -
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  -
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x162c4)) with (Z_to_bv 64 0x162c4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    +
      cbv beta iota.
      destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). atop_facts.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x51000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms4 FM. unfold rfmun_post in FM.
      destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. clear - R2D CB2; lia.
        - rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
      rewrite (munmap_ok_range_val a ERNG).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x162f4)) with (Z_to_bv 64 0x162f4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      {
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 195804 <= a < 195808)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 195804 <= a < 195808)); [| exact NC].
          cover_intervals ltac:(fun y Hy => clear - SLO CB2 DR Hy; first [left; apply rfree_fp_stack; lia | right; right; lia | right; left; apply DR; lia]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 195804 <= a < 195808)); [| exact NC].
        cover_intervals ltac:(fun y Hy => clear - SLO Hy; first [left; apply rfree_fp_stack; lia | right; right; lia]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    +
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 195804 <= a < 195808)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.
End CANSEC1.
End RF_free.
