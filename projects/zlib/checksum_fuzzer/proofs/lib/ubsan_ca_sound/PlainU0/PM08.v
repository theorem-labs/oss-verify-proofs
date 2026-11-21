(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PImgRun.
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
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require ASlot_W9.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM21.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM22.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RASlot_W2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require RASlot_W4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM05.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM07.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM10.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM20.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require PM10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_M5D.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import ASlot_W9. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM01. Import MM01. Import MM01.ASlot_M0. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM02. Import MM02. Import MM02.ASlot_M5D.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RASlot_W4. Import PM03.RASlot_M0. Import PM05. Import PM05.RASlot_M2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM01. Import MM01.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  intros MR REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rregion_byte_raw st m rid r off v :
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
  intros MR Hr Hk Ho Hc.
  destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). atop_facts.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - (* a group region is writable (rshadow_rep's wr_at), so its byte is in the overlay *)
    exfalso. pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH _ _ Hr Hk) as [(_ & _ & HW) _].
    specialize (HW off ltac:(lia)).
    rewrite PImgRun.run_ref_wview_overlay in HW by (rewrite wa_unsigned by lia; lia). exact (HW E).
Qed.

Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x2fcdc.
Proof. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
  mkR (Z_to_bv 64 0x1722c) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
      a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
      (wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
    (m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
  leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'' /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m'' lo (bv_unsigned sp - 144) /\
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
  rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
  rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
  mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
  as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
  rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x172a4) fc None m'' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Definition rNSUCC_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
  0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
  (forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
             < r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
     rmalloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
  (s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
  rimplT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
              sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x17230) fc None m'' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
End LEVEL.
End CANSEC1.
End RASlot_M5D.

Module RF_free_K.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_B. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM09. Import MM09. Export MM09.F_free_K.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.


Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : rctx_head_cells st' = rctx_head_cells st.
Proof.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold rctx_head_cells, rsecw. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
  intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof.
  intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (proj1 ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End CANSEC1.
End RF_free_K.

Module RF_ntf_D.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM10. Import MM10. Import MM10.F_ntf_D. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM20. Import PM20.RF_ntf_A. Import PM10. Import PM10.RF_ntf_E.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof.
  intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lxor_ones64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  Z.lor (Z.lxor a 18446744073709551615) (Z.lxor b 18446744073709551615) = Z.lxor (Z.land a b) 18446744073709551615.
Proof.
  intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
  destruct (Z.lt_ge_cases n 64) as [L|G].
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.

Lemma usage_sub_word u w : 0 <= u < 2^64 -> 0 <= w < 2^64 ->
  Z_to_bv 64 (u + Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor w 18446744073709551615))) 18446744073709551584)
  = wz (u - (Z.land w 31 + 1)).
Proof.
  intros Hu Hw.
  assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
  rewrite unsigned_lit by lia.
  change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
  rewrite lor_lxor_ones64 by lia.
  assert (HL : 0 <= Z.land w 31 < 32).
  { split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite zb_lxor_ones by lia. unfold wz.
  rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
  replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x16688) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -96)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_fg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (lo : Z),
  let mr := get_meta_rec st g in
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g ->
  mw_ok mr ->
  (m_sizeclass mr < 48 -> 0 <= usage st (m_sizeclass mr) < 2^64) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rfg_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (fg_usage_st st g) g (m_sizeclass mr) (meta_word mr) fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16654) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (meta_word_range mr MW) as MWR.
  pose proof MW as (LI & FB & SCR & ML).
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  unfold RCTX in *. atop_facts.
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
      with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rmeta_chunk MR MSL CH. fold mr in CH.
  st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    clear CH.
    unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
  - unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
    specialize (UR ltac:(lia)).
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (327816, 327816 + 928)]%Z m) as MU.
    pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
    pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    st1.
    replace (wa (327816 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (327816 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. st1. st1.
    rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
    pose proof MR as (_ & (_ & _ & USG & _) & _).
    pose proof (u64arr_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (327816 + m_sizeclass mr * 8 + 464)) USG
                  ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    clear USG.
    rraw_store_finish (327816 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (CH' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (conc st g) (meta_cells st mr)) end.
    { pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
      rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
      replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
      unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
    clear CH. unfold meta_cells in CH'.
    st1. clear CH'.
    apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.
End CANSEC1.
End RF_ntf_D.
