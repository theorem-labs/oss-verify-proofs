(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS MallocKit_A3 ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W9 ASlot_W10 ASlot_W12 ASlot_W13 ASlot_W14 ASlot_W18 ASlot_I ASlot_M0.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS MallocKit_A3 ASlot_W0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module ASlot_M3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W10 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0.

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
  induction F as [|F IH]; intros cnt sz Hc Hs; cbn [halve_big]; [lia|].
  destruct (Z.leb_spec (65536 * UNIT) (sz * cnt)) as [LE|GT]; [|lia].
  apply IH; [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. unfold UNIT in LE.
  assert (2 <= cnt) by nia. Z.div_mod_to_equations. lia.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

(* [comment removed for export] *)
Definition ag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (j : list byte) (oo : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  mrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp + -96) /\
  rw_cells asegs m3 (bv_unsigned sp + -96) (ag_frame sc j s4 s3 s2 s1 s0 ra) /\
  rw_cells asegs m3 (errno_addr tp) [C4 errv'] /\ auxv_ok m3 (bv_unsigned sp) /\ rw_cells asegs m3 MEDTAB medtab_cells /\
  pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
  brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition HMM_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' j oo (cnt1 : Z) (t0' t2' a3' t4' t6' : word),
  ag_ctx st1 st2 mm m3 s' errv' j oo ->
  1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
  implT o (ag_mmap sc req k bail st2 mm cnt1) s' Q
    (MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' (wz (size_class sc * UNIT)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
             (wz 4096) (wz (size_class sc * UNIT * cnt1)) (wz (usage st2 sc)) a3' (Z_to_bv 64 SIZE_CLASSES) (wz 2048) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
             (Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) t4' (wz (4 * cnt1)) t6')
        F (Z_to_bv 64 0x16640) fc None m3 (seg_rom asegs)).

Definition HNEST_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' j oo (cnt1 : Z) (t0' t2' a3' t5' t6' : word),
  ag_ctx st1 st2 mm m3 s' errv' j oo ->
  1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  implT o (ag_nest f sc k bail st2 mm cnt1) s' Q
    (MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' (wz (size_class sc * UNIT)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
             (wz 4096) (wz (size_class sc * UNIT * cnt1)) (wz (usage st2 sc)) a3' (Z_to_bv 64 SIZE_CLASSES) (wz 2048) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
             (Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) (wz cnt1) t5' t6')
        F (Z_to_bv 64 0x16954) fc None m3 (seg_rom asegs)).

Hypothesis HMM : HMM_stmt.
Hypothesis HNEST : HNEST_stmt.

(* [comment removed for export] *)
End LEVEL.

End ACeilS1.
End ASlot_M3.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W14.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module ASlot_M4P.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_big.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma pos_iter_slots' (m p : aptr) (stride : Z) : forall n tb,
  0 < stride ->
  let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
  fst (Pos.iter F (0, tb) n) = Z.pos n
  /\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
    intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
    left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
  - rewrite Pos.iter_succ. cps_destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
    unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
    split; [lia|]. split.
    + rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
    + intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
      * right. exists (Z.pos n). split; [lia| reflexivity].
      * rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first' m p stride c st : 1 <= c -> 0 < stride ->
  (s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
  destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
  cps_destruct (pos_iter_slots' m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

Lemma mask_upto_range' k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

(* [comment removed for export] *)
Lemma put_meta_wr8_comm mt r q v st : put_meta mt r (wr8 q v st) = wr8 q v (put_meta mt r st).
Proof. destruct st; reflexivity. Qed.
Lemma put_meta_zero_hdrs_comm mt r p size : forall k i st,
  put_meta mt r (zero_hdrs p size i k st) = zero_hdrs p size i k (put_meta mt r st).
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH, put_meta_wr8_comm. reflexivity. Qed.
Lemma rec_zero_hdrs p size q : forall k i st, get_meta_rec (zero_hdrs p size i k st) q = get_meta_rec st q.
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. destruct st; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SMG.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis P0 : 0 <= snd p.

Definition sm_rec : meta :=
  mkMeta (Some mt) (Some mt) (Some p) (mask_upto ai - 1) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.

Lemma smg_proj :
  s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
  /\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
  /\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
  /\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
  /\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. repeat split; reflexivity. Qed.

Lemma smg_rec_mt : get_meta_rec stF mt = sm_rec.
Proof.
  unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
  unfold stFin, stE. rewrite rec_set_active, get_meta_rec_put_same. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma smg_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof.
  unfold stF, st_model. cbv zeta. rewrite active_set_active. destruct (c =? sc); [reflexivity|].
  rewrite !active_upd_meta. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma smg_stride : get_stride sm_rec = if (cnt =? 1) && negb (ml =? 0) then ml * 4096 - 16 else 16 * size_class sc.
Proof.
  unfold get_stride, sm_rec. cbn [m_last_idx m_maplen m_sizeclass].
  replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); try reflexivity; lia).
  unfold UNIT. reflexivity.
Qed.

Lemma smg_slot0 : 0 < get_stride sm_rec -> (s_slots stF) !! (fst p, snd p + 16) = Some (mt, 0).
Proof.
  intros HS. unfold stF, st_model. cbv zeta.
  match goal with |- s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ ?X))) !! _ = _ =>
    change (s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ X)))) with (s_slots X) end.
  match goal with |- s_slots (add_slots mt p ?s cnt ?X) !! _ = _ =>
    replace s with (get_stride sm_rec) end.
  2:{ unfold upd_meta. rewrite rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC. unfold get_stride, sm_rec.
      cbn [m_last_idx m_maplen m_sizeclass m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      reflexivity. }
  change (fst p, snd p + 16) with (aadd p UNIT).
  apply (proj1 (add_slots_first' mt p (get_stride sm_rec) cnt _ ltac:(lia) HS)).
Qed.

Lemma smg_shadow_other q : q <> fst p -> get_shadow stF q = get_shadow stT q.
Proof.
  intros NE. unfold get_shadow. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma smg_shadow_p :
  get_shadow stF (fst p) = mkShadow (r_cells (get_shadow stT (fst p)))
                             (<[snd p / 16 := hav_add 12 (s_tick stT) (default [] ((r_hav (get_shadow stT (fst p))) !! (snd p / 16)))]> (r_hav (get_shadow stT (fst p))))
                             (r_havp (get_shadow stT (fst p))).
Proof.
  unfold get_shadow at 1. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma smg_group_p : (s_groups stF) !! p = Some (mkGhdr (Some mt) (Z.land ai 31)).
Proof. rewrite (proj1 (proj2 (proj2 smg_proj))). apply lookup_insert_eq. Qed.

Lemma smg_groups_inv b' gh : (s_groups stF) !! b' = Some gh -> (b' = p /\ gh = mkGhdr (Some mt) (Z.land ai 31)) \/ (b' <> p /\ (s_groups stT) !! b' = Some gh).
Proof.
  rewrite (proj1 (proj2 (proj2 smg_proj))). intros H. destruct (decide (b' = p)) as [->|NE].
  - left. rewrite lookup_insert_eq in H. inversion H. auto.
  - right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.

Lemma smg_groups_old b' gh : (s_groups stT) !! p = None -> (s_groups stT) !! b' = Some gh -> (s_groups stF) !! b' = Some gh.
Proof.
  intros GN H. rewrite (proj1 (proj2 (proj2 smg_proj))). rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite GN in H. discriminate.
Qed.

Lemma smg_grp_hdr_cov off : snd p <= off < snd p + 12 -> grp_hdr_cov stF (fst p) off.
Proof. intros Ho. exists p, (mkGhdr (Some mt) (Z.land ai 31)). split; [exact smg_group_p|]. split; [reflexivity| lia]. Qed.

Lemma smg_grp_hdr_cov_old q off : (s_groups stT) !! p = None -> grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. (intros GN; cps_intros (b' & gh & Hb & Hf & Ho)). exists b', gh. split; [apply smg_groups_old; assumption| auto]. Qed.

Lemma smg_conc q : conc stF q = conc stT q.
Proof. unfold conc, get_region. rewrite (proj1 smg_proj). reflexivity. Qed.

Lemma smg_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. split; intros H; (eapply meta_slot_same_areas; [| exact H]); rewrite (proj1 (proj2 (proj2 (proj2 smg_proj)))); reflexivity. Qed.

(* [comment removed for export] *)
Lemma smg_ret_span rid' S len :
  (exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
     /\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
  rid' = fst p /\ S = snd p + 16 /\ len = get_stride sm_rec - 4.
Proof.
  cps_intros (g & b & HA & HM & -> & -> & ->). rewrite smg_active, Z.eqb_refl in HA. inversion HA; subst g.
  rewrite smg_rec_mt in HM |- *. cbn in HM. inversion HM; subst b. split; [reflexivity| split; [lia| reflexivity]].
Qed.
End SMG.

Lemma Zle_1_nonneg' x : 1 <= x < 2^28 -> 0 <= x /\ True.
Proof. intros H. split; [lia| exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SM.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt : aptr) (rid : N) (r0 : region).
Let p : aptr := (rid, 0).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 1 <= ml < 2^28.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis HrT : (s_regions stT) !! rid = Some r0.
Hypothesis Hk0 : r_kind r0 = RKGroup.
Hypothesis SHT : (s_shadow stT) !! rid = None.
Hypothesis GNT : forall off, (s_groups stT) !! (rid, off) = None.

Let P0 : 0 <= snd p := Z.le_refl 0.
Let ML0 : 0 <= ml := proj1 (Zle_1_nonneg' ml ML).


Lemma sm_proj :
  s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
  /\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
  /\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
  /\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
  /\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. exact (smg_proj stT sc cnt ai mt p). Qed.

Lemma sm_rec_mt : get_meta_rec stF mt = sm_rec sc cnt ai ml mt p.
Proof. apply (smg_rec_mt stT sc cnt ai ml mt p); assumption. Qed.

Lemma sm_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof. exact (smg_active stT sc cnt ai mt p c). Qed.

Lemma sm_ml_nz : (ml =? 0) = false.
Proof. apply Z.eqb_neq. lia. Qed.

Lemma sm_stride : get_stride (sm_rec sc cnt ai ml mt p) = if cnt =? 1 then ml * 4096 - 16 else 16 * size_class sc.
Proof. rewrite (smg_stride sc cnt ai ml mt p) by assumption. rewrite sm_ml_nz, andb_true_r. reflexivity. Qed.

Lemma sm_slot0 : 0 < get_stride (sm_rec sc cnt ai ml mt p) -> (s_slots stF) !! (rid, 16) = Some (mt, 0).
Proof. intros HS. apply (smg_slot0 stT sc cnt ai ml mt p); assumption. Qed.

(* [comment removed for export] *)
Lemma sm_cell_read off : 0 <= off -> cell_read (get_shadow stF rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  intros Ho. unfold get_shadow. rewrite (proj1 (proj2 sm_proj)). fold (get_shadow (hdr_havoc p stT) rid).
  apply cell_read_hh0; [exact SHT| exact Ho].
Qed.

Lemma sm_cells_none off : (r_cells (get_shadow stF rid)) !! off = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_cells]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_hav_none off : 16 <= off -> (r_hav (get_shadow stF rid)) !! (off / 16) = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. intros Ho. change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_hav]. unfold p. cbn [fst snd]. change (0 / 16) with 0.
  rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). unfold get_shadow. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_havp_none k : (r_havp (get_shadow stF rid)) !! k = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_havp]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_shadow_other q : q <> rid -> get_shadow stF q = get_shadow stT q.
Proof. intros NE. exact (smg_shadow_other stT sc cnt ai mt p q NE). Qed.

Lemma sm_groups_rid off gh : (s_groups stF) !! (rid, off) = Some gh -> off = 0 /\ gh = mkGhdr (Some mt) (Z.land ai 31).
Proof.
  intros H. destruct (smg_groups_inv stT sc cnt ai mt p _ _ H) as [[E ->]|[NE H']].
  - unfold p in E. inversion E. auto.
  - rewrite GNT in H'. discriminate.
Qed.

Lemma sm_grp_hdr_cov off : 0 <= off < 12 -> grp_hdr_cov stF rid off.
Proof. clear ML0 P0 CNT AI ML REC HrT Hk0 GNT SHT. intros Ho. apply (smg_grp_hdr_cov stT sc cnt ai mt p SC off). cbn. lia. Qed.

Lemma sm_grp_hdr_cov_old q off : grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros H. exact (smg_grp_hdr_cov_old stT sc cnt ai mt p P0 q off (GNT 0) H). Qed.

Lemma sm_conc q : conc stF q = conc stT q.
Proof. exact (smg_conc stT sc cnt ai mt p q). Qed.

Lemma sm_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. exact (smg_meta_slot stT sc cnt ai mt p q). Qed.

Lemma sm_rdv o : rdv pans_mem o stF (rid, 13) = 0.
Proof. clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. unfold rdv. cbn [fst snd]. rewrite sm_cell_read by lia. reflexivity. Qed.

Lemma sm_stride_mod16 : get_stride (get_meta_rec stF mt) mod 16 = 0.
Proof.
  rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1).
  - replace (ml * 4096 - 16) with ((256 * ml - 1) * 16) by lia. apply Z_mod_mult.
  - rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma sm_slot_ok (req nd : Z) :
  0 <= req < 2^32 -> req + 4 <= 16 * size_class sc ->
  r_len r0 = nd -> nd = 4096 * ml -> req + 20 <= nd -> 16 * size_class sc < 2^18 ->
  (cnt = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * cnt + 16 <= nd /\ nd < 16 * size_class sc * cnt + 16 + 4096) ->
  meta_slot stT mt ->
  slot_ok stF mt p r0 0 req
  /\ get_stride (get_meta_rec stF mt) = (if cnt =? 1 then nd - 16 else 16 * size_class sc)
  /\ 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) <= nd.
Proof.
  intros RQ FIT LEN EML NDR SZ NDC MS.
  pose proof (size_class_range sc SC) as SZR.
  assert (RU : round_up_pg nd = nd).
  { rewrite EML. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace (- (4096 * ml)) with ((- ml) * 4096) by lia. rewrite Z_mod_mult. lia. }
  assert (STR : get_stride (get_meta_rec stF mt) = if cnt =? 1 then nd - 16 else 16 * size_class sc).
  { rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1); lia. }
  assert (S20 : 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) * cnt <= nd
               /\ req + 4 <= get_stride (get_meta_rec stF mt) /\ get_stride (get_meta_rec stF mt) - 4 - req < 2^31
               /\ (forall off, 16 * off + req + 4 <= get_stride (get_meta_rec stF mt) -> off < 65536)).
  { rewrite STR. destruct (Z.eqb_spec cnt 1) as [E1|NE1].
    - rewrite E1. destruct NDC as [[_ X]|[X1 X2]]; (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros off Hoff; lia).
    - destruct NDC as [[X _]|[X1 X2]]; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros off Hoff. lia. }
  cps_destruct S20 as (G20 & GSP & GFIT & G31 & G18).
  pose proof (mask_upto_range' ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (AM : mask_upto ai <= mask_upto (cnt - 1)) by (unfold mask_upto; apply Z.sub_le_mono_r; apply Z.pow_le_mono_r; lia).
  split; [| split; [exact STR| split; [exact G20| nia]]].
  constructor.
  - rewrite sm_rec_mt. reflexivity.
  - rewrite (proj1 sm_proj). exact HrT.
  - exact Hk0.
  - unfold p. cbn [snd]. lia.
  - reflexivity.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - replace (m_last_idx (get_meta_rec stF mt)) with (cnt - 1) by (rewrite sm_rec_mt; reflexivity).
    rewrite LEN, RU. unfold p. cbn [snd]. replace (cnt - 1 + 1) with cnt by lia. lia.
  - exact G20.
  - apply sm_stride_mod16.
  - exact G31.
  - lia.
  - exact GFIT.
  - intros b' gh Hb' Hf. destruct b' as [b1 b2]. unfold p in Hf. cbn in Hf. subst b1. destruct (sm_groups_rid _ _ Hb') as [-> _]. unfold p. cbn [snd]. left. lia.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0 - 4) with 12 by lia. rewrite sm_cell_read by lia. reflexivity.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. apply G18. exact OF.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0) with 16 by lia. apply sm_slot0. rewrite <- sm_rec_mt. lia.
  - apply (proj1 (sm_meta_slot mt)). exact MS.
  - rewrite sm_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

Lemma sm_ret_span rid' S len :
  (exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
     /\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
  rid' = rid /\ S = 16.
Proof.
  intros H. cps_destruct (smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H) as (-> & -> & _). unfold p. cbn. split; reflexivity.
Qed.
End SM.

End ACeilS1.
End ASlot_M4P.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
Module ASlot_M1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0.

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : ISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

(* [comment removed for export] *)
End TASLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

(* [comment removed for export] *)

(* [comment removed for export] *)
End LEVEL.

End ACeilS1.
End ASlot_M1.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W15. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W15. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W17 ASlot_W18.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W12.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
Module ASlot_M4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_mm_syscalls.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_bigw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_big.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W10 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W15 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W15.ASlot_W16 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W17 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W18 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M4P. (* [comment removed for export] *)            (* [comment removed for export] *)              (* [comment removed for export] *)                 

 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section MMEQ.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
  let size := UNIT * size_class sc in
  let st1 := step_seq (account_bounce sc st2) in
  fun r =>
        if negb (mmap_answer_ok (live_ranges st1) nd r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r nd st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if c - 1 <? ai then c - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

Lemma ag_mmap_eq st2 m cnt :
  ag_mmap sc req k bail st2 m cnt =
  (let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
                              (mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
                              (is_bouncing sc st2) in
   SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Lemma ag_tail_kq_eq stT mm p c ai :
  m_next (get_meta_rec stT mm) = None -> m_prev (get_meta_rec stT mm) = None -> active stT sc = None ->
  ag_tail full_lay stT sc mm p c ai (as_kq sc k bail) = k (st_model stT sc c ai mm p) 0.
Proof.
  intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
  rewrite as_queue_eq.
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
  unfold as_queue_st. cbn [get_head].
  match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
  rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mm_cnt_red_range sc size cnt u1 nos : 1 <= cnt <= 32 -> 1 <= mm_cnt_red sc size cnt u1 nos <= 32.
Proof.
  intros H. unfold mm_cnt_red.
  destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props x : 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma mm_final_props size req u1 cnt nos c nd :
  1 <= cnt <= 32 -> 16 <= size -> 0 <= req -> req + 4 <= size ->
  mm_final size req u1 cnt nos = (c, nd) ->
  1 <= c <= cnt /\ nd mod 4096 = 0 /\ req + 20 <= nd
  /\ (c = 1 /\ nd = round_up_pg (req + 20) \/ size * c + 16 <= nd /\ nd = round_up_pg (size * c + 16)).
Proof.
  intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
  pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
  pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
  change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
  change (size * cnt + UNIT) with (size * cnt + 16) in E.
  destruct (negb nos && (cnt <=? 7)).
  - destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
    + inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
    + destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
      * inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
      * inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
  - inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stS_shape sc st2 : exists f, step_seq (account_bounce sc st2) = upd_ctx f st2
  /\ forall c, c_active (f c) = c_active c /\ c_usage (f c) = c_usage c /\ c_brk (f c) = c_brk c
     /\ c_mmap_counter (f c) = c_mmap_counter c /\ c_free_meta_head (f c) = c_free_meta_head c
     /\ c_avail_meta (f c) = c_avail_meta c /\ c_secret (f c) = c_secret c /\ c_init_done (f c) = c_init_done c
     /\ c_avail_meta_count (f c) = c_avail_meta_count c /\ c_avail_meta_area_count (f c) = c_avail_meta_area_count c
     /\ c_meta_alloc_shift (f c) = c_meta_alloc_shift c /\ c_meta_area_head (f c) = c_meta_area_head c
     /\ c_meta_area_tail (f c) = c_meta_area_tail c /\ c_avail_meta_areas (f c) = c_avail_meta_areas c.
Proof.
  assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
  { unfold account_bounce, set_bounce.
    destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
  cps_destruct AB as (g & EG & HG).
  rewrite step_seq_eq. rewrite EG.
  destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
  - exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
  - exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.

(* [comment removed for export] *)

(* [comment removed for export] *)
End LEVEL.

End ACeilS1.
End ASlot_M4.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W13.
Module ASlot_M5P.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_big.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M4P.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_wr8_other st q v o : o <> snd q ->
  (r_cells (get_shadow (wr8 q v st) (fst q))) !! o = (r_cells (get_shadow st (fst q))) !! o.
Proof. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

(* [comment removed for export] *)

Lemma hav_wr8 st q v : r_hav (get_shadow (wr8 q v st) (fst q)) = r_hav (get_shadow st (fst q))
  /\ r_havp (get_shadow (wr8 q v st) (fst q)) = r_havp (get_shadow st (fst q)).
Proof. rewrite get_shadow_wr8_same. split; reflexivity. Qed.

Lemma cells_wr8_other' st rid off v o : o <> off ->
  (r_cells (get_shadow (wr8 (rid, off) v st) rid)) !! o = (r_cells (get_shadow st rid)) !! o.
Proof. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.

Lemma hav_wr8_any st q v rid : r_hav (get_shadow (wr8 q v st) rid) = r_hav (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma havp_wr8_any st q v rid : r_havp (get_shadow (wr8 q v st) rid) = r_havp (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma shadow_put_meta st m r rid : get_shadow (put_meta m r st) rid = get_shadow st rid.
Proof. reflexivity. Qed.

Lemma cell_read_wr8_other' st rid off v o : o <> off ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.

Lemma cell_read_wr8_same' st rid off v : ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known v.
Proof. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.

Lemma cell_read_wr8_same_land st rid off v : ticks_ok st ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known (Z.land v 255).
Proof.
  intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
  - apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.

Lemma ticks_ok_same2 st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.

Section ZH.
Variables (p : aptr) (s : Z).

Lemma zh_proj : forall k i st,
  let st' := zero_hdrs p s i k st in
  s_regions st' = s_regions st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
  /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
  /\ s_ctx st' = s_ctx st /\ s_slots st' = s_slots st /\ s_metas st' = s_metas st.
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [repeat split; reflexivity|].
  cps_destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. repeat split; reflexivity.
Qed.

Lemma zh_shadow_other q : q <> fst p -> forall k i st, get_shadow (zero_hdrs p s i k st) q = get_shadow st q.
Proof.
  intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.

Lemma zh_hav : forall k i st,
  r_hav (get_shadow (zero_hdrs p s i k st) (fst p)) = r_hav (get_shadow st (fst p))
  /\ r_havp (get_shadow (zero_hdrs p s i k st) (fst p)) = r_havp (get_shadow st (fst p)).
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
  pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.

Lemma zh_cells_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  (r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! o = (r_cells (get_shadow st (fst p))) !! o.
Proof.
  induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH by (intros j Hj; apply Ho; lia).
  pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)

Lemma zh_cell_read_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof.
  intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
  destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma zh_cell_read_at : 0 < s -> forall k i st j, ticks_ok st -> i <= j < i + Z.of_nat k ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) (snd p + UNIT + j * s - 4) = Known 0.
Proof.
  intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cell_read_other by (intros j' Hj'; nia).
    pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
  - apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.

(* [comment removed for export] *)
Lemma existsb_filter_gt12 (l : list (Z * N)) (f : Z * N -> bool) :
  (forall ch, f ch = true -> 12 < fst ch) ->
  existsb f (filter (fun ch : Z * N => Is_true (12 <? fst ch)) l) = existsb f l.
Proof.
  intros Hf. induction l as [|ch l IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
  destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.

Lemma stale_hav_add_ge hl bb T t : 12 <= bb -> stale (hav_add 12 T hl) bb t = stale hl bb t.
Proof.
  intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
  replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
  apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.

Lemma cell_read_hdr_havoc_other st b o :
  snd b mod 16 = 0 -> ~ (snd b <= o < snd b + 12) ->
  cell_read (get_shadow (hdr_havoc b st) (fst b)) o = cell_read (get_shadow st (fst b)) o.
Proof.
  intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id].
    assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
    fold (get_shadow st (fst b)).
    destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma hav_hdr_havoc_other st b u : u <> snd b / 16 ->
  (r_hav (get_shadow (hdr_havoc b st) (fst b))) !! u = (r_hav (get_shadow st (fst b))) !! u.
Proof.
  intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cells_hdr_havoc st b : r_cells (get_shadow (hdr_havoc b st) (fst b)) = r_cells (get_shadow st (fst b))
  /\ r_havp (get_shadow (hdr_havoc b st) (fst b)) = r_havp (get_shadow st (fst b)).
Proof.
  unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section NEST.
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.

Definition nt_stW : mstate :=
  wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192)
      (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.

Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : forall o v t, X <= o < X + strideg - 4 ->
  (r_cells (get_shadow st3 (fst b))) !! o = Some (v, t) -> (t < s_tick st3)%N.

(* [comment removed for export] *)

Lemma szc_range : 1 <= szc <= 8191.
Proof. unfold szc. apply size_class_range. exact SC. Qed.

Lemma nest_model_eq :
  upd_meta mm (m_set_maplen 0) (nest_layout st3 g idx jn (UNIT * size_class sc) cnt) = nt_stT.
Proof.
  unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
  rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
  unfold upd_meta. rewrite rec_zero_hdrs.
  change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
  rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
  unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ntW_proj :
  s_regions nt_stW = s_regions st3 /\ s_groups nt_stW = s_groups st3 /\ s_areas nt_stW = s_areas st3
  /\ s_tick nt_stW = s_tick st3 /\ s_next_rid nt_stW = s_next_rid st3 /\ s_reserved nt_stW = s_reserved st3
  /\ s_ctx nt_stW = s_ctx st3 /\ s_slots nt_stW = s_slots st3.
Proof. repeat split; reflexivity. Qed.

Lemma ntT_proj :
  s_regions nt_stT = s_regions st3 /\ s_groups nt_stT = s_groups st3 /\ s_areas nt_stT = s_areas st3
  /\ s_tick nt_stT = s_tick st3 /\ s_next_rid nt_stT = s_next_rid st3 /\ s_reserved nt_stT = s_reserved st3
  /\ s_ctx nt_stT = s_ctx st3 /\ s_slots nt_stT = s_slots st3.
Proof.
  unfold nt_stT. cps_destruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.

Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
  unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
  change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
    with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
  destruct (decide (q = mm)) as [->|NE].
  - rewrite get_meta_rec_put_same, G0. reflexivity.
  - rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.

Lemma ntT_active c : active nt_stT c = active st3 c.
Proof. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_usage i : usage nt_stT i = usage st3 i.
Proof. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_ctx : ctx nt_stT = ctx st3.
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.

Lemma ntT_conc q : conc nt_stT q = conc st3 q.
Proof. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.

Lemma ntT_shadow_other q : q <> fst b -> get_shadow nt_stT q = get_shadow st3 q.
Proof.
  intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
  rewrite get_shadow_wr8_other by exact NE.
  change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
  unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.

Lemma ntW_hav :
  r_hav (get_shadow nt_stW (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stW (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stW, enf0_st, wr16.
  split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.

Lemma ntT_hav :
  r_hav (get_shadow nt_stT (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stT (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
  rewrite A, B. exact ntW_hav.
Qed.

(* [comment removed for export] *)
Definition nt_written (o : Z) : Prop :=
  o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).

Lemma ntW_cells_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  (r_cells (get_shadow nt_stW (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite !cells_wr8_other' by lia. reflexivity.
Qed.

Lemma ntW_cell_read_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  cell_read (get_shadow nt_stW (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma ntT_cells_other o : ~ nt_written o ->
  (r_cells (get_shadow nt_stT (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
  rewrite zh_cells_other.
  2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
  unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.

Lemma ntT_cell_read_other o : ~ nt_written o ->
  cell_read (get_shadow nt_stT (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.

Lemma ntW_ticks_ok : ticks_ok nt_stW.
Proof.
  unfold nt_stW. apply ticks_ok_wr8.
  assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
  eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.

Lemma ntT_cell_read_zero j : 0 <= j <= cnt ->
  cell_read (get_shadow nt_stT (fst b)) (X + 12 + j * (16 * szc)) = Known 0.
Proof.
  intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
  apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.

Lemma ntT_cell_read_hdr k : 1 <= k <= 3 -> exists v, cell_read (get_shadow nt_stT (fst b)) (X - k) = Known v.
Proof.
  intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
  unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
  assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
                          (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
  assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
  assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
  assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
  destruct (Z.eq_dec k 3) as [->|N3].
  { eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
  rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite 2 cell_read_wr8_other' by lia.
  destruct (Z.eq_dec k 1) as [->|N1].
  { eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
  assert (k = 2) by lia. subst k.
  rewrite cell_read_wr8_other' by lia.
  eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slot_geom :
  m_mem (get_meta_rec st3 g) = Some b /\ (s_regions st3) !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ 0 <= snd b /\ snd b mod 16 = 0 /\ 0 <= idx /\ 16 <= strideg /\ strideg mod 16 = 0
  /\ X + strideg <= round_up_pg (r_len r) /\ 0 <= strideg * idx
  /\ (forall b' gh, (s_groups st3) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= X - 4 \/ X + strideg - 4 <= snd b').
Proof.
  destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
  fold strideg in Sspan, Ss16, Ssmod, Snogrp.
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  repeat (split; [first [assumption | unfold X; lia] |]).
  intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.

Lemma X_mod16 : X mod 16 = 0.
Proof.
  cps_destruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _).
  unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
  rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.

Lemma nt_tail_hyps :
  meta_slot nt_stT mm
  /\ get_meta_rec nt_stT mm = mkMeta None None None 0 0 0 0 0 0
  /\ (s_regions nt_stT) !! (fst p) = Some r
  /\ 0 <= snd p /\ snd p mod 16 = 0 /\ snd p + 16 <= round_up_pg (r_len r)
  /\ (s_groups nt_stT) !! p = None
  /\ (forall b' gh, (s_groups nt_stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b')
  /\ (forall o v t, snd p <= o < snd p + 12 -> (r_cells (get_shadow nt_stT (fst p))) !! o = Some (v, t) -> (t < s_tick nt_stT)%N)
  /\ s_tick nt_stT = s_tick st3.
Proof.
  cps_destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  cps_destruct ntT_proj as (PR & PG & PA & PT & _).
  split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
  split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
  split. { rewrite PR. exact Sreg. }
  split. { unfold p, X. cbn. lia. }
  split. { exact X_mod16. }
  split. { unfold p. cbn [snd]. lia. }
  split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
           destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
  split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
  split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
           rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
           eapply FRESH3; [| exact Hc]. lia. }
  exact PT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.

Lemma ntF_rec_mt : get_meta_rec stF mm = sm_rec sc cnt (cnt - 1) 0 mm p.
Proof.
  apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.

Lemma ntF_stride : get_stride (get_meta_rec stF mm) = 16 * szc.
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.

Lemma ntF_shadow_eq : s_shadow stF = s_shadow (hdr_havoc p nt_stT).
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.

Lemma ntF_cell_read_other o : ~ (X <= o < X + 12) ->
  cell_read (get_shadow stF (fst b)) o = cell_read (get_shadow nt_stT (fst b)) o.
Proof.
  intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.

Lemma ntF_cells o : (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow nt_stT (fst b))) !! o.
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.

Lemma ntF_havp : r_havp (get_shadow stF (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.

Lemma ntF_hav u : u <> X / 16 -> (r_hav (get_shadow stF (fst b))) !! u = (r_hav (get_shadow st3 (fst b))) !! u.
Proof.
  intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nt_slot_ok (req : Z) : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
  intros RQ FIT. pose proof szc_range as SZR.
  cps_destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG).
  cps_destruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
  pose proof ntF_stride as STF.
  pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  cps_destruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _). fold stF in PF1, PF2, PF3, PF4.
  cps_destruct ntT_proj as (PR & PG & PA & PT & _).
  constructor; rewrite ?STF.
  - rewrite ntF_rec_mt. reflexivity.
  - rewrite PF1, PR. exact Sreg.
  - exact Skind.
  - exact TP0.
  - exact TP16.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
  - lia.
  - rewrite Z.mul_comm. apply Z_mod_mult.
  - lia.
  - exact RQ.
  - exact FIT.
  - intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
    + left. unfold p. cbn [snd]. lia.
    + rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf); [left; lia| right].
      assert (E__ : 16 * szc <= 16 * szc * cnt) by (clear - CNT SZR; nia).   (* [comment removed for export] *)
      lia.
  - unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
    rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
  - unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
    apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
  - apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
  - rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

(* [comment removed for export] *)
Lemma ntF_span_cells o : X + 16 <= o < X + 16 + 16 * szc - 4 ->
  (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
  intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.

Lemma ntF_span_hav o : X + 16 <= o -> (r_hav (get_shadow stF (fst b))) !! (o / 16) = (r_hav (get_shadow st3 (fst b))) !! (o / 16).
Proof. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma ntF_rdv13 o :
  (r_cells (get_shadow st3 (fst b))) !! (X + 13) = None ->
  (r_hav (get_shadow st3 (fst b))) !! ((X + 13) / 16) = None ->
  (r_havp (get_shadow st3 (fst b))) !! ((X + 13) / 4096) = None ->
  rdv pans_mem o stF (fst b, X + 13) = 0.
Proof.
  intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
  rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
  unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ntF_unknown off h : 0 <= off ->
  cell_read (get_shadow stF (fst b)) off = Unknown h ->
  grp_hdr_cov stF (fst b) off
  \/ (cell_read (get_shadow st3 (fst b)) off = Unknown h /\ ~ (X - 3 <= off < X) /\ ~ (exists j, 0 <= j <= cnt /\ off = X + 12 + j * (16 * szc))).
Proof.
  intros Ho Hc. pose proof szc_range as SZR.
  destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
  2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
  all: right; rewrite ntF_cell_read_other in Hc by lia.
  - destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
      split; [exact Hc|]. split; [lia|]. cps_intros (j & Hj & E). nia.
    + exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
  - destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
      [destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
      split; [exact Hc|]. split; [lia|]. cps_intros (j & Hj & E).
      assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
    + exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
      pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
      pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
      replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
      split; [exact Hc|]. split; [lia|]. cps_intros (j & Hj & E).
      apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.

Lemma ntF_shadow_other q : q <> fst b -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.

End ACeilS1.
End ASlot_M5P.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W10 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W12 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W18 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M4P OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M5P. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS MallocKit_A3 ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W9 ASlot_W10 ASlot_W12 ASlot_I ASlot_M0. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp MallocKit_A2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_AB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv4. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma slot_ok_N st g b r idx n N :
  slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arith_prog_dec a c s n : 0 < s ->
  (exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma meta_slot_mono stA stB g :
  (forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
  (intros HA; cps_intros (ar & arr & kk & Ha & Hk & E)). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  exists ar, arr', kk. auto.
Qed.

(* [comment removed for export] *)
Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).

Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
  /\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Hypothesis IHf : alloc_slot_stmt2 f.




(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


End LEVEL.

End ACeilS1.
